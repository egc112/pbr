'use strict';
// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright 2020-2026 MOSSDeF, Stan Grishin (stangri@melmac.ca).
//
// Main ucode module for pbr (Policy Based Routing).
// All business logic lives here; the init script is a thin procd wrapper.

import { readfile, writefile, popen, stat, unlink, open, glob, mkdir, mkstemp, access, dirname, lsdir } from 'fs';
import { cursor } from 'uci';
import { connect } from 'ubus';

// rpcd backward-compat wrappers are now methods on pbr

// ── Constants ───────────────────────────────────────────────────────

const pkg = {
	name: 'pbr',
	version: 'dev-test',
	compat: '29',
	config_file: '/etc/config/pbr',
	debug_file: '/var/run/pbr.debug',
	lock_file: '/var/run/pbr.lock',
	dnsmasq_file: '/var/run/pbr.dnsmasq',
	mwan4_nft_prefix: 'mwan4',
	mwan4_nft_iface_file: '/usr/share/nftables.d/ruleset-post/12-mwan4-interfaces.nft',
	nft_temp_file: '/var/run/pbr.nft',
	nft_netifd_file: '/usr/share/nftables.d/ruleset-post/20-pbr-netifd.nft',
	nft_main_file: '/usr/share/nftables.d/ruleset-post/30-pbr.nft',
	nft_table: 'fw4',
	nft_prefix: 'pbr',
	nft_ipv4_flag: 'ip',
	nft_ipv6_flag: 'ip6',
	chains_list: 'forward output prerouting',
	ip_full: '/usr/libexec/ip-full',
	ip_table_prefix: 'pbr',
	rt_tables_file: '/etc/iproute2/rt_tables',
	ss_config_file: '/etc/shadowsocks',
	tor_config_file: '/etc/tor/torrc',
	xray_iface_prefix: 'xray_',
	url: function(fragment) {
		return sprintf("https://docs.openwrt.melmac.ca/%s/%s/%s", this.name, split(this.version, '-')[0], fragment || '');
	},
};
pkg.service_name = pkg.name + ' ' + pkg.version;

// ── Symbols ─────────────────────────────────────────────────────────

const sym = {
	dot:  ['.', '[w]'],
	ok:   ['\033[0;32m✓\033[0m', '\033[0;32m[✓]\033[0m'],
	okb:  ['\033[1;34m✓\033[0m', '\033[1;34m[✓]\033[0m'],
	fail: ['\033[0;31m✗\033[0m', '\033[0;31m[✗]\033[0m'],
	ERR:  '\033[0;31mERROR:\033[0m',
	WARN: '\033[0;33mWARNING:\033[0m',
};

// ── Environment ─────────────────────────────────────────────────────
// Immutable system capabilities, detected once per run.
// Methods (is_present, detect, load_network, get_downloader,
// is_running_nft_file) are assigned after utility functions are defined.

let env = {
	// Platform capabilities (set by env.detect())
	nft_installed: false,
	dnsmasq_installed: false,
	unbound_installed: false,
	adguardhome_installed: false,
	dnsmasq_features: '',
	dnsmasq_nftset_supported: false,
	resolver_set_supported: false,
	agh_config_file: '/etc/AdGuardHome/AdGuardHome.yaml',

	// Network (set by env.load_network())
	firewall_wan_zone: '',
	ifaces_supported: '',
	webui_interfaces: [],
	uplink_gw: '',
	uplink_gw4: '',
	uplink_gw6: '',

	// Downloader (set lazily by env.get_downloader())
	_dl_cache: null,

	// Tor (detected from running process)
	tor_dns_port: '',
	tor_traffic_port: '',

	// External marks and chains (populated by env.detect())
	netifd_mark: {},
	mwan4_mark: {},
	mwan4_interface_chain: {},
	mwan4_strategy_chain: {},

	// Guard flags
	_config_loaded: false,
	_loaded: false,
	_detected: false,
	_network_output_done: false,
};

// ── Mutable Runtime State ───────────────────────────────────────────

// Config values loaded by env.load_config()
let cfg = {};

// Unified pbr object — merges runtime state, nft rule accumulator, and interface/error tracking.
let pbr = {
	// Runtime state
	script_name: pkg.name,
	is_tty: false,
	output_queue: '',
	iface_priority: '',
	ifaces_triggers: '',
	service_start_trigger: '',
	process_dns_policy_error: false,
	process_policy_error: false,
	process_policy_warning: false,
	pbr_nft_prev_param4: '',
	pbr_nft_prev_param6: '',
	nft_rule_params: '',
	nft_set_params: '',
	dnsmasq_ubus: null,
	nft_fw4_dump: '',
	resolver_working_flag: false,
	resolver_stored_hash: '',
	_mark_chains_created: null,

	// NFT rule accumulator
	nft_lines: [],

	// Per-interface data, error/warning tracking
	errors: [],
	warnings: [],
	// Domain sub-objects (methods assigned later; interface also holds per-iface data)
	interface: {},
	policy: {},
	dns_policy: {},
	user_file: {},
	nft_file: {},
};

pbr.reset = function() {
	pbr.errors = [];
	pbr.warnings = [];
	for (let k in keys(pbr.interface))
		if (type(pbr.interface[k]) != 'function')
			delete pbr.interface[k];
};
pbr.get_mark = function(iface) {
	let iface_key = replace(iface, '-', '_');
	return pbr.interface[iface_key]?.mark;
};
pbr.set_interface = function(iface, data) {
	let iface_key = replace(iface, '-', '_');
	pbr.interface[iface_key] = data;
};
pbr.get_interface = function(iface) {
	let iface_key = replace(iface, '-', '_');
	return pbr.interface[iface_key];
};

// ── UCI Cursor ──────────────────────────────────────────────────────

let _cursor = null;
let _cursor_loaded = {};

function uci_ctx(config, reload) {
	if (!_cursor) _cursor = cursor();
	if (!_cursor_loaded[config] || reload) {
		_cursor.load(config);
		_cursor_loaded[config] = true;
	}
	return _cursor;
}

// ── Shell / System Helpers ──────────────────────────────────────────

function shell_quote(s) {
	return "'" + replace('' + s, "'", "'\\''") + "'";
}

function shell(cmd) {
	let p = popen(cmd, 'r');
	if (!p) return '';
	let data = p.read('all') || '';
	p.close();
	return trim(data);
}

function sys(cmd) {
	return system(cmd + ' >/dev/null 2>&1');
}

function mkdir_p(path) {
	if (!path || stat(path)?.type == 'directory') return true;
	let parent = dirname(path);
	if (parent && parent != path) mkdir_p(parent);
	return mkdir(path) != null;
}

env.is_present = function(cmd) {
	if (index(cmd, '/') >= 0)
		return access(cmd, 'x') == true;
	for (let dir in ['/usr/sbin', '/usr/bin', '/sbin', '/bin'])
		if (access(dir + '/' + cmd, 'x') == true) return true;
	return false;
};
let is_present = (...args) => env.is_present(...args);

// ── ip command wrapper ──────────────────────────────────────────────
// Wraps ip-full to emulate `ip rule replace` on builds where it's unavailable.

function ip(...args) {
	if (length(args) < 1) return 1;
	let fam = args[0];
	if (fam == '-4' || fam == '-6') {
		let rest = slice(args, 1);
		if (length(rest) >= 2 && rest[0] == 'rule' && rest[1] == 'replace') {
			let rule_args = slice(rest, 2);
			let prio = null;
			let newargs = [];
			for (let i = 0; i < length(rule_args); i++) {
				if (rule_args[i] == 'priority' || rule_args[i] == 'pref') {
					i++;
					if (i < length(rule_args))
						prio = rule_args[i];
					continue;
				}
				push(newargs, rule_args[i]);
			}
			if (prio != null) {
				system(pkg.ip_full + ' ' + fam + ' rule del priority ' + prio + ' 2>/dev/null');
				return system(pkg.ip_full + ' ' + fam + ' rule add ' + join(' ', newargs) + ' pref ' + prio);
			}
			return system(pkg.ip_full + ' ' + fam + ' rule add ' + join(' ', newargs));
		}
		return system(pkg.ip_full + ' ' + fam + ' ' + join(' ', rest));
	}
	return system(pkg.ip_full + ' ' + join(' ', args));
}

// ── ubus helpers ────────────────────────────────────────────────────

function ubus_call(path, method, args) {
	let u = connect();
	if (!u) return null;
	let result = u.call(path, method, args);
	u.disconnect();
	return result;
}

function network_get_device(iface) {
	let iface_status = ubus_call('network.interface.' + iface, 'status');
	return iface_status?.l3_device || iface_status?.device || null;
}

function network_get_physdev(iface) {
	let iface_status = ubus_call('network.interface.' + iface, 'status');
	return iface_status?.device || null;
}

function network_get_gateway(iface) {
	let iface_status = ubus_call('network.interface.' + iface, 'status');
	if (!iface_status) return null;
	let routes = iface_status?.route;
	if (type(routes) == 'array') {
		for (let r in routes) {
			if (r?.target == '0.0.0.0' && r?.mask == 0)
				return r?.nexthop;
		}
	}
	return null;
}

function network_get_gateway6(iface) {
	let iface_status = ubus_call('network.interface.' + iface, 'status');
	if (!iface_status) return null;
	let routes = iface_status?.route;
	if (type(routes) == 'array') {
		for (let r in routes) {
			if (r?.target == '::' && r?.mask == 0)
				return r?.nexthop;
		}
	}
	return null;
}

function network_get_protocol(iface) {
	let ctx = uci_ctx('network');
	return ctx.get('network', iface, 'proto') || null;
}

function network_flush_cache() {
	// Force reload of network config from UCI
	_cursor_loaded['network'] = false;
}

// ── Output Management ───────────────────────────────────────────────

let _write = function(level, ...args) {
	if (!cfg.verbosity)
		cfg.verbosity = int(uci_ctx(pkg.name).get(pkg.name, 'config', 'verbosity') || '2');
	let msg = join('', args);
	if (level != null && (cfg.verbosity & level) == 0) return;

	// Print to stderr (terminal)
	if (pbr.is_tty)
		warn(replace(msg, /\\n/g, '\n'));

	// Queue for logger: flush on newline
	if (index(msg, '\\n') >= 0 || index(msg, '\n') >= 0) {
		msg = pbr.output_queue + msg;
		pbr.output_queue = '';
		let clean = replace(msg, /\x1b\[[0-9;]*m/g, '');
		clean = replace(clean, /\\n/g, '\n');
		clean = trim(clean);
		if (clean != '')
			system('/usr/bin/logger -t ' + shell_quote(pbr.script_name) + ' ' + shell_quote(clean));
	} else {
		pbr.output_queue += msg;
	}
};

function logger_debug(msg) {
	if (cfg.debug_performance)
		system('/usr/bin/logger -t ' + shell_quote(pbr.script_name) + ' ' + shell_quote(msg));
}

let output = {
	_write:   _write,
	info:     function(...args) { _write(1, ...args); },
	verbose:  function(...args) { _write(2, ...args); },
	debug:    function(...args) { _write(3, ...args); },
	print:    function(...args) { _write(null, ...args); },
	// Dual-level status (writes both levels) — use after output.print()
	ok:       function() { _write(1, sym.ok[0]); _write(2, sym.ok[1] + '\\n'); },
	okn:      function() { _write(1, sym.ok[0] + '\\n'); _write(2, sym.ok[1] + '\\n'); },
	okb:      function() { _write(1, sym.okb[0]); _write(2, sym.okb[1] + '\\n'); },
	okbn:     function() { _write(1, sym.okb[0] + '\\n'); _write(2, sym.okb[1] + '\\n'); },
	fail:     function() { _write(1, sym.fail[0]); _write(2, sym.fail[1] + '\\n'); },
	failn:    function() { _write(1, sym.fail[0] + '\\n'); _write(2, sym.fail[1] + '\\n'); },
	dot:      function() { _write(1, sym.dot[0]); _write(2, sym.dot[1]); },
	newline1: function() { _write(1, '\\n'); },
	// Info-level status (level 1 only) — use after output.info()
	info_ok:      function() { _write(1, sym.ok[0]); },
	info_okn:     function() { _write(1, sym.ok[0] + '\\n'); },
	info_okb:     function() { _write(1, sym.okb[0]); },
	info_okbn:    function() { _write(1, sym.okb[0] + '\\n'); },
	info_fail:    function() { _write(1, sym.fail[0]); },
	info_failn:   function() { _write(1, sym.fail[0] + '\\n'); },
	info_newline: function() { _write(1, '\\n'); },
	// Verbose-level status (level 2 only) — use after output.verbose()
	verbose_ok:      function() { _write(2, sym.ok[1] + '\\n'); },
	verbose_okn:     function() { _write(2, sym.ok[1] + '\\n'); },
	verbose_okb:     function() { _write(2, sym.okb[1] + '\\n'); },
	verbose_okbn:    function() { _write(2, sym.okb[1] + '\\n'); },
	verbose_fail:    function() { _write(2, sym.fail[1] + '\\n'); },
	verbose_failn:   function() { _write(2, sym.fail[1] + '\\n'); },
	verbose_newline: function() { _write(2, '\\n'); },
	// Debug-level status (level 3 only) — use after output.debug()
	debug_okn:     function() { _write(3, sym.ok[1] + '\\n'); },
	debug_failn:   function() { _write(3, sym.fail[1] + '\\n'); },
	error:    function(msg) { _write(null, sym.ERR + ' ' + msg + '!\\n'); },
	warning:  function(msg) { _write(null, sym.WARN + ' ' + msg + '.\\n'); },
	quiet_mode: function(mode) {
		if (mode == 'on') cfg.verbosity = 0;
		else cfg.verbosity = int(uci_ctx(pkg.name).get(pkg.name, 'config', 'verbosity') || '2');
	},
};

// ── String / Validation Utility Functions ───────────────────────────

function str_contains(haystack, needle) { return haystack != null && needle != null && index('' + haystack, '' + needle) >= 0; }
function str_contains_word(haystack, needle) { return !!(haystack && needle) && index(split(trim('' + haystack), /\s+/), '' + needle) >= 0; }
function str_first_word(s) { let m = s ? match(trim('' + s), /^(\S+)/) : null; return m ? m[1] : ''; }

// ── Validation Functions ────────────────────────────────────────────

function is_ipv4(s) {
	if (!s) return false;
	return !!match('' + s, /^((25[0-5]|2[0-4][0-9]|1?[0-9]{1,2})\.){3}(25[0-5]|2[0-4][0-9]|1?[0-9]{1,2})(\/([0-2]?[0-9]|3[0-2]))?$/);
}
function is_mac_address(s) {
	if (!s) return false;
	return !!match('' + s, /^([0-9A-Fa-f]{2}:){5}([0-9A-Fa-f]{2})$/);
}
function is_ipv6(s) {
	if (!s) return false;
	s = '' + s;
	if (is_mac_address(s)) return false;
	return index(s, ':') >= 0;
}
function is_domain(s) {
	if (!s) return false;
	s = '' + s;
	if (is_ipv4(s)) return false;
	if (match(s, /^([0-9A-Fa-f]{2}-){5}([0-9A-Fa-f]{2})$/)) return false;
	return !!match(s, /^[a-zA-Z0-9]$/) || !!match(s, /^[a-zA-Z0-9][a-zA-Z0-9_-]{0,61}[a-zA-Z0-9]$/) ||
		!!match(s, /^([a-zA-Z0-9]([a-zA-Z0-9_-]{0,61}[a-zA-Z0-9])?\.)+[a-zA-Z]{2,}$/);
}
function is_phys_dev(s) {
	if (!s) return false;
	s = '' + s;
	if (substr(s, 0, 1) != '@') return false;
	let dev = substr(s, 1);
	return stat('/sys/class/net/' + dev)?.type == 'link';
}
function is_url_file(s) { return !!s && substr('' + s, 0, 7) == 'file://'; }
function is_url_https(s) { return !!s && substr('' + s, 0, 8) == 'https://'; }
function is_url(s) { if (!s) return false; s = '' + s; return is_url_file(s) || substr(s, 0, 6) == 'ftp://' || substr(s, 0, 7) == 'http://' || is_url_https(s); }
function is_dslite(iface) { let _p = network_get_protocol(iface); return _p != null && substr(_p, 0, 6) == 'dslite'; }
function is_l2tp(iface) { let _p = network_get_protocol(iface); return _p != null && substr(_p, 0, 4) == 'l2tp'; }
function is_oc(iface) { let _p = network_get_protocol(iface); return _p != null && substr(_p, 0, 11) == 'openconnect'; }
function is_ovpn(iface) {
	let d = uci_ctx('network').get('network', iface, 'device');
	if (!d) return false;
	if (substr(d, 0, 3) == 'tun' || substr(d, 0, 3) == 'tap') return true;
	return stat('/sys/devices/virtual/net/' + d + '/tun_flags')?.type != null;
}
function is_pptp(iface) { let _p = network_get_protocol(iface); return _p != null && substr(_p, 0, 4) == 'pptp'; }
function is_softether(iface) { let d = network_get_device(iface); return d != null && substr(d, 0, 4) == 'vpn_'; }
function is_netbird(iface) { let d = network_get_device(iface); return d != null && substr(d, 0, 2) == 'wt'; }
function is_tailscale(iface) { let d = network_get_device(iface); return d != null && substr(d, 0, 9) == 'tailscale'; }
function is_wg(iface) { let _p = network_get_protocol(iface); return !uci_ctx('network').get('network', iface, 'listen_port') && _p != null && substr(_p, 0, 9) == 'wireguard'; }
function is_wg_server(iface) { let _p = network_get_protocol(iface); return !!uci_ctx('network').get('network', iface, 'listen_port') && _p != null && substr(_p, 0, 9) == 'wireguard'; }
function is_tor(iface) { return lc(iface) == 'tor'; }
function get_xray_traffic_port(iface) {
	if (!iface) return null;
	let i = replace('' + iface, pkg.xray_iface_prefix, '');
	if (i == '' + iface) return null;
	return i;
}
function is_xray(iface) { return get_xray_traffic_port(iface) != null; }
function is_tunnel(iface) {
	return is_dslite(iface) || is_l2tp(iface) || is_oc(iface) || is_ovpn(iface) ||
		is_pptp(iface) || is_softether(iface) || is_netbird(iface) ||
		is_tailscale(iface) || is_tor(iface) || is_wg(iface);
}
function is_wan(iface) {
	if (!iface) return false;
	iface = '' + iface;
	let is6 = !!match(iface, /wan.*6$/) || !!match(iface, /.*wan6$/);
	if (is6) return !!cfg.ipv6_enabled;
	return !!match(iface, /wan/) || !!match(iface, /.*wan$/);
}
function is_uplink4(iface) { return iface == cfg.uplink_interface4; }
function is_uplink6(iface) { return !!cfg.ipv6_enabled && iface == cfg.uplink_interface6; }
function is_uplink(iface) { return is_uplink4(iface) || is_uplink6(iface); }
function is_split_uplink() { return !!cfg.ipv6_enabled && cfg.uplink_interface4 != cfg.uplink_interface6; }
function is_default_dev(dev) {
	let out = shell(pkg.ip_full + ' -4 route show default 2>/dev/null');
	let m = match(out, /dev\s+(\S+)/);
	return m ? dev == m[1] : false;
}
function is_disabled_interface(iface) { return uci_ctx('network').get('network', iface, 'disabled') == '1'; }
function is_lan(iface) {
	let d = network_get_device(iface);
	if (!d) return false;
	return str_contains(cfg.lan_device, d);
}
function is_ignored_interface(iface) { return str_contains_word(cfg.ignored_interface, iface); }
function is_tor_running() {
	if (is_ignored_interface('tor')) return false;
	let content = readfile(pkg.tor_config_file);
	if (!content || content == '') return false;
	let svc = ubus_call('service', 'list', { name: 'tor' });
	if (!svc?.tor?.instances) return false;
	for (let k in keys(svc.tor.instances)) {
		if (svc.tor.instances[k]?.running == true)
			return true;
	}
	return false;
}
function is_ignore_target(iface) { return lc(iface) == 'ignore'; }
function is_netifd_table(name) { let c = readfile('/etc/config/network') || ''; return index(c, name) >= 0 && !!match(c, regexp('ip.table.*' + name)); }
function is_netifd_interface(iface) {
	let ctx = uci_ctx('network');
	let ip4t = ctx.get('network', iface, 'ip4table');
	let ip6t = ctx.get('network', iface, 'ip6table');
	return !!(ip4t || ip6t);
}
function is_mwan4_interface(iface) {
	return !!(iface && env.mwan4_mark[iface]);
}
function is_netifd_interface_default(iface) {
	if (!is_netifd_interface(iface)) return false;
	if (cfg.netifd_interface_default == iface) return true;
	if (cfg.netifd_interface_default6 == iface) return true;
	return false;
}
function is_supported_protocol(proto) { return sys('grep -qi "^' + (proto || '-') + '" /etc/protocols') == 0; }
function is_mwan4_strategy(iface) { return iface && index(iface, 'mwan4_strategy_') == 0;
}
function is_supported_interface(iface) {
	if (!iface) return false;
	if (is_lan(iface) || is_disabled_interface(iface)) return false;
	if (str_contains_word(cfg.supported_interface, iface)) return true;
	if (!is_ignored_interface(iface) && (is_uplink(iface) || is_wan(iface) || is_tunnel(iface))) return true;
	if (is_ignore_target(iface)) return true;
	if (is_xray(iface)) return true;
	return false;
}
function is_config_enabled(section_type) {
	let result = false;
	let ctx = uci_ctx(pkg.name);
	ctx.foreach(pkg.name, section_type, function(s) {
		if ((s.enabled || '1') == '1') result = true;
	});
	return result;
}
function is_family_mismatch(a, b) {
	a = replace('' + (a || ''), '!', '');
	b = replace('' + (b || ''), '!', '');
	return (is_ipv4(a) && is_ipv6(b)) || (is_ipv6(a) && is_ipv4(b));
}
// ── Network Helper Functions ────────────────────────────────────────

pbr.get_gateway4 = function(iface, dev) {
	let gw = network_get_gateway(iface);
	if (!gw || gw == '0.0.0.0') {
		let out = shell(pkg.ip_full + ' -4 a list dev ' + shell_quote(dev) + ' 2>/dev/null');
		let m = match(out, /inet\s+([0-9.]+)/);
		gw = m ? m[1] : '';
	}
	return gw;
};

pbr.get_gateway6 = function(iface, dev) {
	if (is_uplink4(iface)) iface = cfg.uplink_interface6;
	let gw = network_get_gateway6(iface);
	if (!gw || gw == '::/0' || gw == '::0/0' || gw == '::') {
		let out = shell(pkg.ip_full + ' -6 a list dev ' + shell_quote(dev) + ' 2>/dev/null');
		let m = match(out, /inet6\s+(\S+)\s+scope global/);
		gw = m ? m[1] : '';
	}
	return gw;
};

function filter_options(opt, values) {
	if (!values) return '';
	let parts = split(trim('' + values), /\s+/);
	let ret = [];
	for (let v in parts) {
		if (str_contains(opt, '_negative')) {
			if (substr('' + v, 0, 1) != '!') continue;
			opt = replace(opt, '_negative', '');
		}
		let check_val = replace(v, '!', '');
		let ok = false;
		switch (opt) {
		case 'phys_dev': ok = is_phys_dev(check_val); break;
		case 'mac_address': ok = is_mac_address(check_val); break;
		case 'domain': ok = is_domain(check_val); break;
		case 'ipv4': ok = is_ipv4(check_val); break;
		case 'ipv6': ok = is_ipv6(check_val); break;
		}
		if (ok) push(ret, v);
	}
	return join(' ', ret);
}

function inline_set(value) {
	if (!value) return '';
	let parts = split(trim('' + value), /\s+/);
	let result = [];
	for (let i in parts) {
		let cleaned = replace(i, /^[@!]/, '');
		push(result, cleaned);
	}
	return join(', ', result);
}

// mwan4 detection and integration functions

function is_mwan4_installed() {
	return access('/etc/init.d/mwan4', 'x') == true && stat('/etc/config/mwan4')?.type != null;
}

function is_mwan4_running() { // ucode-lsp disable
	if (!is_mwan4_installed()) return false;
	return sys('/etc/init.d/mwan4 running') == 0;
}

// ── Misc helpers ────────────────────────────────────────────────────

function get_rt_tables_id(iface) {
	let content = readfile(pkg.rt_tables_file) || '';
	let esc_iface = replace(iface, /([.+*?^${}()|[\]\\])/g, '\\$1');
	let pattern = regexp('(^|\\n)(\\d+)\\s+' + pkg.ip_table_prefix + '_' + esc_iface + '(\\n|$)');
	let m = match(content, pattern);
	return m ? m[2] : '';
}

function get_rt_tables_next_id() {
	let out = shell("sort -r -n " + shell_quote(pkg.rt_tables_file) + " | grep -o -E -m 1 '^[0-9]+'");
	return '' + ((int(out) || 0) + 1);
}

function get_rt_tables_non_pbr_next_id() {
	let out = shell("grep -v " + shell_quote(pkg.ip_table_prefix + '_') + " " + shell_quote(pkg.rt_tables_file) + " | sort -r -n | grep -o -E -m 1 '^[0-9]+'");
	return '' + ((int(out) || 0) + 1);
}

function get_mark_nft_chains() {
	let out = shell('nft list table inet ' + pkg.nft_table + ' 2>/dev/null');
	let prefix = pkg.nft_prefix + '_mark_';
	let results = [];
	for (let line in split(out, '\n')) {
		let m = match(line, /chain\s+(\S+)/);
		if (m && index(m[1], prefix) == 0) push(results, m[1]);
	}
	return join(' ', results);
}

// Returns a set of marking chain names owned by netifd/mwan4 (not created by pbr).
function get_external_mark_chains() {
	let external = {};
	let prefix = pkg.nft_prefix + '_mark_';
	let chain_re = regexp('chain\\s+(' + pkg.nft_prefix + '_mark_\\S+)');
	// Chains declared in the netifd nft file
	let netifd_nft = readfile(pkg.nft_netifd_file) || '';
	for (let line in split(netifd_nft, '\n')) {
		let m = match(line, chain_re);
		if (m) external[m[1]] = true;
	}
	// Chains declared in the mwan4 nft file
	let mwan4_nft = readfile(pkg.mwan4_nft_iface_file) || '';
	for (let line in split(mwan4_nft, '\n')) {
		let m = match(line, chain_re);
		if (m) external[m[1]] = true;
	}
	return external;
}

function is_service_running_nft() {
	if (!env.nft_installed) return false;
	let chains = get_mark_nft_chains();
	return chains != null && chains != '';
}

function get_nft_sets() {
	let out = shell('nft list table inet ' + pkg.nft_table + ' 2>/dev/null');
	let prefix = pkg.nft_prefix + '_';
	let results = [];
	for (let line in split(out, '\n')) {
		let m = match(line, /set\s+(\S+)/);
		if (m && index(m[1], prefix) == 0) push(results, m[1]);
	}
	return join(' ', results);
}

env.is_running_nft_file = function() {
	let s = stat(pkg.nft_main_file);
	return s != null && s.type == 'file' && s.size > 0;
};

function resolveip_to_nftset(...args) {
	pbr.resolver('wait');
	let out = shell('resolveip ' + join(' ', map(args, (a) => shell_quote(a))));
	let ips = filter(split(trim(out), '\n'), (l) => length(l) > 0);
	return join(',', ips);
}

function resolveip_to_nftset4(host) {
	return resolveip_to_nftset('-4', host);
}

function resolveip_to_nftset6(host) {
	if (!cfg.ipv6_enabled) return '';
	return resolveip_to_nftset('-6', host);
}

function ipv4_leases_to_nftset(arg) {
	let content = readfile('/tmp/dhcp.leases') || '';
	if (!content) return '';
	let results = [];
	for (let line in split(content, '\n')) {
		if (index(line, arg) >= 0) {
			let parts = split(trim(line), /\s+/);
			if (length(parts) >= 3 && parts[2]) push(results, parts[2]);
		}
	}
	return join(',', results);
}

env.detect = function() {
	if (env._detected) return;
	env.nft_installed = is_present('nft');
	env.dnsmasq_installed = is_present('dnsmasq');
	env.unbound_installed = is_present('unbound');
	let agh = shell('command -v AdGuardHome');
	if (agh && is_present(agh)) {
		let content = readfile(env.agh_config_file);
		if (content && content != '') {
			env.adguardhome_installed = true;
		} else {
			let alt = dirname(agh) + '/AdGuardHome.yaml';
			content = readfile(alt);
			env.adguardhome_installed = !!(content && content != '');
		}
	}
	if (env.dnsmasq_installed) {
		if (!env.dnsmasq_features)
			env.dnsmasq_features = shell("dnsmasq --version 2>/dev/null | grep -m1 'Compile time options:' | cut -d: -f2") + ' ';
		env.dnsmasq_nftset_supported = index(env.dnsmasq_features, ' nftset ') >= 0;
	}
	if (cfg.resolver_set == 'dnsmasq.nftset') {
		env.resolver_set_supported = !!env.dnsmasq_nftset_supported;
	} else {
		env.resolver_set_supported = !cfg.resolver_set || cfg.resolver_set == 'none' || false;
	}
	// Parse external marks from netifd/mwan4 nft files
	let define_re = regexp('^define ' + pkg.nft_prefix + '_(\\S+)_mark = (\\S+)');
	let netifd_nft = readfile(pkg.nft_netifd_file) || '';
	for (let line in split(netifd_nft, '\n')) {
		let m = match(line, define_re);
		if (m) env.netifd_mark[m[1]] = m[2];
	}
	// mwan4 marks, chains, strategies — from module API if available, fallback to nft file
	if (is_mwan4_installed()) {
		let m4 = null;
		try { m4 = require('mwan4'); m4.load(); } catch(e) {}
		if (m4) {
			for (let iface in m4.get_interfaces()) {
				let mark = m4.get_iface_mark(iface);
				if (mark) env.mwan4_mark[iface] = mark;
				env.mwan4_interface_chain[iface] = m4.get_iface_chain(iface);
			}
			for (let strategy in m4.get_strategies())
				env.mwan4_strategy_chain[strategy] = m4.get_strategy_chain(strategy);
		} else {
			let mwan4_nft = readfile(pkg.mwan4_nft_iface_file) || '';
			for (let line in split(mwan4_nft, '\n')) {
				let m = match(line, define_re);
				if (m) {
					env.mwan4_mark[m[1]] = m[2];
					env.mwan4_interface_chain[m[1]] = pkg.mwan4_nft_prefix + '_iface_in_' + m[1];
				}
			}
		}
	}
	env._detected = true;
};

function ipv6_leases_to_nftset(arg) {
	let content = readfile('/tmp/hosts/odhcpd') || '';
	if (!content) return '';
	let results = [];
	for (let line in split(content, '\n')) {
		if (index(line, arg) >= 0) {
			let parts = split(trim(line), /\s+/);
			if (length(parts) >= 1 && parts[0]) push(results, parts[0]);
		}
	}
	return join(',', results);
}

function try_cmd(...args) {
	let cmd = join(' ', args);
	if (sys(cmd) != 0) {
		push(pbr.errors, { code: 'errorTryFailed', info: cmd });
		return false;
	}
	return true;
}

function try_ip(...args) {
	if (ip(...args) != 0) {
		push(pbr.errors, { code: 'errorTryFailed', info: pkg.ip_full + ' ' + join(' ', args) });
		return false;
	}
	return true;
}

// ── get_text() ──────────────────────────────────────────────────────

function get_text(code, ...args) {
	let a1 = length(args) > 0 ? args[0] : '';
	let texts = {
		errorConfigValidation:                 sprintf("Config (%s) validation failure", pkg.config_file),
		errorNoNft:                            sprintf("Resolver set support (%s) requires nftables, but nft binary cannot be found", cfg.resolver_set),
		errorResolverNotSupported:             sprintf("Resolver set (%s) is not supported on this system", cfg.resolver_set),
		errorServiceDisabled:                  sprintf("The %s service is currently disabled", pkg.name),
		errorNoUplinkGateway:                  sprintf("The %s service failed to discover uplink gateway", pkg.service_name),
		errorNoUplinkInterface:                sprintf("The %s interface not found, you need to set the 'pbr.config.uplink_interface' option", a1),
		errorNoUplinkInterfaceHint:            sprintf("Refer to %s", a1),
		errorNftsetNameTooLong:                sprintf("The nft set name '%s' is longer than allowed 255 characters", a1),
		errorUnexpectedExit:                   sprintf("Unexpected exit or service termination: '%s'", a1),
		errorPolicyNoSrcDest:                  sprintf("Policy '%s' has no source/destination parameters", a1),
		errorPolicyNoInterface:                sprintf("Policy '%s' has no assigned interface", a1),
		errorPolicyNoDns:                      sprintf("Policy '%s' has no assigned DNS", a1),
		errorPolicyProcessNoInterfaceDns:      sprintf("Interface '%s' has no assigned DNS", a1),
		errorPolicyUnknownInterface:           sprintf("Policy '%s' has an unknown interface", a1),
		errorPolicyProcessCMD:                 sprintf("'%s'", a1),
		errorFailedSetup:                      sprintf("Failed to set up '%s'", a1),
		errorFailedReload:                     sprintf("Failed to reload '%s'", a1),
		errorUserFileNotFound:                 sprintf("Custom user file '%s' not found or empty", a1),
		errorUserFileSyntax:                   sprintf("Syntax error in custom user file '%s'", a1),
		errorUserFileRunning:                  sprintf("Error running custom user file '%s'", a1),
		errorUserFileNoCurl:                   sprintf("Use of 'curl' is detected in custom user file '%s', but 'curl' isn't installed", a1),
		errorNoGateways:                       "Failed to set up any gateway",
		errorResolver:                         sprintf("Resolver '%s'", a1),
		errorPolicyProcessNoIpv6:              sprintf("Skipping IPv6 policy '%s' as IPv6 support is disabled", a1),
		errorPolicyProcessUnknownFwmark:       sprintf("Unknown packet mark for interface '%s'", a1),
		errorPolicyProcessMismatchFamily:      sprintf("Mismatched IP family between in policy '%s'", a1),
		errorPolicyProcessUnknownProtocol:     sprintf("Unknown protocol in policy '%s'", a1),
		errorPolicyProcessInsertionFailed:     sprintf("Insertion failed for both IPv4 and IPv6 for policy '%s'", a1),
		errorPolicyProcessInsertionFailedIpv4: sprintf("Insertion failed for IPv4 for policy '%s'", a1),
		errorPolicyProcessUnknownEntry:        sprintf("Unknown entry in policy '%s'", a1),
		errorInterfaceRoutingEmptyValues:      "Received empty tid/mark or interface name when setting up routing",
		errorInterfaceMarkOverflow:            sprintf("Interface mark for '%s' exceeds the fwmask value", a1),
		errorFailedToResolve:                  sprintf("Failed to resolve '%s'", a1),
		errorInvalidOVPNConfig:                sprintf("Invalid OpenVPN config for '%s' interface", a1),
		errorNftMainFileInstall:               sprintf("Failed to install fw4 nft file '%s'", a1),
		errorTryFailed:                        sprintf("Command failed: %s", a1),
		errorDownloadUrlNoHttps:               sprintf("Failed to download '%s', HTTPS is not supported", a1),
		errorDownloadUrl:                      sprintf("Failed to download '%s'", a1),
		errorNoDownloadWithSecureReload:       sprintf("Policy '%s' refers to URL which can't be downloaded in 'secure_reload' mode", a1),
		errorFileSchemaRequiresCurl:           "The file:// schema requires curl, but it's not detected on this system",
		errorIncompatibleUserFile:             sprintf("Incompatible custom user file detected '%s'", a1),
		errorUserFileUnsafeNft:                sprintf("Unsafe nft command in custom user file '%s'; only 'add', 'insert' and 'create' are allowed", a1),
		errorDefaultFw4TableMissing:           sprintf("Default fw4 table '%s' is missing", a1),
		errorDefaultFw4ChainMissing:           sprintf("Default fw4 chain '%s' is missing", a1),
		errorRequiredBinaryMissing:            sprintf("Required binary '%s' is missing", a1),
		errorInterfaceRoutingUnknownDevType:   sprintf("Unknown IPv6 Link type for device '%s'", a1),
		errorUplinkDown:                       "Uplink/WAN interface is still down, increase value of 'procd_boot_trigger_delay' option",
		errorMktempFileCreate:                 sprintf("Failed to create temporary file with mktemp mask: '%s'", a1),
		errorSummary:                          sprintf("Errors encountered, please check %s", a1),
		errorNftNetifdFileInstall:             sprintf("Netifd setup: failed to install fw4 netifd nft file '%s'", a1),
		errorNftNetifdFileDelete:              sprintf("Netifd setup: failed to remove fw4 netifd nft file '%s'", a1),
		errorNetifdMissingOption:              sprintf("Netifd setup: required option '%s' is missing", a1),
		errorNetifdInvalidGateway4:            sprintf("Netifd setup: invalid value of netifd_interface_default option '%s'", a1),
		errorNetifdInvalidGateway6:            sprintf("Netifd setup: invalid value of netifd_interface_default6 option '%s'", a1),
		warningInvalidOVPNConfig:              sprintf("Invalid OpenVPN config for '%s' interface", a1),
		warningResolverNotSupported:           sprintf("Resolver set (%s) is not supported on this system", cfg.resolver_set),
		warningPolicyProcessCMD:               sprintf("'%s'", a1),
		warningTorUnsetParams:                 sprintf("Please unset 'src_addr', 'src_port' and 'dest_port' for policy '%s'", a1),
		warningTorUnsetProto:                  sprintf("Please unset 'proto' or set 'proto' to 'all' for policy '%s'", a1),
		warningTorUnsetChainNft:               sprintf("Please unset 'chain' or set 'chain' to 'prerouting' for policy '%s'", a1),
		warningOutdatedLuciPackage:            sprintf("The WebUI application is outdated (version %s), please update it", a1),
		warningDnsmasqInstanceNoConfdir:       sprintf("Dnsmasq instance '%s' targeted in settings, but it doesn't have its own confdir", a1),
		warningDhcpLanForce:                   sprintf("Please set 'dhcp.%s.force=1' to speed up service start-up", a1),
		warningSummary:                        sprintf("Warnings encountered, please check %s", pkg.url('#warning-messages-details')),
		warningIncompatibleDHCPOption6:        sprintf("Incompatible DHCP Option 6 for interface '%s'", a1),
		warningNetifdMissingInterfaceLocal:    sprintf("Netifd setup: option netifd_interface_local is missing, assuming '%s'", a1),
		warningUplinkDown:                     "Uplink/WAN interface is still down, going back to boot mode",
		warningDynamicRoutingMode:             sprintf("Running in dynamic routing tables mode. Consider installing netifd extensions ('pbr netifd install') or mwan4 for more efficient operation. See %s", pkg.url('#routing-tables-modes')),
	};
	return texts[code] || sprintf("Unknown error/warning '%s'", code);
}

// ── Download helpers ─────────────────────────────────────────────────

env.get_downloader = function() {
	if (env._dl_cache) return env._dl_cache;
	let command, flag, https_supported;
	if (is_present('curl')) {
		command = 'curl --silent --insecure';
		flag = '-o';
	} else if (is_present('/usr/libexec/wget-ssl')) {
		command = '/usr/libexec/wget-ssl --no-check-certificate -q';
		flag = '-O';
	} else if (shell('wget --version 2>/dev/null | grep -q "+https" && echo yes') == 'yes') {
		command = 'wget --no-check-certificate -q';
		flag = '-O';
	} else {
		command = 'uclient-fetch --no-check-certificate -q';
		flag = '-O';
	}
	if (shell('curl --version 2>/dev/null | grep -q "Protocols: .*https.*" && echo yes') == 'yes' ||
		shell('wget --version 2>/dev/null | grep -q "+ssl" && echo yes') == 'yes') {
		https_supported = true;
	}
	env._dl_cache = { command, flag, https_supported };
	return env._dl_cache;
};

// ── process_url() ───────────────────────────────────────────────────

function process_url(url) {
	let _sanitize_list = function(filepath) {
		let content = readfile(filepath) || '';
		let lines = split(content, '\n');
		let seen = {}, results = [];
		for (let line in lines) {
			line = replace(line, /#.*/, '');
			line = trim(line);
			if (line && !seen[line]) {
				seen[line] = true;
				push(results, line);
			}
		}
		sort(results);
		return join(' ', results);
	};

	let dl = env.get_downloader();

	let dl_temp_file = shell('mktemp -q -t ' + shell_quote(pkg.name + '_tmp.XXXXXXXX'));
	if (!dl_temp_file || !stat(dl_temp_file)) {
		push(pbr.errors, { code: 'errorMktempFileCreate', info: pkg.name + '_tmp.XXXXXXXX' });
		return '';
	}

	let result = '';
	if (is_url_file(url) && !is_present('curl')) {
		push(pbr.errors, { code: 'errorFileSchemaRequiresCurl', info: url });
	} else if (is_url_https(url) && !dl.https_supported) {
		push(pbr.errors, { code: 'errorDownloadUrlNoHttps', info: url });
	} else if (sys(dl.command + ' ' + shell_quote(url) + ' ' + dl.flag + ' ' + shell_quote(dl_temp_file)) == 0) {
		result = _sanitize_list(dl_temp_file);
	} else {
		push(pbr.errors, { code: 'errorDownloadUrl', info: url });
	}

	unlink(dl_temp_file);
	return result;
}

// ── Config Schema & Parsing ─────────────────────────────────────────

const config_schema = { // ucode-lsp disable
	// Booleans (default false)
	enabled:                  ['bool', false],
	ipv6_enabled:             ['bool', false],
	nft_rule_counter:         ['bool', false],
	nft_set_counter:          ['bool', false],
	nft_set_flags_timeout:    ['bool', false],
	nft_user_set_counter:     ['bool', false],
	webui_show_ignore_target: ['bool', false],
	netifd_enabled:           ['bool', false],
	debug_performance:        ['bool', false],
	netifd_strict_enforcement:['bool', false],
	// Booleans (default true)
	nft_set_auto_merge:       ['bool', true],
	nft_set_flags_interval:   ['bool', true],
	strict_enforcement:       ['bool', true],
	// Strings
	config_compat:            ['string'],
	config_version:           ['string'],
	fw_mask:                  ['string', '00ff0000'],
	icmp_interface:           ['string', ''],
	nft_set_gc_interval:      ['string', ''],
	nft_set_policy:           ['string', 'performance'],
	nft_set_timeout:          ['string', ''],
	nft_user_set_policy:      ['string', ''],
	prefixlength:             ['string', '1'],
	procd_boot_trigger_delay: ['string', '5000'],
	procd_reload_delay:       ['string', '0'],
	resolver_set:             ['string', ''],
	uplink_interface:         ['string', 'wan'],
	uplink_interface6:        ['string', 'wan6'],
	uplink_ip_rules_priority: ['string', '30000'],
	uplink_mark:              ['string', '00010000'],
	netifd_interface_default: ['string', ''],
	netifd_interface_default6:['string', ''],
	netifd_interface_local:   ['string', ''],
	// Integers
	verbosity:                ['int', 2],
	// Lists (stored as space-separated strings)
	ignored_interface:        ['list', ''],
	lan_device:               ['list', 'br-lan'],
	resolver_instance:        ['list', '*'],
	supported_interface:      ['list', ''],
};

const policy_schema = { // ucode-lsp disable
	enabled:   ['string', '1'],
	name:      ['string', ''],
	interface: ['string', ''],
	src_addr:  ['string', ''],
	src_port:  ['string', ''],
	dest_addr: ['string', ''],
	dest_port: ['string', ''],
	proto:     ['string', ''],
	chain:     ['string', ''],
};

const dns_policy_schema = { // ucode-lsp disable
	enabled:       ['string', '1'],
	name:          ['string', ''],
	src_addr:      ['string', ''],
	dest_dns:      ['string', ''],
	dest_dns_port: ['string', ''],
};

function parse_options(raw, schema) { // ucode-lsp disable
	let result = {};
	for (let key in schema) {
		let spec = schema[key];
		let v = raw[key];
		switch (spec[0]) {
		case 'bool':
			result[key] = (v == null) ? spec[1] : (+v > 0 || v == 'yes' || v == 'on' || v == 'true');
			break;
		case 'string':
			result[key] = (v == null) ? (spec[1] ?? null) : '' + v;
			break;
		case 'int':
			result[key] = (v == null) ? (spec[1] ?? 0) : +v;
			break;
		case 'list':
			if (v == null) { result[key] = spec[1] ?? ''; }
			else { result[key] = (type(v) == 'array') ? join(' ', v) : '' + v; }
			break;
		}
	}
	return result;
}

// ── env.load_config() ───────────────────────────────────────────────

env.load_config = function(param) {
	if (env._config_loaded) return;
	pbr.is_tty = system('[ -t 2 ]') == 0 ? true : false;
	let raw = uci_ctx(pkg.name, true).get_all(pkg.name, 'config') || {};
	cfg = parse_options(raw, config_schema);

	cfg.uplink_interface4 = cfg.uplink_interface;
	cfg.uplink_interface6_metric = '128';
	cfg.fw_mask = '0x' + cfg.fw_mask;
	cfg.uplink_mark = '0x' + cfg.uplink_mark;

	if (cfg.resolver_set == 'none') cfg.resolver_set = '';
	if (!cfg.ipv6_enabled) cfg.uplink_interface6 = '';

	// Compute fw_maskXor: fw_mask XOR 0xffffffff
	let mask_val = int(hex(cfg.fw_mask));
	let xor_val = mask_val ^ 0xffffffff;
	cfg.fw_maskXor = sprintf('%#x', xor_val) || '0xff00ffff';

	if (!match('' + cfg.procd_boot_trigger_delay, /^[0-9]+$/)) cfg.procd_boot_trigger_delay = '5000';
	if (int(cfg.procd_boot_trigger_delay) < 1000) cfg.procd_boot_trigger_delay = '1000';

	// Build nft_set_flags string
	let nft_set_flags = '';
	let fi = cfg.nft_set_flags_interval;
	let ft = cfg.nft_set_flags_timeout;
	if (fi && ft) {
		nft_set_flags = 'flags interval, timeout' + (cfg.nft_set_timeout ? '; timeout ' + cfg.nft_set_timeout : '');
	} else if (fi && !ft) {
		nft_set_flags = 'flags interval';
	} else if (!fi && ft) {
		nft_set_flags = 'flags timeout' + (cfg.nft_set_timeout ? '; timeout ' + cfg.nft_set_timeout : '');
	}

	if (!cfg.nft_set_flags_timeout && !cfg.nft_set_timeout) cfg.nft_set_gc_interval = '';

	pbr.nft_rule_params = cfg.nft_rule_counter ? 'counter' : '';

	let set_parts = [];
	if (cfg.nft_set_auto_merge) push(set_parts, 'auto-merge;');
	if (cfg.nft_set_counter) push(set_parts, 'counter;');
	if (nft_set_flags) push(set_parts, nft_set_flags + ';');
	if (cfg.nft_set_gc_interval) push(set_parts, 'gc_interval "' + cfg.nft_set_gc_interval + '";');
	if (cfg.nft_set_policy) push(set_parts, 'policy ' + cfg.nft_set_policy + ';');
	if (cfg.nft_set_timeout) push(set_parts, 'timeout "' + cfg.nft_set_timeout + '";');
	pbr.nft_set_params = ' ' + join(' ', set_parts) + ' ';

	// Handle agh config file
	if (is_present('AdGuardHome')) {
		let agh_path = shell('command -v AdGuardHome');
		if (agh_path) {
			let content = readfile(env.agh_config_file);
			if (!content || content == '') {
				let alt = dirname(agh_path) + '/AdGuardHome.yaml';
				content = readfile(alt);
				if (content && content != '')
					env.agh_config_file = alt;
			}
		}
	}

	env._loaded = false;
	env._config_loaded = true;
};

// ── env.load() ──────────────────────────────────────────────────────

env.load = function(param) {
	if (env._loaded) return true;

	let _check_system_health = function() {
		let health_fail = false;
		if (!env.nft_installed) {
			push(pbr.errors, { code: 'errorNoNft' });
			health_fail = true;
		}
		let auto_inc = uci_ctx('firewall').get('firewall', 'defaults', 'auto_includes');
		if (auto_inc == '0') {
			let ctx = uci_ctx('firewall');
			ctx.delete('firewall', 'defaults', 'auto_includes');
			ctx.commit('firewall');
		}
		let ip_link = shell('readlink /sbin/ip 2>/dev/null');
		if (ip_link != pkg.ip_full) {
			push(pbr.errors, { code: 'errorRequiredBinaryMissing', info: 'ip-full' });
			health_fail = true;
		}
		if (!pbr.nft_check_element('table', 'fw4')) {
			push(pbr.errors, { code: 'errorDefaultFw4TableMissing', info: 'fw4' });
			health_fail = true;
		}
		if (is_config_enabled('dns_policy') || is_tor_running()) {
			if (!pbr.nft_check_element('chain', 'dstnat')) {
				push(pbr.errors, { code: 'errorDefaultFw4ChainMissing', info: 'dstnat' });
				health_fail = true;
			}
		}
		let chains = split(pkg.chains_list, ' ');
		for (let c in chains) {
			if (!pbr.nft_check_element('chain', 'mangle_' + c)) {
				push(pbr.errors, { code: 'errorDefaultFw4ChainMissing', info: 'mangle_' + c });
				health_fail = true;
			}
		}
		if (cfg.resolver_set == 'dnsmasq.nftset' && !env.resolver_set_supported) {
			push(pbr.warnings, { code: 'warningResolverNotSupported' });
		}
		let ctx_dhcp = uci_ctx('dhcp');
		let ctx_net = uci_ctx('network');
		ctx_net.foreach('network', 'interface', function(s) {
			let iface = s['.name'];
			if (!is_lan(iface)) return;
			let force = ctx_dhcp.get('dhcp', iface, 'force');
			if (force == '0') {
				push(pbr.warnings, { code: 'warningDhcpLanForce', info: iface });
			}
			if (!cfg.resolver_set) return;
			let dhcp_option = ctx_dhcp.get('dhcp', iface, 'dhcp_option');
			if (type(dhcp_option) != 'array') return;
			let ipaddr = ctx_net.get('network', iface, 'ipaddr') || '';
			let ipaddr_base = split(ipaddr, '/')[0];
			for (let opt in dhcp_option) {
				let parts = split(opt, ',');
				if (length(parts) >= 2) {
					let option = parts[0];
					let value = parts[1];
					if (option == '6' && value != ipaddr_base) {
						push(pbr.warnings, { code: 'warningIncompatibleDHCPOption6', info: iface + ': ' + value });
					}
				}
			}
		});
		return !health_fail;
	};

	let start_time, end_time;

	switch (param) {
	case 'on_start':
		output.info('Loading environment (' + param + ') ');
		start_time = time();
		env.load_config(param);
		end_time = time();
		logger_debug('[PERF-DEBUG] Loading config took ' + (end_time - start_time) + 's');
		if (!cfg.enabled) {
			output.info_failn();
			push(pbr.errors, { code: 'errorServiceDisabled' });
			output.error(get_text('errorServiceDisabled'));
			output.print("Run the following commands before starting service again:\\n");
			output.print("uci set " + pkg.name + ".config.enabled='1'; uci commit " + pkg.name + ";\\n");
			return false;
		}
		start_time = time();
		env.detect();
		end_time = time();
		logger_debug('[PERF-DEBUG] Detecting environment took ' + (end_time - start_time) + 's');
		if (!_check_system_health()) {
			output.info_failn();
			return false;
		}
		start_time = time();
		env.load_network(param);
		end_time = time();
		logger_debug('[PERF-DEBUG] Loading network data took ' + (end_time - start_time) + 's');
		output.info_okn();
		break;

	case 'on_stop':
	case 'on_reload':
	case 'on_interface_reload':
		output.info('Loading environment (' + param + ') ');
		start_time = time();
		env.load_config(param);
		end_time = time();
		logger_debug('[PERF-DEBUG] Loading config took ' + (end_time - start_time) + 's');
		start_time = time();
		env.detect();
		end_time = time();
		logger_debug('[PERF-DEBUG] Detecting environment took ' + (end_time - start_time) + 's');
		start_time = time();
		env.load_network(param);
		end_time = time();
		logger_debug('[PERF-DEBUG] Loading network data took ' + (end_time - start_time) + 's');
		output.info_okn();
		break;

	case 'netifd':
	case 'service_started':
		env.load_config(param);
		break;

	case 'rpcd':
		env.load_config(param);
		env.detect();
		env.load_network(param);
		break;

	case 'status':
		env.load_config(param);
		env.detect();
		env.load_network(param);
		break;
	}

	env._loaded = true;
	return true;
};

// ── env.load_network() ──────────────────────────────────────────────

env.load_network = function(param) {
	if (!env.ifaces_supported || env.ifaces_supported == '') {
		// Find firewall WAN zone
		let ctx_fw = uci_ctx('firewall', true);
		ctx_fw.foreach('firewall', 'zone', function(s) {
			if (s.name == 'wan') env.firewall_wan_zone = s['.name'];
		});
		// Get network list from WAN zone
		let wan_networks = ctx_fw.get('firewall', env.firewall_wan_zone, 'network');
		if (type(wan_networks) == 'array') {
			for (let n in wan_networks) {
				if (is_supported_interface(n) && !str_contains(env.ifaces_supported, n))
					env.ifaces_supported += n + ' ';
			}
		} else if (wan_networks && is_supported_interface(wan_networks) && !str_contains(env.ifaces_supported, wan_networks)) {
			env.ifaces_supported += wan_networks + ' ';
		}
		// Build from network interfaces
		let ctx_net = uci_ctx('network', true);
		ctx_net.foreach('network', 'interface', function(s) {
			let iface = s['.name'];
			if (is_supported_interface(iface) && !str_contains(env.ifaces_supported, iface))
				env.ifaces_supported += iface + ' ';
		});

		// Build webui interfaces list (ifaces_supported + split_uplink filter + extras)
		let webui = '';
		for (let n in split(trim(env.ifaces_supported), /\s+/)) {
			if (is_split_uplink() && is_uplink6(n)) continue;
			if (!str_contains(webui, n)) webui += n + ' ';
		}
		if (is_tor_running()) webui += 'tor ';
		let si = cfg.supported_interface;
		if (type(si) == 'array') si = join(' ', si);
		for (let x in split(si || '', /\s+/)) {
			if (is_xray(x)) webui += x + ' ';
		}
		if (cfg.webui_show_ignore_target == '1') webui += 'ignore ';
		env.webui_interfaces = split(trim(webui), /\s+/);
	}

	let dev4 = network_get_device(cfg.uplink_interface4);
	if (!dev4) dev4 = network_get_physdev(cfg.uplink_interface4);
	if (!env.uplink_gw4)
		env.uplink_gw4 = pbr.get_gateway4(cfg.uplink_interface4, dev4);

	if (cfg.ipv6_enabled) {
		let dev6 = network_get_device(cfg.uplink_interface6);
		if (!dev6) dev6 = network_get_physdev(cfg.uplink_interface6);
		if (!env.uplink_gw6)
			env.uplink_gw6 = pbr.get_gateway6(cfg.uplink_interface6, dev6);
	}

	if (!env._network_output_done && (param == 'on_boot' || param == 'on_start')) {
		env._network_output_done = true;
		if (cfg.uplink_interface4)
			output.verbose('Using uplink' + (cfg.uplink_interface6 ? ' IPv4' : '') + ' interface (' + param + '): ' + cfg.uplink_interface4 + ' ' + sym.ok[1] + '\\n');
		if (env.uplink_gw4)
			output.verbose('Found uplink' + (cfg.uplink_interface6 ? ' IPv4' : '') + ' gateway (' + param + '): ' + env.uplink_gw4 + ' ' + sym.ok[1] + '\\n');
		if (cfg.uplink_interface6)
			output.verbose('Using uplink IPv6 interface (' + param + '): ' + cfg.uplink_interface6 + ' ' + sym.ok[1] + '\\n');
		if (env.uplink_gw6)
			output.verbose('Found uplink IPv6 gateway (' + param + '): ' + env.uplink_gw6 + ' ' + sym.ok[1] + '\\n');
	}

	env.uplink_gw = env.uplink_gw4 || env.uplink_gw6;
};

// ── is_wan_up() ─────────────────────────────────────────────────────

function is_wan_up(param) {
	let ctx = uci_ctx('network');
	if (!ctx.get('network', cfg.uplink_interface4)) {
		push(pbr.errors, { code: 'errorNoUplinkInterface', info: cfg.uplink_interface4 });
		push(pbr.errors, { code: 'errorNoUplinkInterfaceHint', info: pkg.url('#uplink_interface') });
		return false;
	}
	network_flush_cache();
	env.load_network(param);
	if (env.uplink_gw) {
		return true;
	} else {
		push(pbr.errors, { code: 'errorNoUplinkGateway' });
		return false;
	}
}

// ── NFT Operations ──────────────────────────────────────────────────

function nft_add(line) {
	if (line) pbr.nft_file.append('main', line);}

function nft4(line) {
	nft_add(line);
	return true;
}

function nft6(line) {
	if (!cfg.ipv6_enabled) return true;
	nft_add(line);
}

function nft_call(...args) {
	return sys('nft ' + join(' ', args)) == 0;
}

pbr.nft_check_element = function(element_type, name) {
	if (!pbr.nft_fw4_dump)
		pbr.nft_fw4_dump = shell('nft list table inet fw4 2>&1');
	if (element_type == 'table' && name == 'fw4')
		return !!(pbr.nft_fw4_dump && pbr.nft_fw4_dump != '');
	let lines = split(pbr.nft_fw4_dump, '\n');
	for (let line in lines) {
		if (index(line, element_type) >= 0 && index(line, name) >= 0)
			return true;
	}
	return false;
};

pbr.nft_file.append = function(target, ...extra) {
	let line = join(' ', extra);
	if (line)
		push(pbr.nft_lines, line);
	return true;
};

pbr.nft_file.init = function(target) {
	let nft_prefix = pkg.nft_prefix;
	let nft_table = pkg.nft_table;
	let chains_list = pkg.chains_list;

	switch (target) {
	case 'main': {
		unlink(pkg.nft_temp_file);
		unlink(pkg.nft_main_file);
		mkdir_p(dirname(pkg.nft_temp_file));
		mkdir_p(dirname(pkg.nft_main_file));
		pbr.nft_lines = [];
		pbr._mark_chains_created = {};
		// Emit nft define statements for fw mark/mask and per-interface chain names
		push(pbr.nft_lines, 'define ' + nft_prefix + '_fw_mark = ' + cfg.fw_mask);
		push(pbr.nft_lines, 'define ' + nft_prefix + '_fw_mask = ' + cfg.fw_maskXor);
		for (let iname in keys(pbr.interface)) {
			let idata = pbr.interface[iname];
			if (type(idata) == 'function') continue;
			if (idata?.chain_name) {
				push(pbr.nft_lines, 'define ' + nft_prefix + '_' + iname + '_chain = ' + idata.chain_name);
			}
		}
		push(pbr.nft_lines, '');
		// Create pbr chains in fw4 table
		let chains = split(chains_list, ' ');
		for (let ch in ['dstnat', ...chains])
			push(pbr.nft_lines, 'add chain inet ' + nft_table + ' ' + nft_prefix + '_' + ch + ' {}');
		push(pbr.nft_lines, '');
		// Add jump rules from fw4 chains to pbr chains
		push(pbr.nft_lines, 'add rule inet ' + nft_table + ' dstnat jump ' + nft_prefix + '_dstnat');
		push(pbr.nft_lines, 'add rule inet ' + nft_table + ' mangle_prerouting jump ' + nft_prefix + '_prerouting');
		push(pbr.nft_lines, 'add rule inet ' + nft_table + ' mangle_output jump ' + nft_prefix + '_output');
		push(pbr.nft_lines, 'add rule inet ' + nft_table + ' mangle_forward jump ' + nft_prefix + '_forward');
		push(pbr.nft_lines, '');
		// Insert PBR guards
		let rule_params = pbr.nft_rule_params ? ' ' + pbr.nft_rule_params : '';
		for (let ch in chains)
			push(pbr.nft_lines, 'add rule inet ' + nft_table + ' ' + nft_prefix + '_' + ch +
				rule_params + ' meta mark & ' + cfg.fw_mask + ' != 0 return');
		break;
	}
	case 'netifd':
		unlink(pkg.nft_temp_file);
		unlink(pkg.nft_netifd_file);
		mkdir_p(dirname(pkg.nft_temp_file));
		mkdir_p(dirname(pkg.nft_netifd_file));
		pbr.nft_lines = [];
		break;
	}
	return true;
};

pbr.nft_file.remove = function(target) {
	switch (target) {
	case 'main':
		pbr.nft_lines = [];
		unlink(pkg.nft_temp_file);
		unlink(pkg.nft_main_file);
		break;
	case 'netifd':
		output.print('Removing fw4 netifd nft file ');
		if (unlink(pkg.nft_netifd_file) != false) {
			output.okbn();
		} else {
			push(pbr.errors, { code: 'errorNftNetifdFileDelete', info: pkg.nft_netifd_file });
			output.failn();
		}
		break;
	}
	return true;
};

pbr.nft_file.exists = function(target) {
	switch (target) {
	case 'main': {
		let sm = stat(pkg.nft_main_file);
		return sm != null && sm.size > 0;
	}
	case 'netifd': {
		let sn = stat(pkg.nft_netifd_file);
		return sn != null && sn.size > 0;
	}
	}
	return false;
};

pbr.nft_file.apply = function(target) {
	switch (target) {
	case 'main': {
		if (!length(pbr.nft_lines)) return false;
		mkdir_p(dirname(pkg.nft_temp_file));
		mkdir_p(dirname(pkg.nft_main_file));
		writefile(pkg.nft_temp_file, '#!/usr/sbin/nft -f\n\n' + join('\n', pbr.nft_lines) + '\n');
		output.print('Installing fw4 nft file ');
		if (nft_call('-c', '-f', pkg.nft_temp_file) &&
			sys('cp -f ' + shell_quote(pkg.nft_temp_file) + ' ' + shell_quote(pkg.nft_main_file)) == 0) {
			output.okn();
			sys('fw4 -q reload');
			return true;
		} else {
			push(pbr.errors, { code: 'errorNftMainFileInstall', info: pkg.nft_temp_file });
			output.failn();
			return false;
		}
	}
	case 'netifd': {
		if (!length(pbr.nft_lines)) return false;
		mkdir_p(dirname(pkg.nft_temp_file));
		mkdir_p(dirname(pkg.nft_netifd_file));
		writefile(pkg.nft_temp_file, '#!/usr/sbin/nft -f\n\n' + join('\n', pbr.nft_lines) + '\n');
		output.print('Installing fw4 netifd nft file ');
		if (nft_call('-c', '-f', pkg.nft_temp_file) &&
			sys('cp -f ' + shell_quote(pkg.nft_temp_file) + ' ' + shell_quote(pkg.nft_netifd_file)) == 0) {
			output.okbn();
			return true;
		} else {
			push(pbr.errors, { code: 'errorNftNetifdFileInstall', info: pkg.nft_temp_file });
			output.failn();
			return false;
		}
	}
	}
	return true;
};

pbr.nft_file.match = function(target, ...extra) {
	let pattern = length(extra) > 0 ? extra[0] : '';
	let content = join('\n', pbr.nft_lines);
	return index(content, pattern) >= 0;
};

pbr.nft_file.filter = function(target, ...extra) {
	// Remove all accumulated lines matching the given pattern string
	let pattern = length(extra) > 0 ? extra[0] : '';
	if (pattern)
		pbr.nft_lines = filter(pbr.nft_lines, l => index(l, pattern) < 0);
	return true;
};

pbr.nft_file.sed = function(target, ...extra) {
	let sed_args2 = join(' ', extra);
	sys('sed -i ' + sed_args2 + ' ' + shell_quote(pkg.nft_netifd_file));
	return true;
};

pbr.nft_file.show = function(target) {
	switch (target) {
	case 'main': {
		let content_m = readfile(pkg.nft_main_file) || '';
		let lines_m = split(content_m, '\n');
		let result_m = pkg.name + ' fw4 nft file: ' + pkg.nft_main_file + '\n';
		for (let i = 2; i < length(lines_m); i++)
			result_m += lines_m[i] + '\n';
		return result_m;
	}
	case 'netifd': {
		let content_n = readfile(pkg.nft_netifd_file) || '';
		let lines_n = split(content_n, '\n');
		let result_n = pkg.name + ' fw4 netifd nft file: ' + pkg.nft_netifd_file + '\n';
		for (let i = 2; i < length(lines_n); i++)
			result_n += lines_n[i] + '\n';
		return result_n;
	}
	}
	return '';
};

// ── nftset() ────────────────────────────────────────────────────────

pbr.get_set_name = function(iface, family, target, type_val, uid) {
	return pkg.nft_prefix + '_' + (iface ? iface + '_' : '') + (family || '4') +
		(target ? '_' + target : '') + (type_val ? '_' + type_val : '') + (uid ? '_' + uid : '');
};

pbr.nftset = function(command, iface, target, type_val, uid, comment, param) {
	target = target || 'dst';
	type_val = type_val || 'ip';
	let mark = param;
	let nft_prefix = pkg.nft_prefix;
	let nft_table = pkg.nft_table;

	let nftset4 = pbr.get_set_name(iface, '4', target, type_val, uid);
	let nftset6 = pbr.get_set_name(iface, '6', target, type_val, uid);

	if (length(nftset4) > 255) {
		push(pbr.errors, { code: 'errorNftsetNameTooLong', info: nftset4 });
		return false;
	}

	let ipv4_error = true;
	let ipv6_error = true;

	switch (command) {
	case 'add':
		if (is_mac_address(param) || index('' + param, ',') >= 0 || index('' + param, ' ') >= 0) {
			nft4('add element inet ' + nft_table + ' ' + nftset4 + ' { ' + param + ' }');
			ipv4_error = false;
			nft6('add element inet ' + nft_table + ' ' + nftset6 + ' { ' + param + ' }');
			ipv6_error = false;
		} else if (is_ipv4(param)) {
			nft4('add element inet ' + nft_table + ' ' + nftset4 + ' { ' + param + ' }');
			ipv4_error = false;
		} else if (is_ipv6(param)) {
			nft6('add element inet ' + nft_table + ' ' + nftset6 + ' { ' + param + ' }');
			ipv6_error = false;
		} else {
			let param4 = '', param6 = '';
			if (target == 'src') {
				param4 = ipv4_leases_to_nftset(param);
				param6 = ipv6_leases_to_nftset(param);
			}
			if (!param4) param4 = resolveip_to_nftset4(param);
			if (!param6) param6 = resolveip_to_nftset6(param);
			if (!param4 && !param6) {
				push(pbr.errors, { code: 'errorFailedToResolve', info: param });
			} else {
				if (param4) { nft4('add element inet ' + nft_table + ' ' + nftset4 + ' { ' + param4 + ' }'); ipv4_error = false; }
				if (param6) { nft6('add element inet ' + nft_table + ' ' + nftset6 + ' { ' + param6 + ' }'); ipv6_error = false; }
			}
		}
		break;
	case 'add_dnsmasq_element': {
		if (!cfg.ipv6_enabled) nftset6 = '';
		let entry = 'nftset=/' + param + '/4#inet#' + nft_table + '#' + nftset4 +
			(nftset6 ? ',6#inet#' + nft_table + '#' + nftset6 : '') +
			' # ' + comment;
		let existing = readfile(pkg.dnsmasq_file) || '';
		if (index(existing, entry) >= 0) return true;
		let fh = open(pkg.dnsmasq_file, 'a');
		if (fh) {
			fh.write(entry + '\n');
			fh.close();
			ipv4_error = false;
		}
		break;
	}
	case 'create':
		switch (type_val) {
		case 'ip':
		case 'net':
			nft4('add set inet ' + nft_table + ' ' + nftset4 + ' { type ipv4_addr;' + pbr.nft_set_params + ' comment "' + comment + '";}');
			ipv4_error = false;
			nft6('add set inet ' + nft_table + ' ' + nftset6 + ' { type ipv6_addr;' + pbr.nft_set_params + ' comment "' + comment + '";}');
			ipv6_error = false;
			break;
		case 'mac':
			nft4('add set inet ' + nft_table + ' ' + nftset4 + ' { type ether_addr;' + pbr.nft_set_params + ' comment "' + comment + '";}');
			ipv4_error = false;
			nft6('add set inet ' + nft_table + ' ' + nftset6 + ' { type ether_addr;' + pbr.nft_set_params + ' comment "' + comment + '";}');
			ipv6_error = false;
			break;
		}
		break;
	case 'create_dnsmasq_set':
		nft4('add set inet ' + nft_table + ' ' + nftset4 + ' { type ipv4_addr;' + pbr.nft_set_params + ' comment "' + comment + '";}');
		ipv4_error = false;
		nft6('add set inet ' + nft_table + ' ' + nftset6 + ' { type ipv6_addr;' + pbr.nft_set_params + ' comment "' + comment + '";}');
		ipv6_error = false;
		break;
	case 'create_user_set':
		switch (type_val) {
		case 'ip':
		case 'net':
			nft4('add set inet ' + nft_table + ' ' + nftset4 + ' { type ipv4_addr;' + pbr.nft_set_params + ' comment "' + comment + '";}');
			ipv4_error = false;
			nft6('add set inet ' + nft_table + ' ' + nftset6 + ' { type ipv6_addr;' + pbr.nft_set_params + ' comment "' + comment + '";}');
			ipv6_error = false;
			if (target == 'dst') {
				nft4('add rule inet ' + nft_table + ' ' + nft_prefix + '_prerouting ' + pkg.nft_ipv4_flag + ' daddr @' + nftset4 + ' ' + pbr.nft_rule_params + ' goto ' + nft_prefix + '_mark_' + mark);
				nft6('add rule inet ' + nft_table + ' ' + nft_prefix + '_prerouting ' + pkg.nft_ipv6_flag + ' daddr @' + nftset6 + ' ' + pbr.nft_rule_params + ' goto ' + nft_prefix + '_mark_' + mark);
			} else if (target == 'src') {
				nft4('add rule inet ' + nft_table + ' ' + nft_prefix + '_prerouting ' + pkg.nft_ipv4_flag + ' saddr @' + nftset4 + ' ' + pbr.nft_rule_params + ' goto ' + nft_prefix + '_mark_' + mark);
				nft6('add rule inet ' + nft_table + ' ' + nft_prefix + '_prerouting ' + pkg.nft_ipv6_flag + ' saddr @' + nftset6 + ' ' + pbr.nft_rule_params + ' goto ' + nft_prefix + '_mark_' + mark);
			}
			break;
		case 'mac':
			nft4('add set inet ' + nft_table + ' ' + nftset4 + ' { type ether_addr;' + pbr.nft_set_params + ' comment "' + comment + '"; }');
			ipv4_error = false;
			nft6('add set inet ' + nft_table + ' ' + nftset6 + ' { type ether_addr;' + pbr.nft_set_params + ' comment "' + comment + '"; }');
			ipv6_error = false;
			nft4('add rule inet ' + nft_table + ' ' + nft_prefix + '_prerouting ether saddr @' + nftset4 + ' ' + pbr.nft_rule_params + ' goto ' + nft_prefix + '_mark_' + mark);
			nft6('add rule inet ' + nft_table + ' ' + nft_prefix + '_prerouting ether saddr @' + nftset6 + ' ' + pbr.nft_rule_params + ' goto ' + nft_prefix + '_mark_' + mark);
			break;
		}
		break;
	case 'delete':
	case 'destroy':
		if (nft_call('delete', 'set', 'inet', nft_table, nftset4)) ipv4_error = false;
		if (nft_call('delete', 'set', 'inet', nft_table, nftset6)) ipv6_error = false;
		break;
	case 'delete_user_set':
		if (nft_call('delete', 'set', 'inet', nft_table, nftset4)) ipv4_error = false;
		if (nft_call('delete', 'set', 'inet', nft_table, nftset6)) ipv6_error = false;
		switch (type_val) {
		case 'ip':
		case 'net':
			if (target == 'dst') {
				nft_call('delete', 'rule', 'inet', nft_table, nft_prefix + '_prerouting', pkg.nft_ipv4_flag, 'daddr', '@' + nftset4, 'goto', nft_prefix + '_mark_' + mark);
				ipv4_error = false;
				nft_call('delete', 'rule', 'inet', nft_table, nft_prefix + '_prerouting', pkg.nft_ipv6_flag, 'daddr', '@' + nftset6, 'goto', nft_prefix + '_mark_' + mark);
				ipv6_error = false;
			} else if (target == 'src') {
				nft_call('delete', 'rule', 'inet', nft_table, nft_prefix + '_prerouting', pkg.nft_ipv4_flag, 'saddr', '@' + nftset4, 'goto', nft_prefix + '_mark_' + mark);
				ipv4_error = false;
				nft_call('delete', 'rule', 'inet', nft_table, nft_prefix + '_prerouting', pkg.nft_ipv6_flag, 'saddr', '@' + nftset6, 'goto', nft_prefix + '_mark_' + mark);
				ipv6_error = false;
			}
			break;
		case 'mac':
			nft_call('delete', 'rule', 'inet', nft_table, nft_prefix + '_prerouting', 'ether', 'saddr', '@' + nftset4, 'goto', nft_prefix + '_mark_' + mark);
			ipv4_error = false;
			nft_call('delete', 'rule', 'inet', nft_table, nft_prefix + '_prerouting', 'ether', 'saddr', '@' + nftset6, 'goto', nft_prefix + '_mark_' + mark);
			ipv6_error = false;
			break;
		}
		break;
	case 'flush':
	case 'flush_user_set':
		if (nft_call('flush', 'set', 'inet', nft_table, nftset4)) ipv4_error = false;
		if (nft_call('flush', 'set', 'inet', nft_table, nftset6)) ipv6_error = false;
		break;
	}

	// nft6 returns true if IPv6 support is not enabled
	if (!cfg.ipv6_enabled) ipv6_error = true;
	return !ipv4_error || !ipv6_error;
};

// ── cleanup() ───────────────────────────────────────────────────────

pbr.cleanup = function(...actions) {
	for (let action in actions) {
		switch (action) {
		case 'rt_tables': {
			let content = readfile(pkg.rt_tables_file) || '';
			let lines = split(content, '\n');
			let new_lines = [];
			for (let line in lines) {
				let m = match(line, regexp(pkg.ip_table_prefix + '_(.*)'));
				if (m) {
					let table_name = pkg.ip_table_prefix + '_' + m[1];
					if (!is_netifd_table(table_name))
						continue;
				}
				push(new_lines, line);
			}
			writefile(pkg.rt_tables_file, join('\n', new_lines) + '\n');
			sys('sync');
			break;
		}
		case 'main_table': {
			let mask_val = hex(cfg.fw_mask);
			let mark_val = hex(cfg.uplink_mark);
			let max_ifaces = mask_val / mark_val;
			let prio_max = int(cfg.uplink_ip_rules_priority) + 1;
			let prio_min = int(cfg.uplink_ip_rules_priority) - max_ifaces;

			// IPv4 rules cleanup
			let rules4 = shell(pkg.ip_full + ' -4 rule show 2>/dev/null');
			if (rules4) {
				let rule_lines = split(rules4, '\n');
				for (let line in rule_lines) {
					let m = match(line, /^(\d+):/);
					if (!m) continue;
					let prio = +m[1];
					if (prio < prio_min || prio > prio_max) continue;
					// Skip netifd-managed fwmark rules
					if (index(line, 'fwmark') >= 0 && index(line, 'lookup ' + pkg.ip_table_prefix + '_') >= 0) {
						let tm = match(line, /lookup\s+(\S+)/);
						if (tm && is_netifd_table(tm[1])) continue;
					}
					system(pkg.ip_full + ' -4 rule del priority ' + prio + ' 2>/dev/null');
				}
			}
			// Legacy cleanup
			system(pkg.ip_full + ' -4 rule del lookup main suppress_prefixlength ' + cfg.prefixlength + ' 2>/dev/null');

			// IPv6 rules cleanup (always, even if ipv6 currently disabled)
			let rules6 = shell(pkg.ip_full + ' -6 rule show 2>/dev/null');
			if (rules6) {
				let rule_lines6 = split(rules6, '\n');
				for (let line in rule_lines6) {
					let m = match(line, /^(\d+):/);
					if (!m) continue;
					let prio = +m[1];
					if (prio < prio_min || prio > prio_max) continue;
					if (index(line, 'fwmark') >= 0 && index(line, 'lookup ' + pkg.ip_table_prefix + '_') >= 0) {
						let tm = match(line, /lookup\s+(\S+)/);
						if (tm && is_netifd_table(tm[1])) continue;
					}
					system(pkg.ip_full + ' -6 rule del priority ' + prio + ' 2>/dev/null');
				}
			}
			system(pkg.ip_full + ' -6 rule del lookup main suppress_prefixlength ' + cfg.prefixlength + ' 2>/dev/null');
			break;
		}
		case 'main_chains': {
			let chains = split(pkg.chains_list, ' ');
			for (let c in [...chains, 'dstnat']) {
				c = lc(c);
				nft_call('flush', 'chain', 'inet', pkg.nft_table, c);
			}
			break;
		}
		case 'marking_chains': {
			let mark_chains = get_mark_nft_chains();
			if (mark_chains) {
				let external = get_external_mark_chains();
				let mc_list = split(mark_chains, ' ');
				for (let mc in mc_list) {
					mc = trim(mc);
					if (mc && !external[mc])
						nft_call('delete', 'chain', 'inet', pkg.nft_table, mc);
				}
			}
			break;
		}
		case 'sets': {
			let nft_sets = get_nft_sets();
			if (nft_sets) {
				let sets_list = split(nft_sets, '\n');
				for (let s in sets_list) {
					s = trim(s);
					if (s)
						nft_call('delete', 'set', 'inet', pkg.nft_table, s);
				}
			}
			break;
		}
		}
	}
	return true;
};

// ── Status Management ────────────────────────────────────────────────
// All status is kept in-memory in status — no JSON file I/O.

// ── resolver() ──────────────────────────────────────────────────────

pbr.resolver = function(param, iface, target, type_val, uid, name, value) {
	let _uci_has_changes = function(config) {
		return length(uci_ctx(config).changes(config) || []) > 0;
	};

	let _uci_add_list_if_new = function(config, section, option, value) {
		if (!config || !section || !option || !value) return false;
		let ctx = uci_ctx(config);
		let current = ctx.get(config, section, option);
		if (type(current) == 'array' && index(current, value) >= 0) return true;
		if (current == value) return true;
		ctx.list_append(config, section, option, value);
		ctx.save(config);
		return true;
	};

	let _dnsmasq_get_confdir = function(instance) {
		let ctx = uci_ctx('dhcp');
		let dhcp_cfg = ctx.get('dhcp', instance) ? instance : null;
		if (!dhcp_cfg) {
			ctx.foreach('dhcp', 'dnsmasq', function(s) {
				if (s['.name'] == instance || s['.index'] == instance)
					dhcp_cfg = s['.name'];
			});
		}
		if (!pbr.dnsmasq_ubus)
			pbr.dnsmasq_ubus = ubus_call('service', 'list', { name: 'dnsmasq' });
		let cfg_file = null;
		if (pbr.dnsmasq_ubus?.dnsmasq?.instances?.[dhcp_cfg]?.command) {
			let cmd_parts = pbr.dnsmasq_ubus.dnsmasq.instances[dhcp_cfg].command;
			if (type(cmd_parts) == 'array') {
				for (let i = 0; i < length(cmd_parts); i++) {
					if (cmd_parts[i] == '-C' && i + 1 < length(cmd_parts)) {
						cfg_file = cmd_parts[i + 1];
						break;
					}
				}
			}
		}
		if (!cfg_file) return null;
		let content = readfile(cfg_file) || '';
		let m = match(content, /(^|\n)conf-dir=([^\n]*)/);
		return m ? m[2] : null;
	};

	let _dnsmasq_instance_cleanup = function(instance) {
		if (!stat('/etc/config/dhcp')?.type) return true;
		let ctx = uci_ctx('dhcp');
		if (!ctx.get('dhcp', instance)) return false;
		let confdir = _dnsmasq_get_confdir(instance);
		if (confdir) unlink(confdir + '/' + pkg.name);
		let current = ctx.get('dhcp', instance, 'addnmount');
		if (type(current) == 'array') {
			let idx = index(current, pkg.dnsmasq_file);
			if (idx >= 0) {
				ctx.reorder('dhcp', instance, idx);
				ctx.delete('dhcp', instance, 'addnmount', pkg.dnsmasq_file);
				ctx.save('dhcp');
			}
		}
		return true;
	};

	let _dnsmasq_instance_setup = function(instance) {
		if (!stat('/etc/config/dhcp')?.type) return true;
		let ctx = uci_ctx('dhcp');
		if (!ctx.get('dhcp', instance)) return false;
		_uci_add_list_if_new('dhcp', instance, 'addnmount', pkg.dnsmasq_file);
		let confdir = _dnsmasq_get_confdir(instance);
		if (!confdir) return false;
		sys('ln -sf ' + shell_quote(pkg.dnsmasq_file) + ' ' + shell_quote(confdir + '/' + pkg.name));
		sys('chmod 660 ' + shell_quote(confdir + '/' + pkg.name));
		sys('chown -h root:dnsmasq ' + shell_quote(confdir + '/' + pkg.name));
		return true;
	};
	switch (cfg.resolver_set) {
	case '':
	case 'none':
		switch (param) {
		case 'add_resolver_element': return false;
		case 'create_resolver_set': return false;
		case 'check_support': return true;
		case 'cleanup': return true;
		case 'configure': return true;
		case 'kill': return true;
		case 'reload': return true;
		case 'restart': return true;
		case 'compare_hash': return true;
		case 'store_hash': return true;
		case 'wait': {
			if (pbr.resolver_working_flag) return true;
			let timeout = +(iface || '30');
			let hostname = uci_ctx('system').get('system', '@system[0]', 'hostname') || 'OpenWrt';
			for (let count = 0; count < timeout; count++) {
				if (sys('resolveip ' + shell_quote(hostname)) == 0) {
					pbr.resolver_working_flag = true;
					return true;
				}
				system('sleep 1');
			}
			return false;
		}
		}
		break;

	case 'dnsmasq.nftset':
		switch (param) {
		case 'add_resolver_element':
			if (!env.resolver_set_supported) return false;
			if (target == 'src') return false;
			let words = split(trim('' + (value || '')), /\s+/);
			for (let d in words) {
				pbr.nftset('add_dnsmasq_element', iface, target, type_val, uid, name, d);
			}
			return true;
		case 'create_resolver_set':
			if (!env.resolver_set_supported) return false;
			if (target == 'src') return false;
			return pbr.nftset('create_dnsmasq_set', iface, target, type_val, uid, name, value);
		case 'check_support':
			return env.resolver_set_supported;
		case 'cleanup':
			if (!env.resolver_set_supported) return false;
			unlink(pkg.dnsmasq_file);
			let ctx_dhcp = uci_ctx('dhcp', true);
			ctx_dhcp.foreach('dhcp', 'dnsmasq', function(s) {
				_dnsmasq_instance_cleanup(s['.name']);
			});
			return true;
		case 'configure':
			if (!env.resolver_set_supported) return false;
			unlink(pkg.dnsmasq_file);
			writefile(pkg.dnsmasq_file, '');
			let ctx2 = uci_ctx('dhcp', true);
			if (cfg.resolver_instance == '*') {
				ctx2.foreach('dhcp', 'dnsmasq', function(s) {
					_dnsmasq_instance_setup(s['.name']);
				});
			} else {
				ctx2.foreach('dhcp', 'dnsmasq', function(s) {
					_dnsmasq_instance_cleanup(s['.name']);
				});
				let instances = split(trim(cfg.resolver_instance), /\s+/);
				for (let inst in instances) {
					if (!_dnsmasq_instance_setup('@dnsmasq[' + inst + ']'))
						_dnsmasq_instance_setup(inst);
				}
			}
			return true;
		case 'kill':
			if (env.resolver_set_supported)
				sys('killall -q -s HUP dnsmasq');
			return true;
		case 'reload':
			if (!env.resolver_set_supported) return false;
			output.debug('Reloading dnsmasq ');
			if (sys('/etc/init.d/dnsmasq reload') == 0) {
				output.debug_okn();
				return true;
			} else {
				output.debug_failn();
				return false;
			}
		case 'restart':
			if (!env.resolver_set_supported) return false;
			output.debug('Restarting dnsmasq ');
			if (sys('/etc/init.d/dnsmasq restart') == 0) {
				output.debug_okn();
				return true;
			} else {
				output.debug_failn();
				return false;
			}
		case 'compare_hash': {
			if (!env.resolver_set_supported) return false;
			if (_uci_has_changes('dhcp')) {
				uci_ctx('dhcp').commit('dhcp');
			}
			let resolver_new_hash = null;
			let s = stat(pkg.dnsmasq_file);
			if (s && s.size > 0) {
				let md5_out = shell('md5sum ' + shell_quote(pkg.dnsmasq_file));
				let m = match(md5_out, /^(\S+)/);
				resolver_new_hash = m ? m[1] : null;
			}
			return resolver_new_hash != pbr.resolver_stored_hash;
		}
		case 'store_hash': {
			let s = stat(pkg.dnsmasq_file);
			if (s && s.size > 0) {
				let md5_out = shell('md5sum ' + shell_quote(pkg.dnsmasq_file));
				let m = match(md5_out, /^(\S+)/);
				pbr.resolver_stored_hash = m ? m[1] : '';
			}
			return true;
		}
		case 'wait': {
			if (pbr.resolver_working_flag) return true;
			let timeout = +(iface || '30');
			let hostname = uci_ctx('system').get('system', '@system[0]', 'hostname') || 'OpenWrt';
			for (let count = 0; count < timeout; count++) {
				if (sys('resolveip ' + shell_quote(hostname)) == 0) {
					pbr.resolver_working_flag = true;
					return true;
				}
				system('sleep 1');
			}
			return false;
		}
		}
		break;

	case 'unbound.nftset':
		// Stub: not yet implemented
		return true;
	}

	return true;
};

// ── Address Classification Helper ────────────────────────────────────
// Classifies an address value (src or dest) into nft match parameters.
// direction: 'src' or 'dst'
// use_resolver: if true, try resolver set for domains before falling back to resolveip
// Returns: { param4, param6, empty4, empty6 }

function classify_addr(value, direction, iface, uid, name, use_resolver) {
	let negation = '', nftset_suffix = '';
	if (substr(value, 0, 1) == '!') {
		negation = '!= ';
		value = replace(value, /!/g, '');
		nftset_suffix = '_neg';
	}
	let first_val = str_first_word(value);
	let param4 = '', param6 = '';
	let empty4 = false, empty6 = false;

	let ifname_key = (direction == 'src') ? 'iifname' : 'oifname';
	let addr_dir = (direction == 'src') ? 'saddr' : 'daddr';
	let target = (direction == 'src') ? 'src' : 'dst';

	if (is_phys_dev(first_val)) {
		param4 = ifname_key + ' ' + negation + '{ ' + inline_set(value) + ' }';
		param6 = param4;
	} else if (direction == 'src' && is_mac_address(first_val)) {
		param4 = 'ether saddr ' + negation + '{ ' + inline_set(value) + ' }';
		param6 = param4;
	} else if (is_domain(first_val)) {
		if (use_resolver && iface &&
			pbr.resolver('create_resolver_set', iface, target, 'ip', uid, name) &&
			pbr.resolver('add_resolver_element', iface, target, 'ip', uid, name, value)) {
			let nft_prefix = pkg.nft_prefix;
			param4 = pkg.nft_ipv4_flag + ' ' + addr_dir + ' ' + negation +
				'@' + nft_prefix + '_' + iface + '_4_' + target + '_ip_' + uid + nftset_suffix;
			param6 = pkg.nft_ipv6_flag + ' ' + addr_dir + ' ' + negation +
				'@' + nft_prefix + '_' + iface + '_6_' + target + '_ip_' + uid + nftset_suffix;
		} else {
			let is4 = '', is6 = '';
			for (let d in split(value, /\s+/)) {
				if (!d) continue;
				let r4 = resolveip_to_nftset4(d);
				let r6 = resolveip_to_nftset6(d);
				if (!r4 && !r6) {
					push(pbr.errors, { code: 'errorFailedToResolve', info: d });
				} else {
					if (r4) is4 += (is4 ? ', ' : '') + r4;
					if (r6) is6 += (is6 ? ', ' : '') + r6;
				}
			}
			if (!is4) empty4 = true;
			if (!is6) empty6 = true;
			param4 = pkg.nft_ipv4_flag + ' ' + addr_dir + ' ' + negation + '{ ' + is4 + ' }';
			param6 = pkg.nft_ipv6_flag + ' ' + addr_dir + ' ' + negation + '{ ' + is6 + ' }';
		}
	} else {
		let is4 = '', is6 = '';
		for (let v in split(value, /\s+/)) {
			if (!v) continue;
			let clean = replace(v, /^!/, '');
			if (is_ipv4(clean)) is4 += (is4 ? ' ' : '') + v;
			else is6 += (is6 ? ' ' : '') + v;
		}
		if (!is4) empty4 = true;
		if (!is6) empty6 = true;
		param4 = pkg.nft_ipv4_flag + ' ' + addr_dir + ' ' + negation + '{ ' + inline_set(is4) + ' }';
		param6 = pkg.nft_ipv6_flag + ' ' + addr_dir + ' ' + negation + '{ ' + inline_set(is6) + ' }';
	}

	return { param4, param6, empty4, empty6 };
}

// ── DNS Policy Routing ───────────────────────────────────────────────
// Original idea by @egc112: https://github.com/egc112/OpenWRT-egc-add-on/tree/main/stop-dns-leak

pbr.dns_policy.routing = function(name, src_addr, dest_dns, uid, dest_dns_port, dest_dns_ipv4, dest_dns_ipv6) {
	let nft_insert = 'add';
	let protos = ['tcp', 'udp'];
	let chain = 'dstnat';
	let nft_table = pkg.nft_table;
	let nft_prefix = pkg.nft_prefix;

	if (!dest_dns_ipv4 && !dest_dns_ipv6) {
		pbr.process_dns_policy_error = true;
		push(pbr.errors, { code: 'errorPolicyProcessNoInterfaceDns', info: "'" + dest_dns + "'" });
		return 1;
	}

	if (!cfg.ipv6_enabled && is_ipv6(str_first_word(src_addr))) {
		pbr.process_dns_policy_error = true;
		push(pbr.errors, { code: 'errorPolicyProcessNoIpv6', info: name });
		return 1;
	}

	if ((is_ipv4(str_first_word(src_addr)) && !dest_dns_ipv4) ||
		(is_ipv6(str_first_word(src_addr)) && !dest_dns_ipv6)) {
		pbr.process_dns_policy_error = true;
		push(pbr.errors, { code: 'errorPolicyProcessMismatchFamily',
			info: name + ": '" + src_addr + "' '" + dest_dns + "':'" + dest_dns_port + "'" });
		return 1;
	}

	let clean_src = src_addr ? ((substr(src_addr, 0, 1) == '!') ? replace(src_addr, /!/g, '') : src_addr) : '';
	let first_value = str_first_word(clean_src);

	for (let proto_i in protos) {
		let param4 = '', param6 = '';
		let inline_set_ipv4_empty = false, inline_set_ipv6_empty = false;

		let dest4 = 'dport 53 dnat ip to ' + dest_dns_ipv4 + ':' + dest_dns_port;
		let dest6 = 'dport 53 dnat ip6 to ' + dest_dns_ipv6 + ':' + dest_dns_port;

		if (src_addr) {
			let r = classify_addr(src_addr, 'src', null, null, null, false);
			param4 = r.param4;
			param6 = r.param6;
			inline_set_ipv4_empty = r.empty4;
			inline_set_ipv6_empty = r.empty6;
		}

		let rule_params = pbr.nft_rule_params ? ' ' + pbr.nft_rule_params : '';
		param4 = nft_insert + ' rule inet ' + nft_table + ' ' + nft_prefix + '_' + chain +
			(param4 ? ' ' + param4 : '') + rule_params + ' meta nfproto ipv4 ' + proto_i + ' ' + dest4 +
			' comment "' + name + '"';
		param6 = nft_insert + ' rule inet ' + nft_table + ' ' + nft_prefix + '_' + chain +
			(param6 ? ' ' + param6 : '') + rule_params + ' meta nfproto ipv6 ' + proto_i + ' ' + dest6 +
			' comment "' + name + '"';

		let ipv4_error = false, ipv6_error = false;
		if (pbr.pbr_nft_prev_param4 != param4 && first_value &&
			!is_ipv6(first_value) && !inline_set_ipv4_empty && dest_dns_ipv4) {
			if (!nft4(param4)) ipv4_error = true;
			pbr.pbr_nft_prev_param4 = param4;
		}
		if (pbr.pbr_nft_prev_param6 != param6 && param4 != param6 &&
			first_value && !is_ipv4(first_value) && !inline_set_ipv6_empty && dest_dns_ipv6) {
			if (!nft6(param6)) ipv6_error = true;
			pbr.pbr_nft_prev_param6 = param6;
		}

		if (cfg.ipv6_enabled && ipv4_error && ipv6_error) {
			pbr.process_dns_policy_error = true;
			push(pbr.errors, { code: 'errorPolicyProcessInsertionFailed', info: name });
			push(pbr.errors, { code: 'errorPolicyProcessCMD', info: 'nft ' + param4 });
			push(pbr.errors, { code: 'errorPolicyProcessCMD', info: 'nft ' + param6 });
		} else if (!cfg.ipv6_enabled && ipv4_error) {
			pbr.process_dns_policy_error = true;
			push(pbr.errors, { code: 'errorPolicyProcessInsertionFailedIpv4', info: name });
			push(pbr.errors, { code: 'errorPolicyProcessCMD', info: 'nft ' + param4 });
		}
	}
};

// ── Policy Routing ──────────────────────────────────────────────────

pbr.policy.routing = function(name, iface, src_addr, src_port, dest_addr, dest_port, proto, chain, uid) {
	let nft_insert = 'add';
	let nft_table = pkg.nft_table;
	let nft_prefix = pkg.nft_prefix;
	let mark = pbr.get_mark(iface);

	proto = lc(proto || '');
	chain = lc(chain || '') || 'prerouting';

	if (!cfg.ipv6_enabled &&
		(is_ipv6(str_first_word(src_addr)) || is_ipv6(str_first_word(dest_addr)))) {
		pbr.process_policy_error = true;
		push(pbr.errors, { code: 'errorPolicyProcessNoIpv6', info: name });
		return 1;
	}

	let dest4, dest6;
	if (is_tor(iface)) {
		dest_port = null;
		proto = '';
	} else if (is_xray(iface)) {
		dest_port = null;
		if (!src_port) src_port = '0-65535';
		let xport = get_xray_traffic_port(iface);
		dest4 = 'tproxy ' + pkg.nft_ipv4_flag + ' to :' + xport + ' accept';
		dest6 = 'tproxy ' + pkg.nft_ipv6_flag + ' to :' + xport + ' accept';
	} else if (is_mwan4_strategy(iface)) {
		let strategy_data = pbr.get_interface(iface);
		let sname = strategy_data?.strategy_name;
		if (sname) {
			let schain = env.mwan4_strategy_chain[sname] || (pkg.mwan4_nft_prefix + '_strategy_' + sname);
			dest4 = 'goto ' + schain + '_ipv4';
			dest6 = 'goto ' + schain + '_ipv6';
		} else {
			pbr.process_policy_error = true;
			push(pbr.errors, { code: 'errorPolicyProcessUnknownFwmark', info: iface });
			return 1;
		}
	} else if (mark) {
		let chain_name = pbr.get_interface(iface).chain_name;
		if (index(chain_name, pkg.mwan4_nft_prefix) == 0) {
			dest4 = 'goto ' + chain_name + '_ipv4';
			dest6 = 'goto ' + chain_name + '_ipv6';
		} else {
			dest4 = 'goto ' + chain_name;
			dest6 = 'goto ' + chain_name;
		}
	} else if (iface == 'ignore') {
		dest4 = 'return';
		dest6 = 'return';
	} else {
		pbr.process_policy_error = true;
		push(pbr.errors, { code: 'errorPolicyProcessUnknownFwmark', info: iface });
		return 1;
	}

	if (!proto) {
		if (src_port || dest_port)
			proto = 'tcp udp';
		else
			proto = 'all';
	}

	let proto_list = split(proto, /\s+/);
	for (let proto_i in proto_list) {
		let param4 = '', param6 = '';
		let src_inline_set_ipv4_empty, src_inline_set_ipv6_empty;
		let dest_inline_set_ipv4_empty, dest_inline_set_ipv6_empty;

		if (proto_i == 'all') proto_i = '';

		if (proto_i && !is_supported_protocol(proto_i)) {
			pbr.process_policy_error = true;
			push(pbr.errors, { code: 'errorPolicyProcessUnknownProtocol', info: name + ": '" + proto_i + "'" });
			return 1;
		}

		// Source address
		if (src_addr) {
			let r = classify_addr(src_addr, 'src', iface, uid, name, true);
			param4 = r.param4;
			param6 = r.param6;
			src_inline_set_ipv4_empty = r.empty4;
			src_inline_set_ipv6_empty = r.empty6;
		}

		// Destination address
		if (dest_addr) {
			let r = classify_addr(dest_addr, 'dst', iface, uid, name, true);
			param4 += (param4 ? ' ' : '') + r.param4;
			param6 += (param6 ? ' ' : '') + r.param6;
			dest_inline_set_ipv4_empty = r.empty4;
			dest_inline_set_ipv6_empty = r.empty6;
		}

		// Source port
		if (src_port) {
			let negation = '', value = src_port;
			if (substr(src_port, 0, 1) == '!') {
				negation = '!= ';
				value = substr(src_port, 1);
			}
			let port_param = (proto_i ? proto_i + ' ' : '') + 'sport ' + negation + '{ ' + inline_set(value) + ' }';
			param4 += (param4 ? ' ' : '') + port_param;
			param6 += (param6 ? ' ' : '') + port_param;
		}

		// Destination port
		if (dest_port) {
			let negation = '', value = '' + dest_port;
			if (substr(value, 0, 1) == '!') {
				negation = '!= ';
				value = substr(value, 1);
			}
			let port_param = (proto_i ? proto_i + ' ' : '') + 'dport ' + negation + '{ ' + inline_set(value) + ' }';
			param4 += (param4 ? ' ' : '') + port_param;
			param6 += (param6 ? ' ' : '') + port_param;
		}

		let rule_params = pbr.nft_rule_params ? ' ' + pbr.nft_rule_params : '';

		if (is_tor(iface)) {
			let ipv4_error = false, ipv6_error = false;
			chain = 'dstnat';
			let p4_base = nft_insert + ' rule inet ' + nft_table + ' ' + nft_prefix + '_' + chain +
				rule_params + ' meta nfproto ipv4 ' + param4;
			let p6_base = nft_insert + ' rule inet ' + nft_table + ' ' + nft_prefix + '_' + chain +
				rule_params + ' meta nfproto ipv6 ' + param6;
			let tor_rules = [
				'udp dport 53 redirect to :' + env.tor_dns_port + ' comment "Tor-DNS-UDP"',
				'tcp dport 80 redirect to :' + env.tor_traffic_port + ' comment "Tor-HTTP-TCP"',
				'udp dport 80 redirect to :' + env.tor_traffic_port + ' comment "Tor-HTTP-UDP"',
				'tcp dport 443 redirect to :' + env.tor_traffic_port + ' comment "Tor-HTTPS-TCP"',
				'udp dport 443 redirect to :' + env.tor_traffic_port + ' comment "Tor-HTTPS-UDP"',
			];
			for (let dest_rule in tor_rules) {
				if (!nft4(p4_base + ' ' + dest_rule)) ipv4_error = true;
				if (!nft6(p6_base + ' ' + dest_rule)) ipv6_error = true;
				if (cfg.ipv6_enabled && ipv4_error && ipv6_error) {
					pbr.process_policy_error = true;
					push(pbr.errors, { code: 'errorPolicyProcessInsertionFailed', info: name });
				} else if (!cfg.ipv6_enabled && ipv4_error) {
					pbr.process_policy_error = true;
					push(pbr.errors, { code: 'errorPolicyProcessInsertionFailedIpv4', info: name });
				}
			}
		} else {
			param4 = nft_insert + ' rule inet ' + nft_table + ' ' + nft_prefix + '_' + chain +
				(param4 ? ' ' + param4 : '') + rule_params + ' ' + (dest4 || '') + ' comment "' + name + '"';
			param6 = nft_insert + ' rule inet ' + nft_table + ' ' + nft_prefix + '_' + chain +
				(param6 ? ' ' + param6 : '') + rule_params + ' ' + (dest6 || '') + ' comment "' + name + '"';

			let ipv4_error = false, ipv6_error = false;
			if (pbr.pbr_nft_prev_param4 != param4 &&
				!src_inline_set_ipv4_empty && !dest_inline_set_ipv4_empty) {
				if (!nft4(param4)) ipv4_error = true;
				pbr.pbr_nft_prev_param4 = param4;
			}
			if (pbr.pbr_nft_prev_param6 != param6 && param4 != param6 &&
				!src_inline_set_ipv6_empty && !dest_inline_set_ipv6_empty) {
				if (!nft6(param6)) ipv6_error = true;
				pbr.pbr_nft_prev_param6 = param6;
			}

			if (cfg.ipv6_enabled && ipv4_error && ipv6_error) {
				pbr.process_policy_error = true;
				push(pbr.errors, { code: 'errorPolicyProcessInsertionFailed', info: name });
				push(pbr.errors, { code: 'errorPolicyProcessCMD', info: 'nft ' + param4 });
				push(pbr.errors, { code: 'errorPolicyProcessCMD', info: 'nft ' + param6 });
			} else if (!cfg.ipv6_enabled && ipv4_error) {
				pbr.process_policy_error = true;
				push(pbr.errors, { code: 'errorPolicyProcessInsertionFailedIpv4', info: name });
				push(pbr.errors, { code: 'errorPolicyProcessCMD', info: 'nft ' + param4 });
			}
		}
	}
};

// ── DNS Policy Process ──────────────────────────────────────────────

pbr.dns_policy.process = function(uid, enabled, name, src_addr, dest_dns, dest_dns_port) { // ucode-lsp disable
	if (enabled != '1') return 0;

	src_addr = replace(src_addr, /[,;{};]/g, ' ');
	dest_dns = replace(dest_dns, /[,;{}]/g, ' ');

	// Process URLs in src_addr
	let j_parts = [];
	for (let i in split(src_addr || '', /\s+/)) {
		if (!i) continue;
		if (is_url(i)) i = process_url(i);
		push(j_parts, i);
	}
	src_addr = join(' ', j_parts);

	let dest_dns_interface = null, dest_dns_ipv4 = null, dest_dns_ipv6 = null;
	for (let v in split(trim('' + dest_dns), /\s+/)) {
		if (!dest_dns_interface && is_supported_interface(v)) dest_dns_interface = v;
		if (!dest_dns_ipv4 && is_ipv4(v)) dest_dns_ipv4 = v;
		if (!dest_dns_ipv6 && is_ipv6(v)) dest_dns_ipv6 = v;
	}

	if (is_supported_interface(dest_dns_interface)) {
		let dns_list = uci_ctx('network').get('network', dest_dns_interface, 'dns');
		if (type(dns_list) == 'array') {
			for (let d in dns_list) {
				if (!is_family_mismatch(src_addr, d)) {
					if (is_ipv4(d) && !dest_dns_ipv4) dest_dns_ipv4 = d;
					else if (is_ipv6(d) && !dest_dns_ipv6) dest_dns_ipv6 = d;
				}
			}
		}
	}

	pbr.process_dns_policy_error = false;
	output.verbose("Routing '" + name + "' DNS to " + dest_dns + ':' + dest_dns_port + ' ');

	if (!src_addr) {
		push(pbr.errors, { code: 'errorPolicyNoSrcDest', info: name });
		output.verbose_fail(); return 1;
	}
	if (!dest_dns) {
		push(pbr.errors, { code: 'errorPolicyNoDns', info: name });
		output.verbose_fail(); return 1;
	}

	let filter_list = 'phys_dev phys_dev_negative mac_address mac_address_negative domain domain_negative ipv4 ipv4_negative ipv6 ipv6_negative';
	for (let fg in split(filter_list, /\s+/)) {
		let filtered = filter_options(fg, src_addr);
		if (src_addr && filtered) {
			if (str_contains(fg, 'ipv4') && !dest_dns_ipv4) continue;
			if (str_contains(fg, 'ipv6') && !dest_dns_ipv6) continue;
			pbr.dns_policy.routing(name, filtered, dest_dns, uid, dest_dns_port, dest_dns_ipv4, dest_dns_ipv6);
		}
	}

	if (pbr.process_dns_policy_error) output.verbose_fail();
	else output.verbose_ok();
};

// ── Policy Process ──────────────────────────────────────────────────

pbr.policy.process = function(uid, enabled, name, interface_name, src_addr, src_port, dest_addr, dest_port, proto, chain) { // ucode-lsp disable
	if (enabled != '1') return 0;

	src_addr = replace(src_addr, /[,;{};]/g, ' ');
	src_port = replace(src_port, /[,;{}]/g, ' ');
	dest_addr = replace(dest_addr, /[,;{}]/g, ' ');
	dest_port = replace(dest_port, /[,;{}]/g, ' ');

	pbr.process_policy_error = false;
	proto = lc(proto || '');
	if (proto == 'auto' || proto == 'all') proto = '';

	output.verbose("Routing '" + name + "' via " + interface_name + ' ');

	if (!src_addr && !src_port && !dest_addr && !dest_port) {
		push(pbr.errors, { code: 'errorPolicyNoSrcDest', info: name });
		output.verbose_fail(); return 1;
	}
	if (!interface_name) {
		push(pbr.errors, { code: 'errorPolicyNoInterface', info: name });
		output.verbose_fail(); return 1;
	}
	if (!is_supported_interface(interface_name) && !is_mwan4_strategy(interface_name)) {
		push(pbr.errors, { code: 'errorPolicyUnknownInterface', info: name });
		output.verbose_fail(); return 1;
	}

	// Process URLs in src_addr
	let j_parts = [];
	for (let i in split(src_addr || '', /\s+/)) {
		if (!i) continue;
		if (is_url(i)) i = process_url(i);
		push(j_parts, i);
	}
	src_addr = join(' ', j_parts);

	// Process URLs in dest_addr
	j_parts = [];
	for (let i in split(dest_addr || '', /\s+/)) {
		if (!i) continue;
		if (is_url(i)) i = process_url(i);
		push(j_parts, i);
	}
	dest_addr = join(' ', j_parts);

	let filter_list_src = 'phys_dev phys_dev_negative mac_address mac_address_negative domain domain_negative ipv4 ipv4_negative ipv6 ipv6_negative';
	let filter_list_dest = 'domain domain_negative ipv4 ipv4_negative ipv6 ipv6_negative';
	let processed_src = '', processed_dest = '';

	if (!src_addr) filter_list_src = 'none';
	for (let fg_src in split(filter_list_src, /\s+/)) {
		let fv_src = filter_options(fg_src, src_addr);
		if (!src_addr || (src_addr && fv_src)) {
			let fl_dest = dest_addr ? filter_list_dest : 'none';
			for (let fg_dest in split(fl_dest, /\s+/)) {
				let fv_dest = filter_options(fg_dest, dest_addr);
				if (!dest_addr || (dest_addr && fv_dest)) {
					if (str_contains(fg_src, 'ipv4') && str_contains(fg_dest, 'ipv6')) continue;
					if (str_contains(fg_src, 'ipv6') && str_contains(fg_dest, 'ipv4')) continue;
					pbr.policy.routing(name, interface_name, fv_src, src_port, fv_dest, dest_port, proto, chain, uid);
					processed_src += (processed_src ? ' ' : '') + (fv_src || '');
					processed_dest += (processed_dest ? ' ' : '') + (fv_dest || '');
				}
			}
		}
	}

	for (let i in split(src_addr || '', /\s+/)) {
		if (i && !str_contains(processed_src, i)) {
			pbr.process_policy_error = true;
			push(pbr.errors, { code: 'errorPolicyProcessUnknownEntry', info: name + ': ' + i });
		}
	}
	for (let i in split(dest_addr || '', /\s+/)) {
		if (i && !str_contains(processed_dest, i)) {
			pbr.process_policy_error = true;
			push(pbr.errors, { code: 'errorPolicyProcessUnknownEntry', info: name + ': ' + i });
		}
	}

	if (pbr.process_policy_error) output.verbose_fail();
	else output.verbose_ok();
};

// ── Interface Routing ───────────────────────────────────────────────

pbr.interface.routing = function(action, tid, mark, iface, gw4, dev4, gw6, dev6, priority) {
	let s = 0, ipv4_error = 1, ipv6_error = 1;
	let nft_table = pkg.nft_table;
	let nft_prefix = pkg.nft_prefix;
	let rule_params = pbr.nft_rule_params ? ' ' + pbr.nft_rule_params : '';

	if (!tid || !mark || !iface) {
		push(pbr.errors, { code: 'errorInterfaceRoutingEmptyValues' });
		return 1;
	}

	switch (action) {
	case 'create': {
		if (is_netifd_interface(iface) || is_mwan4_interface(iface))
			return 0;
		let table_iface = iface;
		if (is_split_uplink() && iface == cfg.uplink_interface6)
			table_iface = cfg.uplink_interface4;

		// Add rt_tables entry
		let rt_content = readfile(pkg.rt_tables_file) || '';
		if (index(rt_content, tid + ' ' + pkg.ip_table_prefix + '_' + table_iface) < 0) {
			// Remove old entry if any
			let lines = split(rt_content, '\n');
			let new_lines = [];
			for (let l in lines) {
				if (index(l, pkg.ip_table_prefix + '_' + table_iface) < 0)
					push(new_lines, l);
			}
			push(new_lines, tid + ' ' + pkg.ip_table_prefix + '_' + table_iface);
			writefile(pkg.rt_tables_file, join('\n', new_lines) + '\n');
			sys('sync');
		}

		if (dev4) {
			ipv4_error = 0;
			sys(pkg.ip_full + ' -4 rule flush table ' + tid);
			sys(pkg.ip_full + ' -4 route flush table ' + tid);
			if (gw4 || cfg.strict_enforcement) {
				if (!gw4)
					ipv4_error = try_cmd(pkg.ip_full, '-4', 'route', 'replace', 'unreachable', 'default', 'table', tid) ? 0 : 1;
				else
					ipv4_error = try_cmd(pkg.ip_full, '-4', 'route', 'replace', 'default', 'via', gw4, 'dev', dev4, 'table', tid) ? 0 : 1;
				if (try_ip('-4', 'rule', 'replace', 'fwmark', mark + '/' + cfg.fw_mask, 'table', tid, 'priority', priority) != true)
					ipv4_error = 1;
			}

			let idata = pbr.get_interface(iface);
			let chain_name = idata.chain_name;

			if (!pbr._mark_chains_created?.[mark]) {
				if (!pbr._mark_chains_created) pbr._mark_chains_created = {};
				pbr._mark_chains_created[mark] = true;
				nft_add('add chain inet ' + nft_table + ' ' + chain_name);
				nft_add('add rule inet ' + nft_table + ' ' + chain_name + rule_params +
					' meta mark set (meta mark & ' + cfg.fw_maskXor + ') | ' + mark);
				nft_add('add rule inet ' + nft_table + ' ' + chain_name + ' return');
			}

			let dscp = uci_ctx(pkg.name).get(pkg.name, 'config', iface + '_dscp') || '0';
			if (+dscp >= 1 && +dscp <= 63) {
				nft_add('add rule inet ' + nft_table + ' ' + nft_prefix + '_prerouting ' +
					pkg.nft_ipv4_flag + ' dscp ' + dscp + rule_params + ' goto ' + chain_name);
			}
			if (iface == cfg.icmp_interface) {
				nft_add('add rule inet ' + nft_table + ' ' + nft_prefix + '_output ' +
					pkg.nft_ipv4_flag + ' protocol icmp' + rule_params + ' goto ' + chain_name);
			}
		}

		if (cfg.ipv6_enabled && dev6) {
			ipv6_error = 0;
			sys(pkg.ip_full + ' -6 rule flush table ' + tid);
			sys(pkg.ip_full + ' -6 route flush table ' + tid);
			if ((gw6 && gw6 != '::/0') || cfg.strict_enforcement) {
				if (!gw6 || gw6 == '::/0')
					ipv6_error = try_cmd(pkg.ip_full, '-6', 'route', 'replace', 'unreachable', 'default', 'table', tid) ? 0 : 1;
				else {
					let route_check = shell(pkg.ip_full + ' -6 route list table main');
					if (index(route_check, ' dev ' + dev6 + ' ') >= 0) {
						let addr_info = shell(pkg.ip_full + ' -6 address show dev ' + dev6);
						if (index(addr_info, 'BROADCAST') >= 0)
							ipv6_error = try_cmd(pkg.ip_full, '-6', 'route', 'replace', 'default', 'via', gw6, 'dev', dev6, 'table', tid) ? 0 : 1;
						else if (index(addr_info, 'POINTOPOINT') >= 0)
							ipv6_error = try_cmd(pkg.ip_full, '-6', 'route', 'replace', 'default', 'dev', dev6, 'table', tid) ? 0 : 1;
						else
							push(pbr.errors, { code: 'errorInterfaceRoutingUnknownDevType', info: dev6 });
					} else {
						let dev6_out = shell(pkg.ip_full + ' -6 -o a show ' + shell_quote(dev6));
						let dev6_m = match(dev6_out, /\s+inet6\s+(\S+)/);
						let dev6_addr = dev6_m ? dev6_m[1] : null;
						if (dev6_addr)
							try_cmd(pkg.ip_full, '-6', 'route', 'replace', dev6_addr, 'dev', dev6, 'table', tid);
						ipv6_error = try_cmd(pkg.ip_full, '-6', 'route', 'replace', 'default', 'dev', dev6, 'table', tid) ? 0 : 1;
					}
				}
				if (try_ip('-6', 'rule', 'replace', 'fwmark', mark + '/' + cfg.fw_mask, 'table', tid, 'priority', priority) != true)
					ipv6_error = 1;
			}

			let idata6 = pbr.get_interface(iface);
			let chain_name6 = idata6.chain_name;

			if (!pbr._mark_chains_created?.[mark]) {
				if (!pbr._mark_chains_created) pbr._mark_chains_created = {};
				pbr._mark_chains_created[mark] = true;
				nft_add('add chain inet ' + nft_table + ' ' + chain_name6);
				nft_add('add rule inet ' + nft_table + ' ' + chain_name6 + rule_params +
					' meta mark set (meta mark & ' + cfg.fw_maskXor + ') | ' + mark);
				nft_add('add rule inet ' + nft_table + ' ' + chain_name6 + ' return');
			}

			let dscp = uci_ctx(pkg.name).get(pkg.name, 'config', iface + '_dscp') || '0';
			if (+dscp >= 1 && +dscp <= 63) {
				nft_add('add rule inet ' + nft_table + ' ' + nft_prefix + '_prerouting ' +
					pkg.nft_ipv6_flag + ' dscp ' + dscp + rule_params + ' goto ' + chain_name6);
			}
			if (iface == cfg.icmp_interface) {
				nft_add('add rule inet ' + nft_table + ' ' + nft_prefix + '_output ' +
					pkg.nft_ipv6_flag + ' protocol icmp' + rule_params + ' goto ' + chain_name6);
			}
		}

		return (ipv4_error == 0 || ipv6_error == 0) ? 0 : 1;
	}
	case 'create_user_set':
		pbr.nftset('create_user_set', iface, 'dst', 'ip', 'user', '', mark) || (s = 1);
		pbr.nftset('create_user_set', iface, 'src', 'ip', 'user', '', mark) || (s = 1);
		pbr.nftset('create_user_set', iface, 'src', 'mac', 'user', '', mark) || (s = 1);
		return s;

	case 'delete':
	case 'destroy': {
		if (is_netifd_interface(iface) || is_mwan4_interface(iface)) return 0;
		sys(pkg.ip_full + ' -4 rule del table main prio ' + (+priority - 1000));
		sys(pkg.ip_full + ' -4 rule del table ' + tid + ' prio ' + priority);
		sys(pkg.ip_full + ' -6 rule del table main prio ' + (+priority - 1000));
		sys(pkg.ip_full + ' -6 rule del table ' + tid + ' prio ' + priority);
		sys(pkg.ip_full + ' -4 rule flush table ' + tid);
		sys(pkg.ip_full + ' -4 route flush table ' + tid);
		sys(pkg.ip_full + ' -6 rule flush table ' + tid);
		sys(pkg.ip_full + ' -6 route flush table ' + tid);
		let table_iface = iface;
		if (is_split_uplink() && iface == cfg.uplink_interface6)
			table_iface = cfg.uplink_interface4;
		// Remove from rt_tables
		let rt = readfile(pkg.rt_tables_file) || '';
		let lines = split(rt, '\n');
		let new_lines = [];
		for (let l in lines) {
			if (index(l, pkg.ip_table_prefix + '_' + table_iface) < 0)
				push(new_lines, l);
		}
		writefile(pkg.rt_tables_file, join('\n', new_lines) + '\n');
		sys('sync');
		return 0;
	}
	case 'reload_interface': {
		if (is_netifd_interface(iface) || is_mwan4_interface(iface)) return 0;
		if (dev4) {
			ipv4_error = 0;
			sys(pkg.ip_full + ' -4 rule flush fwmark ' + shell_quote(mark + '/' + cfg.fw_mask) + ' table ' + tid);
			ip('-4', 'route', 'flush', 'table', tid);
			if (gw4 || cfg.strict_enforcement) {
				if (!gw4)
					ipv4_error = try_cmd(pkg.ip_full, '-4', 'route', 'replace', 'unreachable', 'default', 'table', tid) ? 0 : 1;
				else
					ipv4_error = try_cmd(pkg.ip_full, '-4', 'route', 'replace', 'default', 'via', gw4, 'dev', dev4, 'table', tid) ? 0 : 1;
				if (try_ip('-4', 'rule', 'replace', 'fwmark', mark + '/' + cfg.fw_mask, 'table', tid, 'priority', priority) != true)
					ipv4_error = 1;
			}
		}
		if (cfg.ipv6_enabled && dev6) {
			ipv6_error = 0;
			sys(pkg.ip_full + ' -6 rule flush fwmark ' + shell_quote(mark + '/' + cfg.fw_mask) + ' table ' + tid);
			ip('-6', 'route', 'flush', 'table', tid);
			if ((gw6 && gw6 != '::/0') || cfg.strict_enforcement) {
				if (!gw6 || gw6 == '::/0')
					ipv6_error = try_cmd(pkg.ip_full, '-6', 'route', 'replace', 'unreachable', 'default', 'table', tid) ? 0 : 1;
				else {
					let route_check = shell(pkg.ip_full + ' -6 route list table main');
					if (index(route_check, ' dev ' + dev6 + ' ') >= 0) {
						let addr_info = shell(pkg.ip_full + ' -6 address show dev ' + dev6);
						if (index(addr_info, 'BROADCAST') >= 0)
							ipv6_error = try_cmd(pkg.ip_full, '-6', 'route', 'replace', 'default', 'via', gw6, 'dev', dev6, 'table', tid) ? 0 : 1;
						else if (index(addr_info, 'POINTOPOINT') >= 0)
							ipv6_error = try_cmd(pkg.ip_full, '-6', 'route', 'replace', 'default', 'dev', dev6, 'table', tid) ? 0 : 1;
						else
							push(pbr.errors, { code: 'errorInterfaceRoutingUnknownDevType', info: dev6 });
					} else {
						let dev6_out = shell(pkg.ip_full + ' -6 -o a show ' + shell_quote(dev6));
						let dev6_m = match(dev6_out, /\s+inet6\s+(\S+)/);
						let dev6_addr = dev6_m ? dev6_m[1] : null;
						if (dev6_addr)
							try_cmd(pkg.ip_full, '-6', 'route', 'replace', dev6_addr, 'dev', dev6, 'table', tid);
						ipv6_error = try_cmd(pkg.ip_full, '-6', 'route', 'replace', 'default', 'dev', dev6, 'table', tid) ? 0 : 1;
					}
				}
				if (try_ip('-6', 'rule', 'replace', 'fwmark', mark + '/' + cfg.fw_mask, 'table', tid, 'priority', priority) != true)
					ipv6_error = 1;
			}
		}
		return (ipv4_error == 0 || ipv6_error == 0) ? 0 : 1;
	}
	}
	return s;
};

// ── Enumerate Interfaces ────────────────────────────────────────────
// Single pass: assigns mark/priority/device to each supported interface.
// Must run after env.load_config() and env.load().

pbr.interface.enumerate = function() {
	uci_ctx('network', true);

	let iface_mark = sprintf('0x%06x', hex(cfg.uplink_mark));
	let iface_priority = cfg.uplink_ip_rules_priority;
	let _uplink_mark = '';
	let _uplink_priority = '';

	pbr.ifaces_triggers = '';

	uci_ctx('network').foreach('network', 'interface', function(s) {
		let iface = s['.name'];

		if (!is_supported_interface(iface)) return;
		if (hex(iface_mark) > hex(cfg.fw_mask)) {
			push(pbr.errors, { code: 'errorInterfaceMarkOverflow', info: iface });
			return;
		}

		let dev4 = network_get_device(iface);
		if (!dev4) dev4 = network_get_physdev(iface);
		let dev6 = null;
		if (is_uplink4(iface) && cfg.uplink_interface6) {
			dev6 = network_get_device(cfg.uplink_interface6);
			if (!dev6) dev6 = network_get_physdev(cfg.uplink_interface6);
		}
		if (!dev6) dev6 = dev4;

		let _mark = iface_mark;
		let _chain_name = pkg.nft_prefix + '_mark_' + _mark;
		let _priority = iface_priority;
		let split_uplink_second = false;

		if (is_netifd_interface(iface) && env.netifd_mark[iface]) {
			_mark = env.netifd_mark[iface];
			_chain_name = pkg.nft_prefix + '_mark_' + _mark;
		} else if (is_mwan4_interface(iface) && env.mwan4_mark[iface]) {
			_mark = env.mwan4_mark[iface];
			_chain_name = env.mwan4_interface_chain[iface];
		} else if (is_split_uplink()) {
			if (is_uplink4(iface) || is_uplink6(iface)) {
				if (_uplink_mark && _uplink_priority) {
					_mark = _uplink_mark;
					_priority = _uplink_priority;
					split_uplink_second = true;
				} else {
					_uplink_mark = iface_mark;
					_uplink_priority = iface_priority;
				}
			}
		}

		pbr.set_interface(iface, {
			mark: _mark, priority: _priority,
			chain_name: _chain_name,
			device_ipv4: dev4 || '', device_ipv6: dev6 || '',
			gateway_ipv4: '', gateway_ipv6: '',
			is_default: false,
		});

		if (!is_netifd_interface(iface) && !is_mwan4_interface(iface))
			pbr.ifaces_triggers += (pbr.ifaces_triggers ? ' ' : '') + iface;

		if (!split_uplink_second) {
			iface_mark = sprintf('0x%06x', hex(iface_mark) + hex(cfg.uplink_mark));
			iface_priority = '' + (+iface_priority - 1);
		}
	});

	// Store post-enumeration priority for create_global_rules
	pbr.iface_priority = iface_priority;
};

// ── Resolve TID ─────────────────────────────────────────────────────
// Looks up existing rt_tables entry, falls back to split-uplink partner,
// then to next available ID.

pbr.interface.resolve_tid = function(iface) {
	let tid = get_rt_tables_id(iface);
	if (!tid && is_split_uplink() && (is_uplink4(iface) || is_uplink6(iface))) {
		let other = is_uplink4(iface) ? cfg.uplink_interface6 : cfg.uplink_interface4;
		let other_data = pbr.get_interface(other);
		if (other_data?.tid) tid = other_data.tid;
	}
	if (!tid) tid = get_rt_tables_next_id();
	return tid;
};

// ── Process Interface ───────────────────────────────────────────────
// Performs actions on interfaces using pre-computed properties from
// pbr.interface.enumerate(). TIDs are resolved lazily per action.

pbr.interface.process = function(iface, action, reloaded_iface) {
	let _get_tor_dns_port = function() {
		let content = readfile(pkg.tor_config_file);
		if (type(content) != 'string' || !content) return '9053';
		let m = match(content, /DNSPort\s+\S+:(\d+)/);
		return m ? m[1] : '9053';
	};

	let _get_tor_traffic_port = function() {
		let content = readfile(pkg.tor_config_file);
		if (type(content) != 'string' || !content) return '9040';
		let m = match(content, /TransPort\s+\S+:(\d+)/);
		return m ? m[1] : '9040';
	};

	let s = 0;
	let nft_prefix = pkg.nft_prefix;

	if (iface == 'all') {
		if (action == 'create_global_rules') {
			// WireGuard server sport rules (del may fail on first run — suppress stderr)
			uci_ctx('network').foreach('network', 'interface', function(s_iface) {
				let name = s_iface['.name'];
				if (is_wg_server(name) && !is_ignored_interface(name)) {
					let disabled = uci_ctx('network').get('network', name, 'disabled');
					let listen_port = uci_ctx('network').get('network', name, 'listen_port');
					if (disabled != '1' && listen_port) {
						if (cfg.uplink_interface4) {
							let tbl = pkg.ip_table_prefix + '_' + cfg.uplink_interface4;
							let prio = '' + pbr.iface_priority;
							system(pkg.ip_full + ' -4 rule del sport ' + listen_port + ' table ' + tbl + ' priority ' + prio + ' 2>/dev/null');
							ip('-4', 'rule', 'add', 'sport', listen_port, 'table', tbl, 'priority', prio);
							if (cfg.ipv6_enabled) {
								system(pkg.ip_full + ' -6 rule del sport ' + listen_port + ' table ' + tbl + ' priority ' + prio + ' 2>/dev/null');
								ip('-6', 'rule', 'add', 'sport', listen_port, 'table', tbl, 'priority', prio);
							}
						}
					}
				}
			});
			// suppress_prefixlength rules (del may fail on first run — suppress stderr)
			let spl_prio = '' + (int(cfg.uplink_ip_rules_priority) + 1);
			system(pkg.ip_full + ' -4 rule del priority ' + spl_prio + ' 2>/dev/null');
			system(pkg.ip_full + ' -4 rule del lookup main suppress_prefixlength ' + cfg.prefixlength + ' 2>/dev/null');
			try_cmd(pkg.ip_full, '-4', 'rule', 'add', 'lookup', 'main', 'suppress_prefixlength',
				'' + cfg.prefixlength, 'pref', spl_prio);
			if (cfg.ipv6_enabled) {
				system(pkg.ip_full + ' -6 rule del priority ' + spl_prio + ' 2>/dev/null');
				system(pkg.ip_full + ' -6 rule del lookup main suppress_prefixlength ' + cfg.prefixlength + ' 2>/dev/null');
				try_cmd(pkg.ip_full, '-6', 'rule', 'add', 'lookup', 'main', 'suppress_prefixlength',
					'' + cfg.prefixlength, 'pref', spl_prio);
			}
		}
		return 0;
	}

	if (iface == 'tor') {
		switch (action) {
		case 'create': case 'reload': case 'reload_interface':
			env.tor_dns_port = _get_tor_dns_port();
			env.tor_traffic_port = _get_tor_traffic_port();
			pbr.set_interface('tor', {
				device_ipv4: '', device_ipv6: '',
				gateway_ipv4: '53->' + env.tor_dns_port,
				gateway_ipv6: '80,443->' + env.tor_traffic_port,
				is_default: false, action: action,
			});
			break;
		}
		return 0;
	}

	// WG server destroy: clean up sport rules even for non-supported servers
	if (action == 'destroy' && is_wg_server(iface) && !is_ignored_interface(iface)) {
		let lp = uci_ctx('network').get('network', iface, 'listen_port');
		if (lp) {
			ip('-4', 'rule', 'del', 'sport', lp, 'table', 'pbr_' + cfg.uplink_interface4);
			ip('-6', 'rule', 'del', 'sport', lp, 'table', 'pbr_' + cfg.uplink_interface4);
		}
	}

	// Look up pre-computed properties from pbr.interface.enumerate()
	let existing = pbr.get_interface(iface);
	if (!existing) return 0;

	let _mark = existing.mark;
	let _priority = existing.priority;
	let dev4 = existing.device_ipv4;
	let dev6 = existing.device_ipv6;
	let gw4, gw6, disp_dev, disp_status, display_text;

	switch (action) {
	case 'create': {
		let _tid = pbr.interface.resolve_tid(iface);
		gw4 = pbr.get_gateway4(iface, dev4);
		gw6 = pbr.get_gateway6(iface, dev6);
		if (is_split_uplink()) {
			if (is_uplink4(iface)) { gw6 = ''; dev6 = ''; }
			else if (is_uplink6(iface)) { gw4 = ''; dev4 = ''; }
		}
		let dg4 = gw4 || '0.0.0.0';
		let dg6 = gw6 || '::/0';
		disp_dev = (iface != dev4) ? dev4 : '';
		disp_status = '';
		if (is_default_dev(dev4))
			disp_status = (cfg.verbosity == '1') ? sym.ok[0] : sym.ok[1];
		if (is_netifd_interface_default(iface))
			disp_status = (cfg.verbosity == '1') ? sym.okb[0] : sym.okb[1];
		display_text = iface + '/' + (disp_dev ? disp_dev + '/' : '') + dg4 + (cfg.ipv6_enabled ? '/' + dg6 : '');
		output.verbose("Setting up routing for '" + display_text + "' ");
		if (pbr.interface.routing('create', _tid, _mark, iface, gw4, dev4, gw6, dev6, _priority) == 0) {
			pbr.set_interface(iface, {
				tid: _tid, mark: _mark, priority: _priority,
				chain_name: existing.chain_name,
				device_ipv4: dev4 || '', device_ipv6: dev6 || '',
				gateway_ipv4: gw4 || '', gateway_ipv6: gw6 || '',
				is_default: disp_status ? true : false,
				status_symbol: disp_status, action: 'create',
			});
			if (is_netifd_interface(iface)) output.verbose_okb();
			else output.verbose_ok();
		} else {
			push(pbr.errors, { code: 'errorFailedSetup', info: display_text });
			output.verbose_fail();
		}
		break;
	}

	case 'create_user_set': {
		let _tid = pbr.interface.resolve_tid(iface);
		if (is_split_uplink()) {
			if (is_uplink4(iface)) dev6 = '';
			else if (is_uplink6(iface)) dev4 = '';
		}
		pbr.interface.routing('create_user_set', _tid, _mark, iface, '', dev4, '', dev6, _priority);
		break;
	}

	case 'destroy': {
		let _tid = pbr.interface.resolve_tid(iface);
		if (is_split_uplink()) {
			if (is_uplink4(iface)) dev6 = '';
			else if (is_uplink6(iface)) dev4 = '';
		}
		disp_dev = (iface != dev4) ? dev4 : '';
		display_text = iface + '/' + (disp_dev ? disp_dev : '');
		output.verbose("Removing routing for '" + display_text + "' ");
		pbr.interface.routing('destroy', _tid, _mark, iface, '', dev4, '', dev6, _priority);
		if (is_netifd_interface(iface)) output.verbose_okb();
		else output.verbose_ok();
		break;
	}

	case 'reload': {
		let _tid = pbr.interface.resolve_tid(iface);
		gw4 = pbr.get_gateway4(iface, dev4);
		gw6 = pbr.get_gateway6(iface, dev6);
		if (is_split_uplink()) {
			if (is_uplink4(iface)) { gw6 = ''; dev6 = ''; }
			else if (is_uplink6(iface)) { gw4 = ''; dev4 = ''; }
		}
		disp_dev = (iface != dev4) ? dev4 : '';
		disp_status = '';
		if (is_default_dev(dev4))
			disp_status = (cfg.verbosity == '1') ? sym.ok[0] : sym.ok[1];
		if (is_netifd_interface_default(iface))
			disp_status = (cfg.verbosity == '1') ? sym.okb[0] : sym.okb[1];
		pbr.set_interface(iface, {
			tid: _tid, mark: _mark, priority: _priority,
			chain_name: existing.chain_name,
			device_ipv4: dev4 || '', device_ipv6: dev6 || '',
			gateway_ipv4: gw4 || '', gateway_ipv6: gw6 || '',
			is_default: disp_status ? true : false,
			status_symbol: disp_status, action: 'reload',
		});
		break;
	}

	case 'reload_interface': {
		let _tid = pbr.interface.resolve_tid(iface);
		gw4 = pbr.get_gateway4(iface, dev4);
		gw6 = pbr.get_gateway6(iface, dev6);
		if (is_split_uplink()) {
			if (is_uplink4(iface)) { gw6 = ''; dev6 = ''; }
			else if (is_uplink6(iface)) { gw4 = ''; dev4 = ''; }
		}
		disp_dev = (iface != dev4) ? dev4 : '';
		disp_status = '';
		if (is_default_dev(dev4))
			disp_status = (cfg.verbosity == '1') ? sym.ok[0] : sym.ok[1];
		if (is_netifd_interface_default(iface))
			disp_status = (cfg.verbosity == '1') ? sym.okb[0] : sym.okb[1];
		if (iface == reloaded_iface) {
			let ri_text = iface + '/' + (disp_dev ? disp_dev + '/' : '') + (gw4 || '0.0.0.0') + (cfg.ipv6_enabled ? '/' + (gw6 || '::/0') : '');
			output.verbose("Reloading routing for '" + ri_text + "' ");
			if (pbr.interface.routing('reload_interface', _tid, _mark, iface, gw4, dev4, gw6, dev6, _priority) == 0) {
				pbr.set_interface(iface, {
					tid: _tid, mark: _mark, priority: _priority,
					chain_name: existing.chain_name,
					device_ipv4: dev4 || '', device_ipv6: dev6 || '',
					gateway_ipv4: gw4 || '', gateway_ipv6: gw6 || '',
					is_default: disp_status ? true : false,
					status_symbol: disp_status, action: 'reload_interface',
				});
				if (is_netifd_interface(iface)) output.verbose_okb();
				else output.verbose_ok();
			} else {
				push(pbr.errors, { code: 'errorFailedReload', info: ri_text });
				output.verbose_fail();
			}
		} else {
			pbr.set_interface(iface, {
				tid: _tid, mark: _mark, priority: _priority,
				chain_name: existing.chain_name,
				device_ipv4: dev4 || '', device_ipv6: dev6 || '',
				gateway_ipv4: gw4 || '', gateway_ipv6: gw6 || '',
				is_default: disp_status ? true : false,
				status_symbol: disp_status, action: 'skip_interface',
			});
		}
		break;
	}
	}

	return s;
};

// ── User File Process ───────────────────────────────────────────────

pbr.user_file.process = function(enabled, path) {
	let _is_bad_user_file_nft_call = function(filepath) {
		let content = readfile(filepath) || '';
		return index(content, '"$nft" list') >= 0 || index(content, '"$nft" -f') >= 0;
	};

	let _user_file_process_sh = function(path) {
		if (sys('/bin/sh -n ' + shell_quote(path)) != 0) {
			push(pbr.errors, { code: 'errorUserFileSyntax', info: path });
			output.info_fail();
			return 1;
		}
		if (_is_bad_user_file_nft_call(path)) {
			push(pbr.errors, { code: 'errorIncompatibleUserFile', info: path });
			output.info_fail();
			return 1;
		}
		output.verbose('Running ' + path + ' ');
		// Create wrapper that captures nft commands into the accumulator
		let nft_capture = '/var/run/pbr.nft.user';
		let wrapper_path = '/var/run/pbr.user_wrapper.sh';
		unlink(nft_capture);
		writefile(wrapper_path,
			'nft() { printf "%s\\n" "$*" >> ' + shell_quote(nft_capture) + '; }\n' +
			'. ' + shell_quote(path) + '\n');
		let rc = sys('. ' + shell_quote(wrapper_path));
		// Read captured nft commands and add to accumulator
		let captured = readfile(nft_capture) || '';
		for (let line in split(captured, '\n')) {
			if (line) push(pbr.nft_lines, line);
		}
		unlink(nft_capture);
		unlink(wrapper_path);
		if (rc != 0) {
			push(pbr.errors, { code: 'errorUserFileRunning', info: path });
			let content = readfile(path) || '';
			if (index(content, 'curl') >= 0 && !is_present('curl'))
				push(pbr.errors, { code: 'errorUserFileNoCurl', info: path });
			output.verbose_fail();
			return 1;
		}
		output.verbose_ok();
		return 0;
	};

	let _user_file_process_uc = function(path) {
		output.verbose('Running ' + path + ' ');
		// Provide an API object for ucode user scripts
		let _unsafe = false;
		let _pending = [];
		let _nft_validate = function(rule_line) {
			if (!rule_line) return false;
			if (!match(rule_line, /^(add|insert|create)\s/)) {
				_unsafe = true;
				return false;
			}
			return true;
		};
		let api = {
			compat: +pkg.compat,
			table: 'inet ' + pkg.nft_table,
			nft: function(rule_line) {
				if (_nft_validate(rule_line))
					push(_pending, rule_line);
			},
			nft4: function(rule_line) {
				if (_nft_validate(rule_line))
					push(_pending, rule_line);
			},
			nft6: function(rule_line) {
				if (cfg.ipv6_enabled && _nft_validate(rule_line))
					push(_pending, rule_line);
			},
			download: function(url) {
				let dl = env.get_downloader();
				let tmp = shell('mktemp -q -t ' + shell_quote(pkg.name + '_user.XXXXXXXX'));
				if (!tmp || !stat(tmp)) return null;
				let rc = sys(dl.command + ' ' + shell_quote(url) + ' ' + dl.flag + ' ' + shell_quote(tmp));
				if (rc != 0) { unlink(tmp); return null; }
				let content = readfile(tmp) || '';
				unlink(tmp);
				return content || null;
			},
			marking_chain: function(iface) {
				let data = pbr.get_interface(iface);
				return data?.chain_name || null;
			},
			strategy_chain: function(strategy) {
				return env.mwan4_strategy_chain[strategy] || null;
			},
			nftset: function(iface, family) {
				return pbr.get_set_name(iface, family, 'dst', 'ip', 'user');
			},
		};
		let code = readfile(path);
		if (!code) {
			push(pbr.errors, { code: 'errorUserFileRunning', info: path });
			output.verbose_fail();
			return 1;
		}
		let fn = loadstring('' + code);
		if (!fn) {
			push(pbr.errors, { code: 'errorUserFileSyntax', info: path });
			output.verbose_fail();
			return 1;
		}
		let result;
		try { result = fn(); } catch (e) {
			push(pbr.errors, { code: 'errorUserFileRunning', info: path + ': ' + e });
			output.verbose_fail();
			return 1;
		}
		// Convention: the script returns a function or an object with run()
		try {
			if (type(result) == 'function')
				result(api);
			else if (type(result) == 'object' && type(result?.run) == 'function')
				result.run(api);
		} catch (e) {
			push(pbr.errors, { code: 'errorUserFileRunning', info: path + ': ' + e });
			output.verbose_fail();
			return 1;
		}
		if (_unsafe) {
			push(pbr.errors, { code: 'errorUserFileUnsafeNft', info: path });
			output.verbose_fail();
			return 1;
		}
		for (let line in _pending)
			push(pbr.nft_lines, line);
		output.verbose_ok();
		return 0;
	};

	if (enabled != '1' && enabled != 1) return 0;
	if (!stat(path) || stat(path).size == 0) {
		push(pbr.errors, { code: 'errorUserFileNotFound', info: path });
		output.info_fail();
		return 1;
	}
	if (match(path, /\.uc$/))
		return _user_file_process_uc(path);
	else
		return _user_file_process_sh(path);
};

// ── Netifd Integration ──────────────────────────────────────────────

pbr.netifd = function(action, target_iface) {
	env.load('netifd');
	pbr.reset();
	action = action || 'install';

	if (action == 'check')
		return cfg.netifd_enabled == '1';

	if (action == 'install') {
		if (!cfg.netifd_strict_enforcement) {
			push(pbr.errors, { code: 'errorNetifdMissingOption', info: 'netifd_strict_enforcement' });
			output.error(get_text('errorNetifdMissingOption', 'netifd_strict_enforcement'));
			return false;
		}
		if (!cfg.netifd_interface_default) {
			push(pbr.errors, { code: 'errorNetifdMissingOption', info: 'netifd_interface_default' });
			output.error(get_text('errorNetifdMissingOption', 'netifd_interface_default'));
			return false;
		}
		let net_ctx = uci_ctx('network', true);
		if (net_ctx.get('network', cfg.netifd_interface_default, '.type') != 'interface') {
			push(pbr.errors, { code: 'errorNetifdInvalidGateway4', info: cfg.netifd_interface_default });
			output.error(get_text('errorNetifdInvalidGateway4', cfg.netifd_interface_default));
			return false;
		}
		if (cfg.netifd_interface_default6 && net_ctx.get('network', cfg.netifd_interface_default6, '.type') != 'interface') {
			push(pbr.errors, { code: 'errorNetifdInvalidGateway6', info: cfg.netifd_interface_default6 });
			output.error(get_text('errorNetifdInvalidGateway6', cfg.netifd_interface_default6));
			return false;
		}
		if (!cfg.netifd_interface_local) {
			push(pbr.warnings, { code: 'warningNetifdMissingInterfaceLocal', info: 'lan' });
			output.warning(get_text('warningNetifdMissingInterfaceLocal', 'lan'));
			cfg.netifd_interface_local = 'lan';
		}
	}

	let mark = sprintf('0x%06x', hex(cfg.uplink_mark));
	let priority = cfg.uplink_ip_rules_priority;
	let tid = get_rt_tables_non_pbr_next_id();
	let lan_priority = int(cfg.uplink_ip_rules_priority) + 1000;
	let _uplinkMark, _uplinkPriority, _uplinkTableID;
	let nft_table = pkg.nft_table;
	let nft_prefix = pkg.nft_prefix;
	let rule_params = pbr.nft_rule_params ? ' ' + pbr.nft_rule_params : '';

	pbr.nft_file.init('netifd');
	output.info('Netifd extensions ' + action + (target_iface ? ' on ' + target_iface : '') + ' ');

	// Remove existing rules
	let net_ctx = uci_ctx('network', true);
	net_ctx.delete('network', 'main_ipv4');
	net_ctx.delete('network', 'main_ipv6');

	// Process each interface
	net_ctx.foreach('network', 'interface', function(s) {
		let iface = s['.name'];
		let rt_name = pkg.ip_table_prefix + '_' + iface;
		if (is_split_uplink() && iface == cfg.uplink_interface6)
			rt_name = pkg.ip_table_prefix + '_' + cfg.uplink_interface4;

		// Clean up existing entries
		net_ctx.delete('network', iface, 'ip4table');
		net_ctx.delete('network', iface, 'ip6table');
		net_ctx.delete('network', rt_name + '_ipv4');
		net_ctx.delete('network', rt_name + '_ipv6');

		// LAN rules for strict enforcement
		if (cfg.netifd_strict_enforcement == '1' && str_contains(cfg.netifd_interface_local, iface)) {
			if (action == 'install') {
				if (cfg.netifd_interface_default) {
					let rule_name = rt_name + '_ipv4';
					net_ctx.add('network', 'rule', rule_name);
					net_ctx.set('network', rule_name, 'in', iface);
					net_ctx.set('network', rule_name, 'lookup', pkg.ip_table_prefix + '_' + cfg.netifd_interface_default);
					net_ctx.set('network', rule_name, 'priority', '' + lan_priority);
				}
				if (cfg.ipv6_enabled && cfg.netifd_interface_default6) {
					let ipv6_lookup = pkg.ip_table_prefix + '_' + cfg.netifd_interface_default6;
					if (is_split_uplink() && cfg.netifd_interface_default6 == cfg.uplink_interface6)
						ipv6_lookup = pkg.ip_table_prefix + '_' + cfg.uplink_interface4;
					let rule6_name = rt_name + '_ipv6';
					net_ctx.add('network', 'rule6', rule6_name);
					net_ctx.set('network', rule6_name, 'in', iface);
					net_ctx.set('network', rule6_name, 'lookup', ipv6_lookup);
					net_ctx.set('network', rule6_name, 'priority', '' + lan_priority);
				}
				lan_priority++;
			}
		}

		// Process supported interfaces
		if (!is_supported_interface(iface)) return;

		let _mark = mark, _priority = priority, _tid = tid;
		let split_second = false;

		if (is_split_uplink()) {
			if (is_uplink4(iface) || is_uplink6(iface)) {
				if (_uplinkMark && _uplinkPriority && _uplinkTableID) {
					_mark = _uplinkMark;
					_priority = _uplinkPriority;
					_tid = _uplinkTableID;
					split_second = true;
				} else {
					_uplinkMark = _mark;
					_uplinkPriority = _priority;
					_uplinkTableID = _tid;
				}
			}
		}

		if (!cfg.netifd_strict_enforcement && cfg.netifd_interface_default == iface)
			rt_name = 'main';

		if (!target_iface || target_iface == iface) {
			if (action == 'install') {
				output.verbose('Setting up netifd extensions for ' + iface + '... ');
				if (!is_split_uplink() || !is_uplink6(iface)) {
					net_ctx.set('network', iface, 'ip4table', rt_name);
					let rule4 = rt_name + '_ipv4';
					net_ctx.add('network', 'rule', rule4);
					net_ctx.set('network', rule4, 'priority', '' + _priority);
					net_ctx.set('network', rule4, 'lookup', rt_name);
					net_ctx.set('network', rule4, 'mark', _mark);
					net_ctx.set('network', rule4, 'mask', cfg.fw_mask);
				}
				if (cfg.ipv6_enabled && (!is_split_uplink() || !is_uplink4(iface))) {
					net_ctx.set('network', iface, 'ip6table', rt_name);
					let rule6 = rt_name + '_ipv6';
					net_ctx.add('network', 'rule6', rule6);
					net_ctx.set('network', rule6, 'priority', '' + _priority);
					net_ctx.set('network', rule6, 'lookup', rt_name);
					net_ctx.set('network', rule6, 'mark', _mark);
					net_ctx.set('network', rule6, 'mask', cfg.fw_mask);
				}
				// rt_tables entry
				if (!is_split_uplink() || !is_uplink6(iface)) {
					if (rt_name != 'main') {
						let rt = readfile(pkg.rt_tables_file) || '';
						let lines = filter(split(rt, '\n'), l => index(l, rt_name) < 0);
						push(lines, _tid + ' ' + rt_name);
						writefile(pkg.rt_tables_file, join('\n', lines) + '\n');
					}
					pbr.nft_file.filter('temp', _mark);
				}
				if (!pbr.nft_file.match('temp', nft_prefix + '_mark_' + _mark)) {
					nft_add('define ' + nft_prefix + '_' + iface + '_mark = ' + _mark);
					nft_add('add chain inet ' + nft_table + ' ' + nft_prefix + '_mark_' + _mark);
					nft_add('add rule inet ' + nft_table + ' ' + nft_prefix + '_mark_' + _mark + rule_params +
						' meta mark set (meta mark & ' + cfg.fw_maskXor + ') | $' + nft_prefix + '_' + iface + '_mark');
					nft_add('add rule inet ' + nft_table + ' ' + nft_prefix + '_mark_' + _mark + ' return');
				}
				let dscp = uci_ctx(pkg.name).get(pkg.name, 'config', iface + '_dscp') || '0';
				if (+dscp >= 1 && +dscp <= 63) {
					if (!is_split_uplink() || !is_uplink6(iface))
						nft_add('add rule inet ' + nft_table + ' ' + nft_prefix + '_prerouting ' +
							pkg.nft_ipv4_flag + ' dscp ' + dscp + rule_params + ' goto ' + nft_prefix + '_mark_' + _mark);
					if (cfg.ipv6_enabled && (!is_split_uplink() || !is_uplink4(iface)))
						nft_add('add rule inet ' + nft_table + ' ' + nft_prefix + '_prerouting ' +
							pkg.nft_ipv6_flag + ' dscp ' + dscp + rule_params + ' goto ' + nft_prefix + '_mark_' + _mark);
				}
				if (iface == cfg.icmp_interface) {
					if (!is_split_uplink() || !is_uplink6(iface))
						nft_add('add rule inet ' + nft_table + ' ' + nft_prefix + '_output ' +
							pkg.nft_ipv4_flag + ' protocol icmp' + rule_params + ' goto ' + nft_prefix + '_mark_' + _mark);
					if (cfg.ipv6_enabled && (!is_split_uplink() || !is_uplink4(iface)))
						nft_add('add rule inet ' + nft_table + ' ' + nft_prefix + '_output ' +
							pkg.nft_ipv6_flag + ' protocol icmp' + rule_params + ' goto ' + nft_prefix + '_mark_' + _mark);
				}
				output.verbose_okb();
			} else if (action == 'remove' || action == 'uninstall') {
				output.verbose('Removing netifd extensions for ' + iface + '... ');
				if (rt_name != 'main') {
					let rt = readfile(pkg.rt_tables_file) || '';
					let lines = filter(split(rt, '\n'), l => index(l, rt_name) < 0);
					writefile(pkg.rt_tables_file, join('\n', lines) + '\n');
				}
				pbr.nft_file.sed('netifd', "'/" + _mark + "/d'");
				output.verbose_okb();
			}
		}

		if (!split_second) {
			mark = sprintf('0x%06x', hex(_mark) + hex(cfg.uplink_mark));
			priority = +_priority - 1;
			tid = +_tid + 1;
		}
	});

	output.newline1();

	switch (action) {
	case 'install':
		pbr.nft_file.apply('netifd');
		if (!target_iface)
			uci_ctx(pkg.name).set(pkg.name, 'config', 'netifd_enabled', '1');
		break;
	case 'remove':
		if (!target_iface) {
			pbr.nft_file.remove('netifd');
			uci_ctx(pkg.name).delete(pkg.name, 'config', 'netifd_enabled');
		}
		break;
	case 'uninstall':
		if (!target_iface)
			pbr.nft_file.remove('netifd');
		break;
	}

	uci_ctx(pkg.name).commit(pkg.name);
	uci_ctx('network').commit('network');
	sys('sync');

	output.print('Restarting network (' + action + ') ');
	if (sys('/etc/init.d/network reload') == 0 && sys('/etc/init.d/firewall reload') == 0)
		output.okbn();
	else
		output.failn();

	return true;
};

// ── start ───────────────────────────────────────────────────────────

pbr.start_service = function(args) {
	let param = (args && args[0]) || 'on_start';
	let reloaded_iface = (args && args[1]) || null;

	// on_boot is handled entirely in shell; nothing to do here
	if (param == 'on_boot') return null;

	pbr.reset();
	if (!env.load(param)) {
		return null;
	}
	output.print('Detecting uplink (' + param + ') ');
	if (!is_wan_up(param)) {
		output.failn();
		output.warning(get_text('warningUplinkDown'));
		return null;
	}

	let start_time, end_time;
	start_time = time();
	pbr.interface.enumerate();
	end_time = time();
	logger_debug('[PERF-DEBUG] Enumerating interfaces took ' + (end_time - start_time) + 's');

	// Determine trigger
	let service_start_trigger;
	switch (param) {
	case 'on_interface_reload':
		if (reloaded_iface)
			service_start_trigger = 'on_interface_reload';
		else
			service_start_trigger = 'on_start';
		break;
	case 'on_reload':
		service_start_trigger = 'on_reload';
		break;
	case 'on_restart':
		service_start_trigger = 'on_start';
		break;
	default:
		service_start_trigger = 'on_start';
	}

	if (reloaded_iface && !is_supported_interface(reloaded_iface))
		return null;

	// Force full restart if there are errors/warnings or service not running
	let ubus_errors = ubus_call('service', 'list', { name: pkg.name });
	let svc_data = ubus_errors?.[pkg.name]?.instances?.main?.data;
	if (svc_data?.errors && length(svc_data.errors) > 0) {
		service_start_trigger = 'on_start';
		reloaded_iface = null;
	} else if (svc_data?.warnings && length(svc_data.warnings) > 0) {
		service_start_trigger = 'on_start';
		reloaded_iface = null;
	} else if (!is_service_running_nft()) {
		service_start_trigger = 'on_start';
		reloaded_iface = null;
	} else if (!svc_data?.gateways) {
		service_start_trigger = 'on_start';
		reloaded_iface = null;
	}

	pbr.service_start_trigger = service_start_trigger;

	switch (service_start_trigger) {
	case 'on_interface_reload':
		output.okn();
		output.info('Reloading Interface: ' + reloaded_iface + ' ');
		start_time = time();
		uci_ctx('network').foreach('network', 'interface', function(s) {
			pbr.interface.process(s['.name'], 'reload_interface', reloaded_iface);
		});
		end_time = time();
		logger_debug('[PERF-DEBUG] Reloading interface ' + reloaded_iface + ' took ' + (end_time - start_time) + 's');
		output.newline1();
		break;

	default: // on_reload, on_start, etc.
		pbr.resolver('store_hash');
		pbr.resolver('configure');
		pbr.cleanup('main_table', 'rt_tables', 'main_chains', 'sets');
		pbr.nft_file.init('main');
		output.okn();

		output.info('Processing interfaces ');
		start_time = time();
		uci_ctx('network').foreach('network', 'interface', function(s) {
			pbr.interface.process(s['.name'], 'create');
		});
		pbr.interface.process('tor', 'destroy');
		if (is_tor_running()) pbr.interface.process('tor', 'create');
		pbr.interface.process('all', 'create_global_rules');
		sys(pkg.ip_full + ' route flush cache');
		end_time = time();
		logger_debug('[PERF-DEBUG] Processing interfaces took ' + (end_time - start_time) + 's');
//		push(pbr.warnings, { code: 'warningDynamicRoutingMode' });
		output.newline1();

		// Process policies (common for all modes)
		if (is_config_enabled('policy')) {
			output.info('Processing policies ');
			start_time = time();
			let uid_counter = 0;
			uci_ctx(pkg.name, true).foreach(pkg.name, 'policy', function(s) {
				uid_counter++;
				let p = parse_options(s, policy_schema);
				pbr.policy.process('' + uid_counter,
					p.enabled, p.name, p.interface, p.src_addr, p.src_port,
					p.dest_addr, p.dest_port, p.proto, p.chain);
			});
			end_time = time();
			logger_debug('[PERF-DEBUG] Processing policies took ' + (end_time - start_time) + 's');
			output.newline1();
		}

		// Process DNS policies (common for all modes)
		if (is_config_enabled('dns_policy')) {
			output.info('Processing dns policies ');
			start_time = time();
			let uid_counter = 0;
			uci_ctx(pkg.name, true).foreach(pkg.name, 'dns_policy', function(s) {
				uid_counter++;
				let p = parse_options(s, dns_policy_schema);
				pbr.dns_policy.process('' + uid_counter,
					p.enabled, p.name, p.src_addr, p.dest_dns, p.dest_dns_port);
			});
			end_time = time();
			logger_debug('[PERF-DEBUG] Processing DNS policies took ' + (end_time - start_time) + 's');
			output.newline1();
		}

		// Process user files (common for all modes)
		if (is_config_enabled('include') || stat('/etc/' + pkg.name + '.d/')?.type == 'directory') {
			uci_ctx('network').foreach('network', 'interface', function(s) {
				pbr.interface.process(s['.name'], 'create_user_set');
			});
			output.info('Processing user file(s) ');
			start_time = time();
			uci_ctx(pkg.name, true).foreach(pkg.name, 'include', function(s) {
				pbr.user_file.process(s.enabled, s.path);
			});
			let user_dir = '/etc/' + pkg.name + '.d/';
			if (stat(user_dir)?.type == 'directory') {
				let files = lsdir(user_dir) || [];
				for (let f in files) {
					let fp = user_dir + f;
					if (stat(fp)?.type == 'file')
						pbr.user_file.process('1', fp);
				}
			}
			end_time = time();
			logger_debug('[PERF-DEBUG] Processing user files took ' + (end_time - start_time) + 's');
			output.newline1();
		}

		start_time = time();
		pbr.nft_file.apply('main');
		end_time = time();
		logger_debug('[PERF-DEBUG] Installing nft rules took ' + (end_time - start_time) + 's');
		break;
	}

	let _build_gateway_summary = function() {
		let lines = [];
		for (let name in keys(pbr.interface)) {
			let iface = pbr.interface[name];
			if (type(iface) == 'function') continue;
			if (!iface || iface.action == 'mwan4_strategy') continue;
			let disp_dev = (name != iface.device_ipv4) ? iface.device_ipv4 : '';
			let gw4 = iface.gateway_ipv4 || '0.0.0.0';
			let gw6 = iface.gateway_ipv6 || '::/0';
			let text = name + '/' + (disp_dev ? disp_dev + '/' : '') + gw4;
			if (cfg.ipv6_enabled) text += '/' + gw6;
			if (iface.status_symbol) text += ' ' + iface.status_symbol;
			push(lines, text);
		}
		return join('\\n', lines);
	};
	let gw_summary = _build_gateway_summary();
	let gateways = [];
	for (let name in keys(pbr.interface)) {
		let iface = pbr.interface[name];
		if (type(iface) == 'function') continue;
		if (iface.action == 'mwan4_strategy') continue;
		push(gateways, {
			name: name,
			device_ipv4: iface.device_ipv4,
			gateway_ipv4: iface.gateway_ipv4,
			device_ipv6: iface.device_ipv6,
			gateway_ipv6: iface.gateway_ipv6,
			'default': iface.is_default || false,
			action: iface.action,
			table_id: '' + (iface.tid || ''),
			mark: iface.mark || '',
			priority: '' + (iface.priority || ''),
		});
	}
	let result = {
		packageCompat: +pkg.compat,
		version: pkg.version,
		gateways: gateways,
		status: {},
		errors: pbr.errors,
		warnings: pbr.warnings,
		interfaces: env.webui_interfaces,
		platform: {
			nft_installed: env.nft_installed,
			adguardhome_installed: env.adguardhome_installed,
			dnsmasq_installed: env.dnsmasq_installed,
			unbound_installed: env.unbound_installed,
			dnsmasq_nftset_support: env.dnsmasq_nftset_supported,
		},
		ifacesTriggers: pbr.ifaces_triggers,
	};
	if (gw_summary)
		result.status.gateways = gw_summary;
	return result;
};

// ── stop_service ────────────────────────────────────────────────────

pbr.stop_service = function() {
	pbr.reset();
	if (!is_service_running_nft() && get_rt_tables_next_id() == get_rt_tables_non_pbr_next_id())
		return;

	unlink(pkg.lock_file);
	env.load('on_stop');
	output.print('Resetting routing ');
	let ok = pbr.nft_file.remove('main') && pbr.cleanup('main_table', 'rt_tables');
	sys(pkg.ip_full + ' route flush cache');
	sys('fw4 -q reload');
	if (ok) output.okn();
	else output.failn();

	output.print('Resetting resolver ');
	if (pbr.resolver('store_hash') && pbr.resolver('cleanup'))
		output.okn();
	else
		output.failn();

	if (pbr.resolver('compare_hash')) pbr.resolver('restart');

	if (cfg.enabled) {
		output.print(pkg.service_name + ' stopped ');
		output.okn();
	}
};

// ── service_started ─────────────────────────────────────────────────

pbr.service_started = function(param) {
	if (param == 'on_boot') return;

	env.load('service_started');

	// Fetch errors/warnings/gateways from ubus (stored by start_service via procd)
	let svc_info = ubus_call('service', 'list', { name: pkg.name });
	let svc_data = svc_info?.[pkg.name]?.instances?.main?.data;

	if (pbr.nft_file.exists('main')) {
		if (pbr.resolver('compare_hash')) pbr.resolver('restart');
		let gw_summary = svc_data?.status?.gateways;
		if (gw_summary)
			output.print(pkg.service_name + ' started with gateways:\\n' + gw_summary + '\\n');
	} else {
		output.print(pkg.service_name + ' FAILED TO START!!!\\n');
		output.print('Check the output of nft -c -f ' + pkg.nft_temp_file + '\\n');
	}

	let warnings = svc_data?.warnings || [];
	for (let w in warnings) {
		output.warning(get_text(w.code, w.info));
	}
	if (length(warnings) > 0)
		output.warning(get_text('warningSummary', pkg.url('#warning-messages-details')));

	let errors = svc_data?.errors || [];
	for (let e in errors) {
		output.error(get_text(e.code, e.info));
	}
	if (length(errors) > 0)
		output.error(get_text('errorSummary', pkg.url('#error-messages-details')));

	writefile(pkg.lock_file, trim(shell('echo $$')));
};

// ── emit_procd_shell ────────────────────────────────────────────────

pbr.emit_procd_shell = function(data) {
	if (!data) return '';
	let lines = [];

	push(lines, 'json_add_int packageCompat ' + shell_quote('' + (data.packageCompat || 0)));
	push(lines, 'json_add_string version ' + shell_quote(data.version || ''));

	// Interfaces array
	push(lines, 'json_add_array interfaces');
	for (let iface in (data.interfaces || []))
		push(lines, 'json_add_string \'\' ' + shell_quote(iface));
	push(lines, 'json_close_array');

	// Platform support
	push(lines, 'json_add_object platform');
	for (let k in keys(data.platform || {})) {
		let v = data.platform[k];
		if (type(v) == 'bool')
			push(lines, 'json_add_boolean ' + k + ' ' + shell_quote(v ? '1' : '0'));
		else
			push(lines, 'json_add_string ' + k + ' ' + shell_quote('' + v));
	}
	push(lines, 'json_close_object');

	// Gateways array
	push(lines, 'json_add_array gateways');
	for (let gw in (data.gateways || [])) {
		push(lines, "json_add_object ''");
		for (let k in keys(gw)) {
			let v = gw[k];
			if (type(v) == 'bool')
				push(lines, 'json_add_boolean ' + k + ' ' + shell_quote(v ? '1' : '0'));
			else if (type(v) == 'int')
				push(lines, 'json_add_int ' + k + ' ' + shell_quote('' + v));
			else
				push(lines, 'json_add_string ' + k + ' ' + shell_quote('' + v));
		}
		push(lines, 'json_close_object');
	}
	push(lines, 'json_close_array');

	// Status object
	push(lines, 'json_add_object status');
	if (data.status?.gateways)
		push(lines, 'json_add_string gateways ' + shell_quote(data.status.gateways));
	push(lines, 'json_close_object');

	// Errors
	push(lines, 'json_add_array errors');
	for (let e in (data.errors || [])) {
		push(lines, "json_add_object ''");
		push(lines, 'json_add_string code ' + shell_quote(e.code || ''));
		push(lines, 'json_add_string info ' + shell_quote(e.info || ''));
		push(lines, 'json_close_object');
	}
	push(lines, 'json_close_array');

	// Warnings
	push(lines, 'json_add_array warnings');
	for (let w in (data.warnings || [])) {
		push(lines, "json_add_object ''");
		push(lines, 'json_add_string code ' + shell_quote(w.code || ''));
		push(lines, 'json_add_string info ' + shell_quote(w.info || ''));
		push(lines, 'json_close_object');
	}
	push(lines, 'json_close_array');

	// Shell variables for service_triggers() (not part of procd data)
	if (data.ifacesTriggers)
		push(lines, '_pbr_ifaces_triggers=' + shell_quote(data.ifacesTriggers));

	return join('\n', lines) + '\n';
};

// ── Status Service ──────────────────────────────────────────────────

pbr.status_service = function(param) {
	env.load('status');

	let board = ubus_call('system', 'board', {});
	let openwrt_release = board?.release?.description || 'unknown';

	let _SEP_ = '===================================';
	let status_text = pkg.service_name + ' on ' + openwrt_release + '.\\n';

	if (cfg.uplink_interface4) {
		let dev4 = network_get_device(cfg.uplink_interface4);
		if (!dev4) dev4 = network_get_physdev(cfg.uplink_interface4);
		status_text += 'Uplink (IPv4): ' + cfg.uplink_interface4 +
			(dev4 ? '/' + dev4 : '') + '/' + (env.uplink_gw4 || '0.0.0.0') + '.\\n';
	}
	if (cfg.uplink_interface6) {
		let dev6 = network_get_device(cfg.uplink_interface6);
		if (!dev6) dev6 = network_get_physdev(cfg.uplink_interface6);
		if (!dev6) {
			let dev4 = network_get_device(cfg.uplink_interface4);
			if (!dev4) dev4 = network_get_physdev(cfg.uplink_interface4);
			dev6 = dev4 || '';
		}
		status_text += 'Uplink (IPv6): ' + cfg.uplink_interface6 +
			(dev6 ? '/' + dev6 : '') + '/' + (env.uplink_gw6 || '::/0') + '.\\n';
	}

	printf('%s\n', _SEP_);
	printf('%s - environment\n', pkg.name);
	printf('%s', replace(status_text, /\\n/g, '\n'));
	printf('%s\n', _SEP_);
	system("dnsmasq --version 2>/dev/null | sed '/^$/,$d'");

	if (pbr.nft_file.exists('netifd')) {
		printf('%s\n', _SEP_);
		let netifd_content = pbr.nft_file.show('netifd');
		if (netifd_content) printf('%s', netifd_content);
	}
	if (pbr.nft_file.exists('main')) {
		printf('%s\n', _SEP_);
		let main_content = pbr.nft_file.show('main');
		if (main_content) printf('%s', main_content);
	}

	printf('%s\n', _SEP_);
	printf('%s chains - policies\n', pkg.name);
	for (let ch in split(pkg.chains_list + ' dstnat', /\s+/)) {
		system('nft -a list table inet ' + pkg.nft_table +
			" | sed -n '/chain " + pkg.nft_prefix + '_' + ch + " {/,/\\t}/p'");
	}

	printf('%s\n', _SEP_);
	printf('%s chains - marking\n', pkg.name);
	let mark_chains = get_mark_nft_chains();
	for (let mc in split(mark_chains, /\s+/)) {
		if (!mc) continue;
		system('nft -a list table inet ' + pkg.nft_table +
			" | sed -n '/chain " + mc + " {/,/\\t}/p'");
	}

	printf('%s\n', _SEP_);
	printf('%s nft sets\n', pkg.name);
	let sets = get_nft_sets();
	for (let ns in split(sets, /\s+/)) {
		if (!ns) continue;
		system('nft -a list table inet ' + pkg.nft_table +
			" | sed -n '/set " + ns + " {/,/\\t}/p'");
	}

	if (stat(pkg.dnsmasq_file)?.size > 0) {
		printf('%s\n', _SEP_);
		printf('dnsmasq nft sets in %s\n', pkg.dnsmasq_file);
		printf('%s', readfile(pkg.dnsmasq_file) || '');
	}

	printf('%s\n', _SEP_);
	printf('%s tables & routing\n', pkg.name);
	let rt = readfile(pkg.rt_tables_file) || '';
	let table_count = 0;
	for (let l in split(rt, '\n'))
		if (index(l, pkg.name + '_') >= 0) table_count++;
	let wan_tid = +get_rt_tables_next_id() - table_count;

	for (let i = 0; i <= table_count; i++) {
		let tid = (i == 0) ? 'main' : '' + (wan_tid + i - 1);
		let status_table = '';
		for (let l in split(rt, '\n')) {
			if (index(l, tid + '\t') == 0 || index(l, tid + ' ') == 0) {
				let parts = split(trim(l), /\s+/);
				if (length(parts) >= 2) status_table = parts[1];
			}
		}
		printf('IPv4 table %s%s routes:\n', tid, status_table ? ' (' + status_table + ')' : '');
		system(pkg.ip_full + ' -4 route show table ' + tid + " | sed 's/^/    /'");
		printf('IPv4 table %s%s rules:\n', tid, status_table ? ' (' + status_table + ')' : '');
		system(pkg.ip_full + ' -4 rule list table ' + tid + " | sed 's/^/    /'");
		if (cfg.ipv6_enabled) {
			printf('%s\n', _SEP_);
			printf('IPv6 table %s routes:\n', tid);
			system(pkg.ip_full + ' -6 route show table ' + tid + " | sed 's/^/    /'");
			printf('IPv6 table %s rules:\n', tid);
			system(pkg.ip_full + ' -6 rule list table ' + tid + " | sed 's/^/    /'");
		}
		printf('%s\n', _SEP_);
	}
};

// ── Support ─────────────────────────────────────────────────────────

pbr.support = function() {
	printf('Setting counters and verbosity for diagnostics...\n');
	let ctx = uci_ctx(pkg.name);
	ctx.set(pkg.name, 'config', 'nft_rule_counter', '1');
	ctx.set(pkg.name, 'config', 'nft_set_counter', '1');
	ctx.set(pkg.name, 'config', 'verbosity', '2');
	ctx.commit(pkg.name);

	for (let cfg_name in ['dhcp', 'firewall', 'network', 'pbr']) {
		let content = readfile('/etc/config/' + cfg_name);
		if (!content) continue;
		printf('\n===== %s config =====\n', cfg_name);
		// Simple masking: mask sensitive option values
		for (let line in split('' + content, '\n')) {
			let m = match(line, /^(\s*(?:option|list)\s+)(endpoint_host|key|password|preshared_key|private_key|psk|public_key|token|username)(\s+)(.*)/);
			if (m) {
				let masked = replace(m[4], /[^\s.\x27]/g, '*');
				printf('%s%s%s%s\n', m[1], m[2], m[3], masked);
			} else {
				printf('%s\n', line);
			}
		}
	}
	printf('\n===== ubus call system board =====\n');
	system('ubus call system board');
	printf('\n===== /etc/init.d/pbr restart =====\n');
	system('/etc/init.d/pbr restart');
	printf('\n===== /etc/init.d/pbr status (after restart) =====\n');
	system('/etc/init.d/pbr status');
};

// ── rpcd Data Functions ─────────────────────────────────────────────

pbr.get_init_list = function(name) {
	name = name || pkg.name;
	env.load('rpcd');
	let result = {};
	let enabled = uci_ctx(pkg.name).get(pkg.name, 'config', 'enabled') || '0';
	result[name] = { enabled: (enabled == '1') };
	return result;
};

pbr.get_init_status = function(name) {
	name = name || pkg.name;
	env.load('status');

	let ubus_data = ubus_call('service', 'list', { name: pkg.name });
	let svc_data = ubus_data?.[pkg.name]?.instances?.main?.data;
	let gateways = svc_data?.status?.gateways || '';
	// Clean ANSI codes from gateways
	gateways = replace(gateways, /\x1b\[[0-9;]*m/g, '');
	gateways = replace(gateways, /\\n/g, '<br />');

	let result = {};
	result[name] = {
		enabled: !!cfg.enabled,
		running: env.is_running_nft_file(),
		running_iptables: false,
		running_nft: is_service_running_nft(),
		running_nft_file: env.is_running_nft_file(),
		version: pkg.version,
		packageCompat: +pkg.compat,
		gateways: gateways,
		gatewaysList: svc_data?.gateways || [],
		errors: svc_data?.errors || [],
		warnings: svc_data?.warnings || [],
		interfaces: env.webui_interfaces,
		platform: {
			nft_installed: env.nft_installed,
			adguardhome_installed: env.adguardhome_installed,
			dnsmasq_installed: env.dnsmasq_installed,
			unbound_installed: env.unbound_installed,
			dnsmasq_nftset_support: env.dnsmasq_nftset_supported,
		},
	};
	return result;
};

pbr.get_platform_support = function(name) {
	name = name || pkg.name;
	env.load('rpcd');
	let result = {};
	result[name] = {
		nft_installed: env.nft_installed,
		adguardhome_installed: env.adguardhome_installed,
		dnsmasq_installed: env.dnsmasq_installed,
		unbound_installed: env.unbound_installed,
		dnsmasq_nftset_support: env.dnsmasq_nftset_supported,
	};
	return result;
};

pbr.get_supported_interfaces = function(name) {
	name = name || pkg.name;
	env.load('rpcd');
	let result = {};
	result[name] = { interfaces: env.webui_interfaces };
	return result;
};

// ── Module Export ───────────────────────────────────────────────────

export default {
	pkg,
	start_service:            pbr.start_service,
	stop_service:             pbr.stop_service,
	status_service:           pbr.status_service,
	netifd:                   pbr.netifd,
	support:                  pbr.support,
	get_init_status:          pbr.get_init_status,
	get_init_list:            pbr.get_init_list,
	get_platform_support:     pbr.get_platform_support,
	get_supported_interfaces: pbr.get_supported_interfaces,
	service_started:          pbr.service_started,
	emit_procd_shell:         pbr.emit_procd_shell,
};

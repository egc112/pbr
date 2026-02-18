'use strict';
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright 2017-2026 MOSSDeF, Stan Grishin (stangri@melmac.ca).
//
// CLI dispatcher for pbr.
// Called from init script:
//   ucode -S -L /lib/pbr /lib/pbr/cli.uc -- <action> [args...]

import pbr from 'pbr';

let action = shift(ARGV);
if (action == '--') action = shift(ARGV);

switch (action) {
case 'start':
	let start_result = pbr.start(ARGV);
	if (start_result)
		print(pbr.emit_procd_shell(start_result));
	break;

case 'stop':
	pbr.stop();
	break;

case 'status':
	pbr.status_service(ARGV[0]);
	break;

case 'netifd':
	pbr.netifd(ARGV[0], ARGV[1]);
	break;

case 'support':
	pbr.support();
	break;

case 'version':
	print(pbr.pkg.version + '\n');
	break;

case 'service_started':
	pbr.service_started_actions(ARGV[0]);
	break;

case 'get_network_trigger_info':
	let info = pbr.get_network_trigger_info();
	if (info)
		print(sprintf('%J', info) + '\n');
	break;

default:
	warn('Unknown action: ' + (action || '(none)') + '\n');
	exit(1);
}

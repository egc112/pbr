// Downloads AWS IP ranges and adds them to the PBR user destination sets.

return function(api) {
	if (!api.compat || api.compat < 27) return;

	let url = 'https://ip-ranges.amazonaws.com/ip-ranges.json';
	let iface = 'wan';

	let raw = api.download(url);
	if (!raw) return;

	let data = json(raw);
	if (!data) return;

	let prefixes4 = [];
	for (let entry in data.prefixes)
		if (entry.ip_prefix) push(prefixes4, entry.ip_prefix);

	for (let prefix in prefixes4)
		api.nft4('add element ' + api.table + ' pbr_' + iface + '_4_dst_ip_user { ' + prefix + ' }');

	let prefixes6 = [];
	for (let entry in data.ipv6_prefixes)
		if (entry.ipv6_prefix) push(prefixes6, entry.ipv6_prefix);

	for (let prefix in prefixes6)
		api.nft6('add element ' + api.table + ' pbr_' + iface + '_6_dst_ip_user { ' + prefix + ' }');
};

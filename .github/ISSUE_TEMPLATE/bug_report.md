---
name: Bug report
about: Report a bug in the pbr service
title: "[pbr] "
labels: bug
assignees: stangri

---

**Before opening this issue**

If you're using the LuCI web UI, please decide first whether the bug is in the UI or the service:

- The setting saves correctly but `pbr` still misbehaves → file here.
- Service-level commands (e.g. `service pbr status`) reproduce the bug without the UI → file here.
- Only the UI looks broken / a control does nothing / Save & Apply produces a JS error → file at [stangri/luci-app-pbr](https://github.com/stangri/luci-app-pbr/issues) instead.

**Describe the bug**

A clear and concise description of what the bug is.

**To reproduce**

1.
2.

**Expected behavior**

A clear and concise description of what you expected to happen.

**Diagnostic info**

Please run the following and paste the output (you can mask sensitive parts). See [Getting Help](https://docs.openwrt.melmac.ca/pbr/#getting-help) in the docs for context.

For pbr 1.2.1 and newer, this single command captures everything needed (and masks sensitive information automatically):

```sh
service pbr support
```

For older versions, please run these instead:

```sh
ubus call system board
uci export dhcp
uci export firewall
uci export network
uci export pbr
service pbr status
```

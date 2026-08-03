#!/bin/sh
set -eu

# Simple POSIX shell tests for DNS port string building used by pbr
# This verifies that when dest_dns_port is unset/empty, no trailing colon is produced.

build_dest4() {
  dest_dns_ipv4="$1"
  dest_dns_port="$2"

  if [ -n "${dest_dns_port}" ]; then
    printf 'dport 53 dnat ip to %s:%s' "$dest_dns_ipv4" "$dest_dns_port"
  else
    printf 'dport 53 dnat ip to %s' "$dest_dns_ipv4"
  fi
}

build_dest6() {
  dest_dns_ipv6="$1"
  dest_dns_port="$2"

  if [ -n "${dest_dns_port}" ]; then
    printf 'dport 53 dnat ip6 to %s:%s' "$dest_dns_ipv6" "$dest_dns_port"
  else
    printf 'dport 53 dnat ip6 to %s' "$dest_dns_ipv6"
  fi
}

run_test() {
  name="$1"
  got="$2"
  want="$3"

  if [ "${got}" = "${want}" ]; then
    printf "OK: %s\n" "$name"
  else
    printf "FAIL: %s\n  got:  %s\n  want: %s\n" "$name" "$got" "$want"
    exit 1
  fi
}

# Test cases
run_test "ipv4 no port" "$(build_dest4 1.1.1.1 "")" "dport 53 dnat ip to 1.1.1.1"
run_test "ipv4 with port" "$(build_dest4 1.1.1.1 5353)" "dport 53 dnat ip to 1.1.1.1:5353"
run_test "ipv6 no port" "$(build_dest6 2606:4700:4700::1111 "")" "dport 53 dnat ip6 to 2606:4700:4700::1111"
run_test "ipv6 with port" "$(build_dest6 2606:4700:4700::1111 5353)" "dport 53 dnat ip6 to 2606:4700:4700::1111:5353"

printf "All tests passed.\n"

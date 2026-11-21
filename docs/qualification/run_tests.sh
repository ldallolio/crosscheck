#!/bin/sh
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
# Requirement-based tests of crosscheck-check that are not already a CI step:
# exit statuses (TOR-6) and large integers (TOR-7). Usage: run_tests.sh CHECKER
set -u
c=$1
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
here=$(cd "$(dirname "$0")" && pwd)
certs=$here/../../formalization/test/certificates
fail=0
expect() { # expect STATUS FILE...
  want=$1; shift
  "$c" "$@" >/dev/null 2>&1
  got=$?
  if [ "$got" != "$want" ]; then echo "FAIL: exit $got, expected $want: $*"; fail=1; fi
}
expect 0 "$certs/count.json"
expect 0 "$certs/program.json"
expect 0 "$certs/minic.json"
expect 0 "$certs/response.json"
expect 1 "$certs/count_rejected.json"
expect 1 "$certs/program_rejected.json"
expect 1 "$certs/minic_rejected.json"
expect 1 "$certs/response_rejected.json"
expect 1 "$certs/count.json" "$certs/count_rejected.json"   # one bad file among good ones
printf '{bad' > "$t/malformed.json"
expect 2 "$t/malformed.json"
expect 2 "$t/missing.json"
expect 2
# TOR-7: `x := x + 1` with cost 10^40 and bound 10^40 is accepted; with bound 10^40 - 1 it
# is rejected (a 64-bit or floating-point comparison would not tell them apart).
big=10000000000000000000000000000000000000000
small=9999999999999999999999999999999999999999
for b in $big $small; do
  cat > "$t/big$b.json" <<J
{ "format": "crosscheck-certificates", "version": 2, "programs": [ { "name": "big", "variables": ["x"],
  "functions": [ { "name": "f", "pre": [], "bound": $b, "post": [], "mods": [0],
    "body": {"node": "assign", "w": $big, "x": 0, "a": {"sv": [1], "c": 1}} } ] } ] }
J
done
expect 0 "$t/big$big.json"
expect 1 "$t/big$small.json"
[ "$fail" = 0 ] && echo "all requirement tests passed"
exit $fail

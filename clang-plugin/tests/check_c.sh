#!/bin/sh
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
# Runs crosscheck-tool on a C file; every function named ok_* must be accepted and every
# function named bad_* rejected. Usage: check_c.sh TOOL FILE INCLUDE [clang flags...]
set -eu
tool=$1; file=$2; inc=$3; shift 3
out=$("$tool" --summary "$file" -- -x c -std=c99 -I"$inc" "$@" 2>/dev/null || true)
echo "$out"
fail=0
for f in $(grep -o '^\(CROSSCHECK_REALTIME\|CROSSCHECK_DEADLINE([0-9]*)\) [a-z0-9_ ]* \(ok\|bad\)_[a-z0-9_]*' "$file" | grep -o '\(ok\|bad\)_[a-z0-9_]*'); do
  case $f in
    ok_*) echo "$out" | grep -q "^OK   $f:" || { echo "expected $f to be accepted"; fail=1; } ;;
    bad_*) echo "$out" | grep -q "^FAIL $f:" || { echo "expected $f to be rejected"; fail=1; } ;;
  esac
done
exit $fail

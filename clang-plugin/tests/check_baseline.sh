#!/bin/sh
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
# The cost bounds of the example programs must equal the committed baseline
# (benchmarks/bounds-baseline.json, the figures of Table tab:plugin). After a change
# of the analyser that changes them, regenerate it with
#   scripts/cost_diff.py REPORTDIR --snapshot ../benchmarks/bounds-baseline.json
# and update the table, benchmarks/README.md and the paper together.
# Usage: check_baseline.sh TOOL BENCHDIR INCLUDE PYTHON [clang flags...]
set -eu
tool=$1; bench=$2; inc=$3; py=$4; shift 4
here=$(dirname "$0")
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
for f in "$bench"/*.cpp; do
  status=0
  "$tool" --report="$out/$(basename "$f" .cpp).json" "$f" -- -std=c++20 -I"$inc" "$@" >/dev/null 2>&1 || status=$?
  if [ "$status" -gt 1 ]; then echo "the tool failed ($status) on $f"; exit 1; fi
done
"$py" "$here/../scripts/cost_diff.py" "$bench/bounds-baseline.json" "$out" --exact

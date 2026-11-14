#!/bin/sh
# Emits the certificates of the example programs and runs the verified Lean
# checker on them. Usage: check_certificates.sh TOOL CHECKER DIRS INCLUDE [clang flags...]
# (DIRS: directories of .cpp files, separated by ':').
# Fails if the checker rejects a certificate or if fewer than MIN are emitted.
set -eu
tool=$1; checker=$2; dirs=$3; inc=$4; shift 4
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
IFS_OLD=$IFS; IFS=:
for d in $dirs; do
  IFS=$IFS_OLD
  for f in "$d"/*.cpp; do
    status=0
    "$tool" --opt=certificates="$out/$(basename "$f" .cpp).json" "$f" -- -std=c++20 -I"$inc" "$@" \
      >/dev/null 2>&1 || status=$?
    # 1 = a function was rejected (expected for the rejected_* examples); a signal is a bug.
    if [ "$status" -gt 1 ]; then echo "the tool failed ($status) on $f"; exit 1; fi
  done
done
IFS=$IFS_OLD
"$checker" "$out"/*.json | tee "$out/result.txt"
accepted=$(grep -c '^ACCEPTED' "$out/result.txt" || true)
if grep -q '^REJECTED\|^PROGRAM.*REJECTED' "$out/result.txt"; then echo "a certificate was rejected"; exit 1; fi
if [ "$accepted" -lt "${MIN_CERTIFICATES:-15}" ]; then echo "only $accepted certificates"; exit 1; fi

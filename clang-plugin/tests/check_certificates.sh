#!/bin/sh
# Emits the certificates of the example programs and runs the verified Lean
# checker on them. Usage: check_certificates.sh TOOL CHECKER BENCHDIR INCLUDE [clang flags...]
# Fails if the checker rejects a certificate or if fewer than MIN are emitted.
set -eu
tool=$1; checker=$2; bench=$3; inc=$4; shift 4
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
for f in "$bench"/*.cpp; do
  "$tool" --opt=certificates="$out/$(basename "$f" .cpp).json" "$f" -- -std=c++20 -I"$inc" "$@" \
    >/dev/null 2>&1 || true
done
"$checker" "$out"/*.json | tee "$out/result.txt"
accepted=$(grep -c '^ACCEPTED' "$out/result.txt" || true)
if grep -q '^REJECTED' "$out/result.txt"; then echo "a certificate was rejected"; exit 1; fi
if [ "$accepted" -lt "${MIN_CERTIFICATES:-7}" ]; then echo "only $accepted certificates"; exit 1; fi

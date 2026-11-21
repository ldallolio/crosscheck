#!/usr/bin/env bash
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
# Runs inside the CoFloCo Docker image (afloresmontoya/cofloco). Reads on stdin a tar of
# llvm2kittel integer programs <function>.koat (from its_in_container.sh); converts each
# with CoFloCo's own front-end (interfaces/C2ces: koat2cfg.pl, then cfg2ces.pl, default
# cost model: one unit per transition, as in KoAT2) and prints
# "function<TAB>maximum cost<TAB>asymptotic class", or "!..." on failure or timeout.
set -u
T=${COFLOCO_TIMEOUT:-60}
C=/cofloco/interfaces/C2ces
mkdir -p /tmp/its && cd /tmp/its && tar xf -
shopt -s nullglob
for k in *.koat; do
  f=${k%.koat}
  if ! timeout "$T" "$C/koat2cfg.pl" "$k" -o "$f.cfg" >/dev/null 2>&1 || [ ! -s "$f.cfg" ] \
     || ! timeout "$T" "$C/cfg2ces.pl" "$f.cfg" -o "$f.ces" >/dev/null 2>&1 || [ ! -s "$f.ces" ]; then
    printf '%s\t!conversion-failed\n' "$f"; continue
  fi
  out=$(timeout "$T" /cofloco/cofloco -i "$f.ces" 2>/dev/null)
  mx=$(printf '%s\n' "$out" | sed -n 's/^### Maximum cost of [^:]*: *//p' | head -1)
  cl=$(printf '%s\n' "$out" | sed -n 's/^Asymptotic class: *//p' | head -1)
  if [ -z "$cl" ]; then printf '%s\t!timeout-or-error\n' "$f"; else printf '%s\t%s\t%s\n' "$f" "$mx" "$cl"; fi
done

#!/usr/bin/env bash
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
# Runs inside the KoAT2 Docker image (koat2:latest, release v2.1.0); see koat2.py.
# Reads one preprocessed C file on stdin; prints "function<TAB>first line of KoAT2's answer" for
# every function defined in it. Callees are inlined (llvm2kittel -eager-inline), so
# the answer for a function covers the code it calls.
set -u
T=${KOAT_TIMEOUT:-60}
cd /tmp
cat > in.c
sed 's/typedef enum {false, true} bool;/const int false = 0;\nconst int true = 1;/g' in.c > replaced.c
clang -c replaced.c -emit-llvm -w -Wno-logical-op-parentheses -o out.bc 2>/dev/null || { echo "!clang-failed"; exit 0; }
clang -S replaced.c -emit-llvm -w -o out.ll 2>/dev/null
for f in $(sed -n 's/^define [^@]*@\([A-Za-z0-9_.$]*\)(.*/\1/p' out.ll); do
  if ! timeout "$T" llvm2kittel -function="$f" -eager-inline -inline-voids -uniform-complexity-tuples \
        -division-constraint exact out.bc > "$f.its" 2>/dev/null; then
    printf '%s\t!translation-failed-or-timeout\n' "$f"; continue
  fi
  r=$(timeout "$T" koat2 analyse -i "$f.its" 2>/dev/null | head -1)
  r=${r:-!timeout-or-error}
  printf '%s\t%s\n' "$f" "$r"
done

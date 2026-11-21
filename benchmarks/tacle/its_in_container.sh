#!/usr/bin/env bash
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
# Runs inside the KoAT2 Docker image (koat2:latest, release v2.1.0), like
# koat_in_container.sh, with the same llvm2kittel options: reads one preprocessed C file
# on stdin and writes on stdout a tar of the integer programs <function>.koat that
# llvm2kittel produces (one per function, callees inlined). Used for CoFloCo.
set -u
T=${KOAT_TIMEOUT:-60}
mkdir -p /tmp/its && cd /tmp
cat > in.c
sed 's/typedef enum {false, true} bool;/const int false = 0;\nconst int true = 1;/g' in.c > replaced.c
clang -c replaced.c -emit-llvm -w -Wno-logical-op-parentheses -o out.bc 2>/dev/null || exit 0
clang -S replaced.c -emit-llvm -w -o out.ll 2>/dev/null
for f in $(sed -n 's/^define [^@]*@\([A-Za-z0-9_.$]*\)(.*/\1/p' out.ll); do
  timeout "$T" llvm2kittel -function="$f" -eager-inline -inline-voids -uniform-complexity-tuples \
        -division-constraint exact out.bc > "its/$f.koat" 2>/dev/null || rm -f "its/$f.koat"
done
tar cf - -C its .

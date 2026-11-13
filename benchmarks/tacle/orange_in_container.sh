#!/usr/bin/env bash
# Runs inside a container built from oRange's sources (see README.md, "oRange").
# Reads on stdin a tar holding the kernel directory <k>/ and the concatenated <k>.c;
# prints oRange's flow-fact XML for the whole program (entry point main).
# The `#pragma loopbound` lines (the benchmark's flow facts) are blanked first, in the
# kernel's files and in the concatenated file, keeping line numbers: oRange reads such
# pragmas, and it must not be given the answers.
set -u
k=$1; T=${ORANGE_TIMEOUT:-600}
mkdir -p /w && cd /w && tar xf -
find . -name '*.[ch]' -exec sed -i 's/^\([[:space:]]*\)#[[:space:]]*pragma[[:space:]]\+loopbound.*$/\1/' {} +
if grep -rqE '#[[:space:]]*pragma[[:space:]]+loopbound' --include='*.[ch]' . ; then echo '<!-- error: loopbound pragma left -->'; exit 0; fi
timeout "$T" orange -I "$k" "$k.c" main -o out.xml > res.txt 2> err.txt
rc=$?
if [ -s out.xml ]; then cat out.xml; else echo "<!-- oRange failed: exit $rc -->"; tail -3 err.txt | sed 's/--/- -/g; s/^/<!-- /; s/$/ -->/'; fi

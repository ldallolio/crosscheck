#!/usr/bin/env bash
# Runs KoAT2 and CoFloCo on every TPDB program fetched by run_tpdb.py, in containers
# without network, with the same scripts and options as for TACLeBench
# (../tacle/koat_in_container.sh, its_in_container.sh, cofloco_in_container.sh).
# Writes results/koat2/<key>.tsv and results/cofloco/<key>.tsv, where <key> is the
# file's path below Complexity_C_Integer with "/" replaced by "__" and no ".c".
# Needs the images koat2:latest and afloresmontoya/cofloco (see ../tacle/README.md).
# Usage: tools_in_containers.sh [parallel jobs, default 4]
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
T=$HERE/../tacle
BASE=$HERE/.cache/TPDB/Complexity_C_Integer
mkdir -p "$HERE/results/koat2" "$HERE/results/cofloco"
one() {
  f=$1; rel=${f#"$BASE"/}; key=${rel//\//__}; key=${key%.c}
  [ -s "$HERE/results/cofloco/$key.tsv" ] && return 0
  docker run -i --rm --network none --entrypoint bash koat2:latest -c "$(cat "$T/koat_in_container.sh")" \
    < "$f" > "$HERE/results/koat2/$key.tsv"
  docker run -i --rm --network none --entrypoint bash koat2:latest -c "$(cat "$T/its_in_container.sh")" < "$f" \
    | docker run -i --rm --network none --entrypoint bash afloresmontoya/cofloco \
        -c "$(cat "$T/cofloco_in_container.sh")" > "$HERE/results/cofloco/$key.tsv"
  [ -s "$HERE/results/cofloco/$key.tsv" ] || echo "(no function translated)" > /dev/null
  echo "$key"
}
export -f one; export HERE T BASE
find "$BASE" -name '*.c' | sort | xargs -P "${1:-4}" -I{} bash -c 'one "$@"' _ {}

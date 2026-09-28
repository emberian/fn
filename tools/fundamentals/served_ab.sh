#!/bin/sh
# Served-read latency, image A against image B, on one store (hbox).
#
#   sh tools/fundamentals/served_ab.sh OUT A_IMAGE B_IMAGE
#
# The served-readers lane's step-9 driver (planning/evidence/
# served-readers-2026-09-27/step9.sh and round2/step9b.sh, which ran from a
# scratch copy with hard-coded image paths), made a tool: B loads one fresh
# store of ARTICLES articles on tmpfs (the POST cost, OUT/load.json), then A
# and B read that store alternately, ROUNDS times per client, each run in its
# own systemd scope under MemoryMax=40G (at 24G the owner refuses its
# connections: connections-exceed-memory).  Every run is
# tools/fundamentals/sr_measure.py (open, greeting, ARTICLE n, OVER); OUT
# gets A-CLIENT-R.json / B-CLIENT-R.json, a .log per run, and load.txt with
# /proc/loadavg before every run and at the start and end, so a timing on a
# loaded box can be judged.  OUT/done is written last.
#
# Environment: ARTICLES (10000), ROUNDS (2), CLIENTS ("bulk"; "bulk line"
# adds the per-line client), CORES (a taskset CPU list, e.g. 12-23; none by
# default), MEM (40G).  Profiling (sb-sprof per batch, sr_measure --prof)
# needs the served-readers heap-hook image and is not driven from here.
set -u
[ $# -eq 3 ] || { sed -n '2,21p' "$0" | sed 's/^# \{0,1\}//' >&2; exit 2; }
O=$1 A=$2 B=$3
for image in "$A" "$B"; do
    [ -x "$image" ] || { echo "served_ab: $image is not an executable image" >&2; exit 2; }
done
H=$(cd "$(dirname "$0")" && pwd)
M=$H/sr_measure.py
ARTICLES=${ARTICLES:-10000} ROUNDS=${ROUNDS:-2} CLIENTS=${CLIENTS:-bulk} MEM=${MEM:-40G}
PIN=
[ -z "${CORES:-}" ] || PIN="taskset -c $CORES"
W=/dev/shm/served-ab-$$
FX=$W/fx
mkdir -p "$O" "$W"
trap 'rm -rf "$W"' EXIT
failed=0
run() {
    t=$1; shift
    echo "$t load $(cat /proc/loadavg)" >> "$O/load.txt"
    # shellcheck disable=SC2086
    systemd-run --user --scope -q -p MemoryMax="$MEM" -p MemorySwapMax=0 $PIN \
        python3 "$M" "$@" > "$O/$t.log" 2>&1
    rc=$?
    echo "$t exit $rc" >> "$O/load.txt"
    [ $rc -eq 0 ] || failed=$rc
}
echo "start $(date -u +%FT%TZ) $(cat /proc/loadavg)" > "$O/load.txt"
run load --image "$B" --fixture fresh --work "$W/l" --articles "$ARTICLES" --keep-store "$FX" --json "$O/load.json"
[ $failed -eq 0 ] || { echo "served_ab: the load failed; $O/load.log" >&2; exit "$failed"; }
r=1
while [ $r -le "$ROUNDS" ]; do
    for c in $CLIENTS; do
        for side in A B; do
            if [ $side = A ]; then image=$A; else image=$B; fi
            run $side-$c-$r --image "$image" --fixture "$FX" --work "$W/$side-$c-$r" \
                --articles "$ARTICLES" --client "$c" --json "$O/$side-$c-$r.json"
        done
    done
    r=$((r + 1))
done
echo "end $(date -u +%FT%TZ) $(cat /proc/loadavg)" >> "$O/load.txt"
echo "$failed" > "$O/done"
exit "$failed"

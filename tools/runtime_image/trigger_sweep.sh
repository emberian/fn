#!/bin/sh
# tools/runtime_image/trigger_sweep.sh IMAGE OUT REPS MIB...
# (lane image-floor-3) POST latency and RSS of IMAGE under each service
# collection trigger MIB (host/native/owner.lisp
# +fnn-owner-service-nursery-octets+, a defparameter set by --eval before
# ACL2 starts), REPS rounds in rotating order, one node_measure.py `run' of
# 1,000 POSTs of 2,048 octets at a 1,024 MB heap each; one JSON line per run
# in OUT/sweep.jsonl.  A measurement only.  Run on hbox under
# systemd-run --user --scope -p MemoryMax=8G, with nothing else measuring.
set -eu
IMAGE=$1 OUT=$2 REPS=$3; shift 3
HERE=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$OUT"
for mib in "$@"; do
  sed "s|--eval '(acl2::sbcl-restart)'|--eval '(setq acl2::+fnn-owner-service-nursery-octets+ (* $mib 1024 1024))' --eval '(acl2::sbcl-restart)'|" \
    "$IMAGE" > "$OUT/fn-host-trigger-$mib"
  chmod +x "$OUT/fn-host-trigger-$mib"
  grep -q "nursery-octets+ (\* $mib " "$OUT/fn-host-trigger-$mib" || { echo "no trigger in variant $mib" >&2; exit 2; }
done
round=0
while [ $round -lt "$REPS" ]; do
  set -- $(printf '%s\n' "$@" | awk -v r=$round '{a[NR]=$0} END {for (i=0;i<NR;i++) print a[(i+r)%NR+1]}')
  for mib in "$@"; do
    work="$OUT/w-$mib-$round"; rm -rf "$work"; mkdir -p "$work"
    line=$(python3 "$HERE/tools/runtime_image/node_measure.py" run "$OUT/fn-host-trigger-$mib" "$work" --posts 1000 --heap 1024)
    echo "{\"trigger_mib\": $mib, \"round\": $round, \"run\": $line}" >> "$OUT/sweep.jsonl"
    rm -rf "$work"
  done
  round=$((round + 1))
done
echo "sweep done: $OUT/sweep.jsonl"

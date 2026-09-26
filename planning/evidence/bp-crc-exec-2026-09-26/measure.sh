#!/bin/sh
# bp-crc-exec: the base image's and the lane image's BP codec, back to back.
S=/tank/fn/scratch/bp-crc-exec
BEFORE=/tank/fn/scratch/perf-ledger/tree/build/fn-host-developer.core
AFTER=$S/native-d9e3f0321e15/tree/build/fn-host-developer.core
cd $S
for round in 1 2; do
for which in before after; do
  if [ $which = before ]; then C=$BEFORE; else C=$AFTER; fi
  out=$S/bpenc-$which-$round.out
  { echo "== $which round $round core $C"; sha256sum $C; echo "== box: $(uptime)"; nproc; } > $out
  systemd-run --user --scope -q -p MemoryMax=24G sh $S/bpenc.sh $C >> $out 2>&1
  echo "== box after: $(uptime)" >> $out
done
done
sha256sum $S/bpenc-*.out > $S/bpenc-SHA256SUMS
echo MEASUREDONE

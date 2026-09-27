#!/bin/sh
# control-quanta (SCN-178): the mixed hour with the live group create + control grant every 120 s,
# before (owner-scheduler-2's after image, 39ce24036) and after (control-quanta-m e7f17498d), concurrently.
set -u
B=/tank/fn/scratch/control-quanta
BEFORE=/tank/fn/scratch/owner-scheduler-2/native-after/tree
AFTER=$B/native-after1/tree
OSSL=/tank/fn/scratch/owner-scheduler-2/native-after/bin/openssl-test
MIXED=/tank/fn/scratch/owner-scheduler-2/mixed.py
SECS=${1:-3600}
cd $B || exit 2
rm -rf $B/mixed-before $B/mixed-after
echo "== measure start $(date -u +%FT%TZ) secs=$SECS"
FN_MIXED_AGENTS=0 FN_MIXED_CONTROL=1 FN_MIXED_TREE=$BEFORE FN_MIXED_IMAGE=$BEFORE/build/fn-host-developer FN_MIXED_OPENSSL=$OSSL \
  systemd-run --user --scope --quiet --slice=swarm.slice -p MemoryMax=40G -p MemorySwapMax=0 -- python3 $MIXED $B/mixed-before $SECS > $B/mixed-before.log 2>&1 &
P1=$!
FN_MIXED_AGENTS=0 FN_MIXED_CONTROL=1 FN_MIXED_TREE=$AFTER FN_MIXED_IMAGE=$AFTER/build/fn-host-developer FN_MIXED_OPENSSL=$OSSL \
  systemd-run --user --scope --quiet --slice=swarm.slice -p MemoryMax=40G -p MemorySwapMax=0 -- python3 $MIXED $B/mixed-after $SECS > $B/mixed-after.log 2>&1 &
P2=$!
wait $P1; echo "mixed-before exit $?"
wait $P2; echo "mixed-after exit $?"
echo "== measure done $(date -u +%FT%TZ)"

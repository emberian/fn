#!/bin/sh
# post-identity-index: five alternating rounds, K = 400, pinned to cores 20-23
# (swarm-build uses 0-15), after run.sh registered the n1k-2k fixture.
set -u
S=/tank/fn/scratch/post-identity-index; M=$S/measure; W=/dev/shm/pidx2
AT=$S/native-r1/tree; A=$AT/build/fn-host-developer
B=/tank/fn/scratch/throughput-gate/native-img-6407de336/tree/build/fn-host-developer
F10=/tank/fn/scratch/fixtures/n10k-2k; F1=/tank/fn/scratch/fixtures/n1k-2k
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
mkdir -p $W $M/results2
cd $AT
ph() { mem=$1; shift; echo "== $* $(date -u +%H:%M:%SZ) load $(cut -d' ' -f1-3 /proc/loadavg)"
  systemd-run --user --scope -q -p MemoryMax=$mem -p MemorySwapMax=0 taskset -c 20-23 python3 $M/postmeasure.py "$@" > /dev/null; echo "   rc=$?"; }
for round in 1 2 3 4 5; do
  for n in 10k 1k; do
    if [ $n = 1k ]; then F=$F1; else F=$F10; fi
    for side in before after; do
      if [ $side = before ]; then I=$B; else I=$A; fi
      ph 24G post $I $F/store $W/$side-$n-$round $side-$n-$round 400; cp $W/$side-$n-$round.json $M/results2/; rm -rf $W/$side-$n-$round
    done
  done
done
rm -rf $W
echo MEASURE2-DONE $(date -u +%H:%M:%SZ)

#!/bin/sh
# signed-post-linear: matched before/after signed POST owner CPU, interleaved, tmpfs stores (no profiler).
S=/tank/fn/scratch/signed-post-linear; OUT=$S/meas; W=/dev/shm/signed-post-linear
export ACL2_CUSTOMIZATION=NONE LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
BEFORE=/tank/fn/scratch/throughput-gate/native-img-6407de336/tree
AFTER=$S/native-after-428ba1a5/tree
mkdir -p $OUT
for round in 1 2; do
for n in 1000 10000; do
  for pair in before=$BEFORE after=$AFTER; do
    L=${pair%%=*}; T=${pair#*=}
    echo "== $L n=$n round=$round $(date -u +%H:%M:%SZ) load $(cut -d' ' -f1-3 /proc/loadavg)" >> $OUT/summary.log
    python3 $S/prof_signed.py run $T $T/build/fn-host-developer $W/n$n $L-$round --k 20 > $OUT/$L-$n-$round.log 2>&1
    echo "   rc=$? $(grep RESULT $OUT/$L-$n-$round.log | python3 -c 'import sys,json; d=json.loads(sys.stdin.read()[7:]); print({k:d[k] for k in ("open_s","unsigned_median_s","signed_median_s","unsigned_owner_cpu_ms","signed_owner_cpu_ms","loadavg_after")})' 2>&1)" >> $OUT/summary.log
    rm -rf $W/n$n/$L-$round
  done
done
done
echo MEAS-DONE >> $OUT/summary.log

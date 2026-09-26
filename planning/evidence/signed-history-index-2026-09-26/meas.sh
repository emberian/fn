#!/bin/sh
# signed-history-index: matched before/after signed POST rows (tmpfs stores).
S=/tank/fn/scratch/signed-history-index
OUT=$S/meas; mkdir -p $OUT
export ACL2_CUSTOMIZATION=NONE LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
BEFORE=/tank/fn/scratch/commit-regression/native-img-8d4ea42c/tree
AFTER=$S/native-after-a888b104/tree
for n in 1000 10000; do
  for pair in before=$BEFORE after=$AFTER; do
    L=${pair%%=*}; T=${pair#*=}
    W=/dev/shm/signed-history-index/$L-$n; rm -rf $W
    python3 $S/measure_signed.py $T $T/build/fn-host-developer $W --n $n --signed 32 --rounds 7 > $OUT/$L-$n.log 2>&1
    echo "$L n=$n rc=$? $(grep SUMMARY $OUT/$L-$n.log | cut -c1-200)" >> $OUT/summary.log
    rm -rf $W
  done
done
echo done >> $OUT/summary.log

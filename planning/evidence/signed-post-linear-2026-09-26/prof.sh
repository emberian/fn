#!/bin/sh
# signed-post-linear: the before profile (perf-ledger's profiling twin of dev f314a5a3), tmpfs stores.
S=/tank/fn/scratch/signed-post-linear; OUT=$S/prof; W=/dev/shm/signed-post-linear
T=${TREE:-/tank/fn/scratch/perf-ledger/tree}; IMG=${IMG:-$T/build/fn-host-developer-prof}
export ACL2_CUSTOMIZATION=NONE LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
mkdir -p $OUT $W
for n in ${NS:-1000 10000}; do
  if [ ! -d $W/n$n/store ]; then
    rm -rf $W/n$n
    echo "== load n=$n $(date -u +%H:%M:%SZ) load $(cut -d' ' -f1-3 /proc/loadavg)" >> $OUT/summary.log
    python3 $S/prof_signed.py load $T $IMG $W/n$n --n $n --signed 32 --probes 40 > $OUT/load-$n.log 2>&1
    echo "   rc=$? $(grep RESULT $OUT/load-$n.log | cut -c1-160)" >> $OUT/summary.log
  fi
  echo "== run n=$n ${TAG:-before} $(date -u +%H:%M:%SZ) load $(cut -d' ' -f1-3 /proc/loadavg)" >> $OUT/summary.log
  python3 $S/prof_signed.py run $T $IMG $W/n$n ${TAG:-before} --k 20 ${SPROF---sprof} > $OUT/run-${TAG:-before}-$n.log 2>&1
  echo "   rc=$? $(grep RESULT $OUT/run-${TAG:-before}-$n.log | cut -c1-400)" >> $OUT/summary.log
  [ -d $W/n$n/${TAG:-before}/sprof ] && cp $W/n$n/${TAG:-before}/sprof/flat.txt $OUT/flat-${TAG:-before}-$n.txt && cp $W/n$n/${TAG:-before}/sprof/graph.txt $OUT/graph-${TAG:-before}-$n.txt
  rm -rf $W/n$n/${TAG:-before}
done
echo PROF-DONE >> $OUT/summary.log

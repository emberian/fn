#!/bin/sh
# usage: egress-run.sh TREE IMAGE LABEL [KINDS]
T=$1; IMG=$2; L=$3; K=${4:-harness,buffered,raw}
S=/tank/fn/scratch/egress-span; W=/dev/shm/egress-span/$L
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_PROF_LOAD=/tank/fn/scratch/perf-ledger/hooks.lisp FN_HEAP_DIR=$W-heap
rm -rf $W $W-heap; mkdir -p /dev/shm/egress-span
cd $T
echo "== $L $(date -u +%H:%M:%SZ) load $(cut -d' ' -f1-3 /proc/loadavg)"
systemd-run --user --scope -q -p MemoryMax=24G -p MemorySwapMax=0 python3 $S/egress.py $IMG $W $S/results/$L.json $K > $S/results/$L.out 2>&1
echo "rc=$? $(date -u +%H:%M:%SZ)"
cat $S/results/$L.out
rm -rf $W $W-heap

#!/bin/sh
# usage: run.sh LABEL N L TREE -- one measured point on the profiling image with the heap hook
L=$1; N=$2; P=$3; T=$4
S=/tank/fn/scratch/hot-path-scans; ROOT=$S/work
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
W=$ROOT/$L; rm -rf $W; mkdir -p $W/heap $S/results
FN_PROF_LOAD=$S/heap.lisp FN_HEAP_DIR=$W/heap python3 $T/tools/rep_measure.py --image $T/build/fn-host-developer-prof --heap-dir $W/heap --work $W/m --articles $N --octets $P --samples 32 --readers 3 --skip-checkpoint --json $S/results/$L.json > $S/results/$L.out 2>&1
echo "$L rc=$?"; uptime

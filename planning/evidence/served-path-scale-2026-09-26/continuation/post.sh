#!/bin/sh
# usage: post.sh LABEL TREE N -- rep_measure (heap hook, K=32, R=3) on /dev/shm, then 200 POSTs with call counts and an alloc profile
L=$1; T=$2; N=$3; M=/tank/fn/scratch/served-path-scale-2/m; W=/dev/shm/sps2/$L
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
rm -rf $W; mkdir -p $W/heap
FN_PROF_LOAD=/tank/fn/scratch/hot-path-scans/heap.lisp FN_HEAP_DIR=$W/heap python3 $T/tools/rep_measure.py --image $T/build/fn-host-developer-prof --heap-dir $W/heap --work $W/m --articles $N --octets 2048 --samples 32 --readers 3 --skip-checkpoint --json $M/post-$L.json > $M/post-$L.out 2>&1
echo "rep rc=$?" >> $M/post-$L.out; uptime >> $M/post-$L.out
FN_HOOK=$M/count.lisp python3 $M/allocprof.py $T $W/m $M/alloc-$L 900000 200 >> $M/post-$L.out 2>&1
echo "alloc rc=$?" >> $M/post-$L.out; uptime >> $M/post-$L.out
cp -r $W/m/store $M/store-$L-n$N 2>/dev/null || cp -r $W/m $M/store-$L-n$N
rm -rf $W
echo "rc=done" >> $M/post-$L.out

#!/bin/sh
# usage: alloc.sh -- 32 KiB POST bytes consed and timings, before/after alternating, on /dev/shm
S=/tank/fn/scratch/ingress-span-2/meas
T=/tank/fn/scratch/ingress-span-2/native-after/tree
BEFORE=/tank/fn/scratch/throughput-gate/native-img-f314a5a3/tree/build/fn-host-developer
AFTER=$T/build/fn-host-developer
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib64:/tank/fn/toolchains/openssl-3.5.8/lib
mkdir -p $S/results
for side in before after; do
  eval L=\$$(echo $side | tr a-z A-Z)
  # the launcher with the heap hook loaded before the entry (no rebuild; same core)
  sed "s#--no-userinit --eval#--no-userinit --load $S/heap.lisp --eval#" $L > $S/fn-host-$side-heap
  chmod +x $S/fn-host-$side-heap
  ln -sf $L.core $S/fn-host-$side-heap.core
done
cd $T
for r in 1 2; do for side in before after; do
  W=/dev/shm/ingress-span-2/$side-r$r; rm -rf $W; mkdir -p $W/heap
  python3 tools/rep_measure.py --image $S/fn-host-$side-heap --heap-dir $W/heap --work $W/m --articles 256 --octets 32768 --samples 32 --readers 1 --skip-reopen --skip-checkpoint --json $S/results/$side-r$r.json > $S/results/$side-r$r.out 2>&1
  echo "$side r$r rc=$? $(cat /proc/loadavg)"
  rm -rf $W
done; done
echo ALLOC-DONE

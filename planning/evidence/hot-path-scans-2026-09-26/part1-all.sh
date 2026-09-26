#!/bin/sh
# hot-path-scans-2: before (dev 5c6825b2) and after (lane ff2eacb3) rows, same box, same scripts
S=/tank/fn/scratch/hot-path-scans-2
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
for side in before after; do sh $S/setup.sh $S/$side-tree $side > $S/$side-setup.out 2>&1; done
for spec in "1000 2048" "10000 2048"; do set -- $spec
  for side in before after; do
    systemd-run --user --scope -p MemoryMax=40G sh $S/run.sh $side-n$1-2k $1 $2 $S/$side-tree
    systemd-run --user --scope -p MemoryMax=40G python3 $S/allocprof.py $S/$side-tree $S/work/$side-n$1-2k/m $S/alloc-$side-n$1 900000 200 > $S/results/alloc-$side-n$1.out 2>&1
  done
done > $S/runs.out 2>&1
echo ALLDONE > $S/results/all.done

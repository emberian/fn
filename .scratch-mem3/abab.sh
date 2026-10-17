#!/bin/sh
# usage: abab.sh TAG LAUNCHER "arms..."   2 rounds interleaved, 1000 POSTs
cd /tank/fn/scratch/n-mem3
T=$1; L=$2; shift 2
for k in 1 2; do for a in "$@"; do
  echo "$T r$k arm$a $(uptime)" >> $T-uptime.log
  SWARM_MEM_MAX=16G timeout 1500 swarm-build python3 mem3.py $L /tank/fn/scratch/n-mem3/$T-r$k-a$a $a 1000 > $T-r$k-a$a.out 2>&1
  tail -c 300 $T-r$k-a$a.out >> $T.progress
done; done; echo done >> $T.progress

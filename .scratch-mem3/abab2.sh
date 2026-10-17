#!/bin/sh
# usage: abab2.sh TAG LAUNCHER ARMS...  : 2 rounds, MEM3_LANE_DIR set
cd /tank/fn/scratch/n-mem3
T=$1; L=$2; shift 2
export MEM3_LANE_DIR=/tank/fn/scratch/n-mem3/lane
for k in 1 2; do for a in "$@"; do
  echo "$T r$k arm$a $(uptime)" >> $T-uptime.log
  SWARM_MEM_MAX=16G timeout 1500 swarm-build python3 mem3.py $L /tank/fn/scratch/n-mem3/$T-r$k-a$a $a 1000 > $T-r$k-a$a.out 2>&1
done; done; echo done > $T.done

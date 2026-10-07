#!/bin/sh
# ABABAB, 1000 POSTs each, from /tank/fn/scratch/n-mem7 ; usage: abab.sh TAG
cd /tank/fn/scratch/n-mem7
for k in 1 2 3; do for s in 64 8; do
  SWARM_MEM_MAX=16G timeout 1500 swarm-build python3 mem7.py /tank/fn/scratch/n-mem7/$1-r$k-s$s $s 1000 2>&1 | tail -1 | cut -c1-300
done; done

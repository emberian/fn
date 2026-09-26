#!/bin/sh
set -u
sh /tank/fn/scratch/served-path-scale-2/m/prof-build.sh /tank/fn/scratch/served-path-scale-2/native-g1/tree > /tank/fn/scratch/served-path-scale-2/m/prof-build-g1.out 2>&1; echo "prof rc=$?" >> /tank/fn/scratch/served-path-scale-2/m/chain1.log
sh /tank/fn/scratch/served-path-scale-2/m/post.sh g1 /tank/fn/scratch/served-path-scale-2/native-g1/tree 10000; echo "post done" >> /tank/fn/scratch/served-path-scale-2/m/chain1.log
for side in base g1; do
  T=/tank/fn/scratch/served-path-scale-2/native-$side/tree; [ $side = base ] && T=/tank/fn/scratch/served-path-scale-2/native-base-a931ed8d/tree
  rm -rf /tank/fn/scratch/served-path-scale-2/m/greet10k-$side
  (cd $T && python3 /tank/fn/scratch/served-path-scale-2/m/greet.py /tank/fn/scratch/served-path-scale-2/m/store-g1-n10000 /tank/fn/scratch/served-path-scale-2/m/greet10k-$side 32 > /tank/fn/scratch/served-path-scale-2/m/greet10k-$side.json 2> /tank/fn/scratch/served-path-scale-2/m/greet10k-$side.err); echo "greet $side rc=$? $(uptime)" >> /tank/fn/scratch/served-path-scale-2/m/chain1.log
done
echo "rc=chain1-done" >> /tank/fn/scratch/served-path-scale-2/m/chain1.log

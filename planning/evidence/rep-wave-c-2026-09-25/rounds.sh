#!/bin/sh
# usage: rounds.sh -- three alternated rounds, base then after, on the built images
S=/tank/fn/scratch/rep-wave-c
cd $S
for r in 1 2 3; do
  for L in base after; do
    sh $S/round.sh $L $r > $S/round-$L-$r.out 2>&1
  done
done
echo ALLDONE > $S/all.done

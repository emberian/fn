#!/bin/sh
S=/tank/fn/scratch/rep-octets
cd $S
sh $S/setup.sh $S/after-tree after > $S/after-setup.log 2>&1
if ! grep -q BUILD-OK $S/after-build.log; then echo SETUP-FAILED after > $S/all.done; exit 1; fi
for r in 1 2 3; do
  for L in base after; do
    sh $S/round.sh $L $r > $S/round-$L-$r.out 2>&1
  done
done
echo ALLDONE > $S/all.done

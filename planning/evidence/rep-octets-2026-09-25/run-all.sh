#!/bin/sh
S=/tank/fn/scratch/rep-octets
cd $S
sh $S/setup.sh $S/base-tree base > $S/base-setup.log 2>&1 &
sh $S/setup.sh $S/after-tree after > $S/after-setup.log 2>&1 &
wait
for L in base after; do
  if ! grep -q BUILD-OK $S/$L-build.log || grep -q "rc=[1-9]" $S/$L-setup.log; then echo SETUP-FAILED $L > $S/all.done; exit 1; fi
done
for r in 1 2 3; do
  for L in base after; do
    sh $S/round.sh $L $r > $S/round-$L-$r.out 2>&1
  done
done
echo ALLDONE > $S/all.done

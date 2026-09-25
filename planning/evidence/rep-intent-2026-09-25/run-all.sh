#!/bin/sh
S=/tank/fn/scratch/rep-intent
cd $S
sh $S/setup2.sh $S/base-tree base > $S/base-setup.log 2>&1 &
sh $S/setup2.sh $S/after-tree after > $S/after-setup.log 2>&1 &
wait
for L in base after; do
  if ! grep -q BUILD-OK $S/$L-setup.log || grep -q "rc=[1-9]" $S/$L-setup.log; then echo SETUP-FAILED $L > $S/all.done; exit 1; fi
done
for r in 1 2 3; do
  for L in base after; do
    sh $S/prof.sh $L 120 48 > $S/prof-$L-r$r.out 2>&1
    cp $S/prof-$L-n120/sprof/flat.txt $S/post-$L-n120-r$r-flat.txt 2>/dev/null
    cp $S/prof-$L-n120/sprof/graph.txt $S/post-$L-n120-r$r-graph.txt 2>/dev/null
  done
done
sh $S/measure-shm.sh $S/base-tree base > $S/shm-base.out 2>&1
sh $S/measure-shm.sh $S/after-tree after > $S/shm-after.out 2>&1
echo ALLDONE > $S/all.done

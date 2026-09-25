#!/bin/sh
S=/tank/fn/scratch/rep-records-2
cd $S
while ! grep -q "BUILD-OK\|rc=[1-9]" $S/after-setup.log 2>/dev/null; do sleep 20; done
if grep -q "rc=[1-9]" $S/after-setup.log; then echo SETUP-FAILED > $S/all.done; exit 1; fi
for r in 1 2 3; do
  for L in base after; do
    sh $S/prof.sh $L 120 48 > $S/prof-$L-r$r.out 2>&1
    cp $S/prof-$L-n120/sprof/flat.txt $S/post-$L-n120-r$r-flat.txt 2>/dev/null
    cp $S/prof-$L-n120/sprof/graph.txt $S/post-$L-n120-r$r-graph.txt 2>/dev/null
  done
done
for r in 1 2; do
  sh $S/measure-shm.sh base $r > $S/shm-base-r$r.out 2>&1
  sh $S/measure-shm.sh after $r > $S/shm-after-r$r.out 2>&1
done
echo ALLDONE > $S/all.done

#!/bin/sh
S=/tank/fn/scratch/advance-projection
cd $S
for r in 1 2 3; do
  for L in base after; do
    sh $S/prof.sh $L 120 48 > $S/prof-$L-r$r.out 2>&1
    cp $S/prof-$L-n120/sprof/flat.txt $S/post-$L-n120-r$r-flat.txt 2>/dev/null
    cp $S/prof-$L-n120/sprof/graph.txt $S/post-$L-n120-r$r-graph.txt 2>/dev/null
  done
done
sh $S/measure.sh $S/base-tree base > $S/measure-base.out 2>&1
sh $S/measure.sh $S/after-tree after > $S/measure-after.out 2>&1
echo DONE > $S/meas.done

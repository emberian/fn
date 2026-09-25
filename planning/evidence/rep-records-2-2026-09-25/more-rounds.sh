#!/bin/sh
S=/tank/fn/scratch/rep-records-2
cd $S
for r in 4 5 6 7 8 9 10 11 12 13; do
  for L in base after; do
    sh $S/prof.sh $L 120 48 > $S/prof-$L-r$r.out 2>&1
    cp $S/prof-$L-n120/sprof/flat.txt $S/post-$L-n120-r$r-flat.txt 2>/dev/null
    cp $S/prof-$L-n120/sprof/graph.txt $S/post-$L-n120-r$r-graph.txt 2>/dev/null
  done
done
echo DONE > $S/more.done

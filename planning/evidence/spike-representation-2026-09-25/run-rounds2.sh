#!/bin/sh
S=/tank/fn/scratch/spike-representation
C="--census /tank/fn/scratch/rep-heap/census.lisp"
for r in 1 2 3; do for o in 2048 32768; do for L in base after; do sh $S/hbox-prof.sh $L $r 120 $o 48; done; done; done
echo PROF-120-DONE
for o in 2048 32768; do for L in base after; do sh $S/hbox-measure.sh $L 1 1000 $o $C --reopen-timeout 7200; done; done
echo ROUNDS-1000-DONE
for r in 1 2; do for o in 2048 32768; do for L in base after; do sh $S/hbox-measure.sh $L $r 10000 $o --skip-reopen; done; done; done
echo ROUNDS-10000-DONE
for o in 2048 32768; do for L in base after; do sh $S/hbox-prof.sh $L 1 10000 $o 200; done; done
echo PROF-10000-DONE
for L in base after; do sh $S/hbox-measure.sh $L 9 10000 2048 --reopen-timeout 10800; done
echo REOPEN-10000-DONE
echo ALL-DONE

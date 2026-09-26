#!/bin/sh
S=/tank/fn/scratch/rep-wave-d
for spec in "n1000-2k 1000 2048" "n1000-32k 1000 32768" "n10000-2k 10000 2048" "n10000-32k 10000 32768"; do set -- $spec; sh $S/run.sh $1 $2 $3; done
echo shm-done-already
echo ALLDONE > $S/results/all.done

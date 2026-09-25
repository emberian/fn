#!/bin/sh
S=/tank/fn/scratch/representation
cd $S
while ! grep -q BUILD-OK $S/after-setup.log 2>/dev/null; do sleep 20; done
if grep -q "rc=[1-9]" $S/after-setup.log; then echo SETUP-FAILED > $S/all.done; exit 1; fi
sh $S/meas-all.sh > $S/meas-all.out 2>&1
sh $S/measure-shm.sh $S/base-tree base > $S/shm-base.out 2>&1
sh $S/measure-shm.sh $S/after-tree after > $S/shm-after.out 2>&1
echo ALLDONE > $S/all.done

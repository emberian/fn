#!/bin/sh
S=/tank/fn/scratch/rep-records-2
cd $S
while [ ! -f run2.done ]; do sleep 30; done
sh setup3.sh $S/after3-tree after3 > after3-setup.log 2>&1
grep -q BUILD-OK after3-setup.log || { echo SETUP-FAILED > run3.done; exit 1; }
sha256sum after3-tree/build/fn-host-developer* > images3.sha256
for r in 4 5 6; do
  for L in base2 after3; do
    sh shm2.sh $L $S/$L-tree $r 64
  done
done
uptime > run3.done

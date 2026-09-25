#!/bin/sh
S=/tank/fn/scratch/rep-records-2
cd $S
sh setup3.sh $S/base2-tree base2 > base2-setup.log 2>&1
grep -q BUILD-OK base2-setup.log || { echo SETUP-FAILED > run2.done; exit 1; }
sha256sum base2-tree/build/fn-host-developer* after-tree/build/fn-host-developer* after2-tree/build/fn-host-developer* > images2.sha256
for r in 1 2 3 4 5 6 7 8 9 10 11 12 13; do
  for L in base2 after after2; do
    sh prof2.sh $L $S/$L-tree 120 48 $r
  done
done
for r in 1 2 3; do
  for L in base2 after after2; do
    sh shm2.sh $L $S/$L-tree $r 64
  done
done
uptime > run2.done

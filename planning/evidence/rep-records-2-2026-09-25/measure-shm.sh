#!/bin/sh
# usage: measure-shm.sh LABEL ROUND
L=$1; R=$2; S=/tank/fn/scratch/rep-records-2
if [ "$L" = base ]; then T=/tank/fn/scratch/rep-intent/base-tree; else T=$S/after-tree; fi
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
cd $S
for n in 16 50 120; do
  rm -rf /dev/shm/rr2-$L-n$n
  python3 $S/after-tree/tools/msgid_measure.py --image $T/build/fn-host-developer --work /dev/shm/rr2-$L-n$n --articles $n --samples 16 --json $S/shm-$L-n$n-r$R.json > $S/shm-$L-n$n-r$R.log 2>&1 </dev/null
  echo n=$n rc=$?; grep -E median $S/shm-$L-n$n-r$R.log | grep -v post_ | tr '\n' ';'; echo
  rm -rf /dev/shm/rr2-$L-n$n
done
uptime

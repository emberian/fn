#!/bin/sh
# usage: shm2.sh LABEL TREE ROUND SAMPLES
L=$1; T=$2; R=$3; K=$4; S=/tank/fn/scratch/rep-records-2
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
rm -rf /dev/shm/rr2b-$L
python3 $S/after2-tree/tools/msgid_measure.py --image $T/build/fn-host-developer --work /dev/shm/rr2b-$L --articles 120 --samples $K --json $S/s2-$L-n120-r$R.json > $S/s2-$L-n120-r$R.log 2>&1 </dev/null
echo $L r$R rc=$?
rm -rf /dev/shm/rr2b-$L

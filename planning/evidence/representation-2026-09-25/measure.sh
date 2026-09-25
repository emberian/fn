#!/bin/sh
# usage: measure.sh TREE LABEL
T=$1; L=$2; S=/tank/fn/scratch/representation
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
cd $S
for n in 16 50 120; do
  rm -rf $S/$L-n$n
  python3 $S/after-tree/tools/msgid_measure.py --image $T/build/fn-host-developer --work $S/$L-n$n --articles $n --samples 16 --json $S/$L-n$n.json > $S/$L-n$n.log 2>&1 </dev/null
  echo n=$n rc=$?; grep -E "median" $S/$L-n$n.log | grep -v post_ | tr '\n' ';'; echo
done
uptime

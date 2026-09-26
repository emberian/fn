#!/bin/sh
# usage: cross.sh LABEL TREE STORE -- `store STORE recover` on a copy of STORE with TREE s developer image; the open report
L=$1; T=$2; S=$3; M=/tank/fn/scratch/served-path-scale-2/m
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib ACL2_CUSTOMIZATION=NONE
rm -rf $M/cross-$L; mkdir -p $M/cross-$L; cp -a $S $M/cross-$L/store
cd $T; start=$(date +%s.%N)
$T/build/fn-host-developer --fn store $M/cross-$L/store recover > $M/cross-$L.out 2>&1
rc=$?; end=$(date +%s.%N)
echo "cross $L rc=$rc seconds=$(echo "$end - $start" | bc) $(grep -o "open=[^ ]*\( [a-z]*=[^ ]*\)*" $M/cross-$L.out | tail -1) load=$(cut -d" " -f1 /proc/loadavg)" >> $M/cross.log
rm -rf $M/cross-$L

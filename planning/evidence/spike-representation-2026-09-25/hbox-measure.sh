#!/bin/sh
# usage: hbox-measure.sh LABEL ROUND N OCTETS   (LABEL = base | after)
L=$1; R=$2; N=$3; O=$4; shift 4; S=/tank/fn/scratch/spike-representation
T=$S/$L-tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
W=/dev/shm/sr-$L-n$N-o$O-r$R; rm -rf $W
python3 $S/after-tree/tools/rep_measure.py --image $T/build/fn-host-developer --work $W --articles $N --octets $O --samples 16 "$@" --json $S/m-$L-n$N-o$O-r$R.json > $S/m-$L-n$N-o$O-r$R.log 2>&1 </dev/null
echo "$L r$R n=$N o=$O rc=$?"; grep -E "median|load_seconds|reopen" $S/m-$L-n$N-o$O-r$R.log | head -8
rm -rf $W

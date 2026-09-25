#!/bin/sh
# usage: hbox-prof.sh LABEL ROUND N OCTETS K
L=$1; R=$2; N=$3; O=$4; K=$5; S=/tank/fn/scratch/spike-representation; T=$S/$L-tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
W=/dev/shm/srp-$L-n$N-o$O-r$R; rm -rf $W
python3 $S/prof_post2.py $S/after-tree/tools --image $T/build/fn-host-developer-prof --work $W --articles $N --octets $O --stats $K > $S/p-$L-n$N-o$O-r$R.out 2>&1 </dev/null
echo "$L r$R n=$N o=$O rc=$? $(cat $S/p-$L-n$N-o$O-r$R.out | tail -1)"
cp $W/sprof/flat.txt $S/post-$L-n$N-o$O-r$R-flat.txt 2>/dev/null; cp $W/sprof/graph.txt $S/post-$L-n$N-o$O-r$R-graph.txt 2>/dev/null
rm -rf $W

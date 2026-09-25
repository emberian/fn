#!/bin/sh
# usage: prof2.sh LABEL TREE N POSTS ROUND
L=$1; T=$2; N=$3; K=$4; R=$5; S=/tank/fn/scratch/rep-records-2
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
rm -rf $S/prof2-$L-n$N
python3 $S/prof_post.py $S/after2-tree/tools --image $T/build/fn-host-developer-prof --work $S/prof2-$L-n$N --articles $N --stats $K </dev/null > $S/p2-$L-r$R.out 2>&1
cp $S/prof2-$L-n$N/sprof/flat.txt $S/p2-$L-n$N-r$R-flat.txt; cp $S/prof2-$L-n$N/sprof/graph.txt $S/p2-$L-n$N-r$R-graph.txt

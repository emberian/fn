#!/bin/sh
# usage: prof.sh LABEL N POSTS
L=$1; N=$2; K=$3; S=/tank/fn/scratch/rep-sha256; T=$S/$L-tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
rm -rf $S/prof-$L-n$N
python3 $S/prof_post.py $S/after-tree/tools --image $T/build/fn-host-developer-prof --work $S/prof-$L-n$N --articles $N --stats $K </dev/null
head -3 $S/prof-$L-n$N/sprof/flat.txt

#!/bin/sh
# usage: prof.sh LABEL N POSTS   (base = rep-intent's dev 0a608298 image, read only)
L=$1; N=$2; K=$3; S=/tank/fn/scratch/rep-records-2
if [ "$L" = base ]; then T=/tank/fn/scratch/rep-intent/base-tree; else T=$S/after-tree; fi
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
rm -rf $S/prof-$L-n$N
python3 $S/prof_post.py $S/after-tree/tools --image $T/build/fn-host-developer-prof --work $S/prof-$L-n$N --articles $N --stats $K </dev/null
head -3 $S/prof-$L-n$N/sprof/flat.txt

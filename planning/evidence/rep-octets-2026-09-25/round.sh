#!/bin/sh
# usage: round.sh LABEL ROUND -- one measured round on one image: sprof and call-count profiles at N=120, then the sized loads
L=$1; R=$2; S=/tank/fn/scratch/rep-octets; T=$S/$L-tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
TOOLS=$S/after-tree/tools
W=/dev/shm/rep-octets-$L-r$R; rm -rf $W; mkdir -p $W
python3 $S/load_sized.py $TOOLS --image $T/build/fn-host-developer-prof --work $W/sprof120 --articles 120 --payload-octets 160 --stats 48 --json $S/$L-r$R-sprof-n120.json </dev/null
cp $W/sprof120/sprof/flat.txt $S/post-$L-n120-r$R-flat.txt 2>/dev/null; cp $W/sprof120/sprof/graph.txt $S/post-$L-n120-r$R-graph.txt 2>/dev/null
FN_DPROF=fnn-octet-list,fnn-octets-fill,fnn-owner-attempt,fn-pb-existing-action,fn-pbb-existing-action,fn-owner-prepare,fn-owner-prepare-buffer python3 $S/load_sized.py $TOOLS --image $T/build/fn-host-developer-prof --work $W/dprof120 --articles 120 --payload-octets 160 --stats 48 --json $S/$L-r$R-dprof-n120.json </dev/null
cp $W/dprof120/sprof/dprof.txt $S/calls-$L-n120-r$R.txt 2>/dev/null
for P in 2048 32768; do
  for N in 120 10000; do
    rm -rf $W/sized; python3 $S/load_sized.py $TOOLS --image $T/build/fn-host-developer --work $W/sized --articles $N --payload-octets $P --json $S/$L-r$R-p$P-n$N.json </dev/null
  done
done
rm -rf $W
uptime

#!/bin/sh
# usage: round.sh LABEL ROUND -- one measured round on one image: call counts and a CPU profile at N=120, then the sized loads under the default profile
L=$1; R=$2; S=/tank/fn/scratch/rep-wave-c; T=$S/$L-tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
TOOLS=$S/base-tree/tools
W=/dev/shm/rwc-$L-r$R; rm -rf $W; mkdir -p $W
python3 $S/load_prof.py $TOOLS --image $T/build/fn-host-developer-prof --work $W/count --articles 120 --payload-octets 2048 --stats 48 --count $S/count.lisp --json $S/$L-r$R-count-p2048-n120.json </dev/null
python3 $S/load_prof.py $TOOLS --image $T/build/fn-host-developer-prof --work $W/sprof --articles 120 --payload-octets 32768 --stats 48 --json $S/$L-r$R-sprof-p32768-n120.json </dev/null
cp $W/sprof/sprof/flat.txt $S/post-$L-p32768-n120-r$R-flat.txt 2>/dev/null; cp $W/sprof/sprof/graph.txt $S/post-$L-p32768-n120-r$R-graph.txt 2>/dev/null
for P in 2048 32768; do
  for N in 120 10000; do
    rm -rf $W/sized; python3 $S/load_prof.py $TOOLS --image $T/build/fn-host-developer --work $W/sized --articles $N --payload-octets $P --json $S/$L-r$R-p$P-n$N.json </dev/null
  done
done
rm -rf $W
uptime

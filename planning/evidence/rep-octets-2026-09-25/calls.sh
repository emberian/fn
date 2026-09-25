#!/bin/sh
S=/tank/fn/scratch/rep-octets; TOOLS=$S/after-tree/tools
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
for r in 1 2 3; do for L in base after; do
  W=/dev/shm/rep-octets-calls-$L-$r; rm -rf $W; mkdir -p $W
  FN_DPROF=fnn-octet-list,fnn-octets-fill,fnn-owner-attempt,fnn-metadata,fn-pb-existing-action,fn-pbb-existing-action,fn-owner-prepare,fn-owner-prepare-buffer,fn-owner-chunk python3 $S/load_sized.py $TOOLS --image $S/$L-tree/build/fn-host-developer-prof --work $W/d --articles 120 --payload-octets 160 --stats 48 --json $S/calls-$L-r$r.json </dev/null > $S/calls-$L-r$r.out 2>&1
  cp $W/d/owner.stderr $S/stderr-$L-r$r.txt; rm -rf $W
done; done
echo CALLSDONE > $S/calls.done

#!/bin/sh
# usage: fixture.sh LABEL TREE K -- fixture_open.py over a copy of the 20,000 fixture with TREE s developer image
L=$1; T=$2; K=$3; M=/tank/fn/scratch/served-path-scale-2/m
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
rm -rf $M/open-$L
cd $T && python3 planning/evidence/served-path-scale-2026-09-26/fixture_open.py /tank/fn/scratch/fixtures/chain-20000-8cc3cd4c $M/open-$L $K > $M/open-$L.log 2>&1
echo "rc=$?" >> $M/open-$L.log; uptime >> $M/open-$L.log

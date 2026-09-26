#!/bin/sh
# usage: greet.sh LABEL TREE STORE K
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
rm -rf /tank/fn/scratch/served-path-scale-2/m/greet-$1
cd $2 && python3 /tank/fn/scratch/served-path-scale-2/m/greet.py $3 /tank/fn/scratch/served-path-scale-2/m/greet-$1 $4 > /tank/fn/scratch/served-path-scale-2/m/greet-$1.json 2> /tank/fn/scratch/served-path-scale-2/m/greet-$1.err
echo "greet $1 rc=$? $(uptime)" >> /tank/fn/scratch/served-path-scale-2/m/greet.log

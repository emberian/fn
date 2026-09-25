#!/bin/sh
# usage: run-prof.sh LABEL TREE IMAGE [extra]
L=$1; T=$2; I=$3; shift 3
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib PYTHONDONTWRITEBYTECODE=1
rm -rf /tank/fn/scratch/signed-path/work-$L
systemd-run --user --scope -q -p MemoryMax=24G python3 /tank/fn/scratch/signed-path/prof_signed.py $T $I /tank/fn/scratch/signed-path/work-$L "$@"

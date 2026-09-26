#!/bin/sh
# perf-ledger driver: each phase its own scope, one at a time; tmpfs stores.
S=/tank/fn/scratch/perf-ledger; T=$S/tree; W=/dev/shm/perf-ledger
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
cd $T
mkdir -p $W $S/results
ph() { mem=$1; shift; echo "== $* $(date -u +%H:%M:%SZ) load $(cut -d' ' -f1-3 /proc/loadavg)"; systemd-run --user --scope -q -p MemoryMax=$mem -p MemorySwapMax=0 python3 $S/perf.py "$@" > $S/results/$1-$(date -u +%H%M%S).out 2>&1; echo "   rc=$?"; }
for step in ${STEPS:-load post-cpu post-alloc reads greet ckptopen big chain}; do
  case $step in
    load) rm -rf $W/n10k; ph 24G load $W/n10k 10000 2048 ;;
    post-cpu) ph 24G post $W/n10k 200 cpu ;;
    post-alloc) ph 24G post $W/n10k 200 alloc ;;
    reads) ph 24G reads $W/n10k ;;
    greet) ph 24G greet $W/n10k 64 ;;
    ckptopen) ph 24G ckptopen $W/n10k ;;
    big) rm -rf $W/big; ph 24G big $W/big ;;
    chain) rm -rf $W/chain; ph 40G chain $W/chain /tank/fn/scratch/fixtures/chain-20000-8cc3cd4c ;;
  esac
done
echo DRIVE-DONE $(date -u +%H:%M:%SZ)

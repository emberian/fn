#!/bin/sh
# post-identity-index: before/after POST cost on hbox.  Run from anywhere:
#   sh run.sh    (the lane's measure dir holds this file and postmeasure.py)
set -u
S=/tank/fn/scratch/post-identity-index; M=$S/measure; W=/dev/shm/pidx
AT=$S/native-r1/tree; A=$AT/build/fn-host-developer
B=/tank/fn/scratch/throughput-gate/native-img-6407de336/tree/build/fn-host-developer
F10=/tank/fn/scratch/fixtures/n10k-2k; F1=/tank/fn/scratch/fixtures/n1k-2k
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
mkdir -p $W $M/results
sha256sum $A $A.core $B $B.core | tee $M/results/images.sha256
( cd $F10 && sha256sum -c --quiet SHA256SUMS ) && echo fixture-n10k-ok
cd $AT
ph() { mem=$1; shift; echo "== $* $(date -u +%H:%M:%SZ) load $(cut -d' ' -f1-3 /proc/loadavg)"
  systemd-run --user --scope -q -p MemoryMax=$mem -p MemorySwapMax=0 python3 $M/postmeasure.py "$@"; echo "   rc=$?"; }
if [ ! -f $F1/SHA256SUMS ]; then
  rm -rf $W/n1k; ph 24G load $B $W/n1k 1000
  mkdir -p $F1 && cp -a $W/n1k/store $F1/store && cp $W/n1k/load.json $F1/origin.json
  printf 'N = 1,000 x 2,048-octet articles in fn.test (default profile), POSTed by post-identity-index postmeasure.py load\nwith the throughput gate developer image of dev 6407de336; msgids as rep_measure.article(i), i = number - 1.\n' > $F1/README.txt
  ( cd $F1 && find store -type f | sort | xargs sha256sum > SHA256SUMS )
fi
( cd $F1 && sha256sum -c --quiet SHA256SUMS ) && echo fixture-n1k-ok
for round in 1 2; do
  for n in 1k 10k; do
    if [ $n = 1k ]; then F=$F1; else F=$F10; fi
    ph 24G post $B $F/store $W/before-$n-$round before-$n-$round 200; cp $W/before-$n-$round.json $M/results/
    ph 24G post $A $F/store $W/after-$n-$round after-$n-$round 200; cp $W/after-$n-$round.json $M/results/
    rm -rf $W/before-$n-$round $W/after-$n-$round
  done
done
ph 24G post $A $F10/store $W/after-10k-cpu after-10k-cpu 200 cpu; cp $W/after-10k-cpu.json $M/results/; cp $W/after-10k-cpu/sprof/flat.txt $M/results/after-10k-cpu-flat.txt; cp $W/after-10k-cpu/sprof/graph.txt $M/results/after-10k-cpu-graph.txt
ph 24G post $B $F10/store $W/before-10k-cpu before-10k-cpu 200 cpu; cp $W/before-10k-cpu.json $M/results/; cp $W/before-10k-cpu/sprof/flat.txt $M/results/before-10k-cpu-flat.txt; cp $W/before-10k-cpu/sprof/graph.txt $M/results/before-10k-cpu-graph.txt
rm -rf $W
echo MEASURE-DONE $(date -u +%H:%M:%SZ)

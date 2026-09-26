#!/bin/sh
# over-number-index: the fixture n10k-2k and the BEFORE reads on the perf-ledger image (dev f314a5a3).
set -u
S=/tank/fn/scratch/over-number-index; T=/tank/fn/scratch/perf-ledger/tree; IMG=$T/build/fn-host-developer
F=/tank/fn/scratch/fixtures/n10k-2k
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
cd $T
if [ ! -f $F/SHA256SUMS ]; then
  rm -rf /dev/shm/oni-load
  systemd-run --user --scope -q -p MemoryMax=24G -p MemorySwapMax=0 python3 $S/measure.py load $T $IMG /dev/shm/oni-load 10000 > $S/load.out 2>&1; echo load rc=$?
  mkdir -p $F && cp -a /dev/shm/oni-load/store $F/store && cp /dev/shm/oni-load/load.json $F/origin.json
  printf 'N = 10,000 x 2,048-octet articles in fn.test (default profile), POSTed by over-number-index measure.py load\nwith the perf-ledger developer image (dev f314a5a3, core addf58ae...); msgids <t17-%%06d@example.invalid>, i = number - 1.\n' > $F/README.txt
  (cd $F && find store -type f | sort | xargs sha256sum > SHA256SUMS && sha256sum README.txt origin.json >> SHA256SUMS)
  rm -rf /dev/shm/oni-load
fi
systemd-run --user --scope -q -p MemoryMax=24G -p MemorySwapMax=0 python3 $S/measure.py reads $T $IMG $F/store /dev/shm/oni-before before > $S/before.out 2>&1; echo before rc=$?
cp /dev/shm/oni-before-before.json $S/ ; rm -rf /dev/shm/oni-before
echo BEFORE-DONE

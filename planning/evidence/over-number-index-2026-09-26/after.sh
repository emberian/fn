#!/bin/sh
# over-number-index: AFTER on the lane image (native-r1), then both images at N = 20,000 (chain fixture).
set -u
S=/tank/fn/scratch/over-number-index; LT=$S/native-r1/tree; BT=/tank/fn/scratch/perf-ledger/tree
LIMG=$LT/build/fn-host-developer; BIMG=$BT/build/fn-host-developer
F=/tank/fn/scratch/fixtures/n10k-2k; C=/tank/fn/scratch/fixtures/chain-20000-8cc3cd4c
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
sha256sum $LIMG $LIMG.core $BIMG $BIMG.core > $S/images.sha256
cd $LT
( cd $F && sha256sum -c --quiet SHA256SUMS ) && echo fixture-ok
run() { mem=$1; tree=$2; img=$3; src=$4; label=$5
  echo "== $label $(date -u +%H:%M:%SZ) load $(cut -d' ' -f1-3 /proc/loadavg)"
  systemd-run --user --scope -q -p MemoryMax=$mem -p MemorySwapMax=0 python3 $S/measure.py reads $tree $img $src /dev/shm/oni-$label $label > $S/$label.out 2>&1; echo "   rc=$?"
  cp /dev/shm/oni-$label-$label.json $S/ 2>/dev/null; rm -rf /dev/shm/oni-$label
}
run 24G $LT $LIMG $F/store after
run 24G $BT $BIMG $F/store before2
run 40G $LT $LIMG $C/store after20k
run 40G $BT $BIMG $C/store before20k
echo AFTER-DONE

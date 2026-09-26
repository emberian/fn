#!/bin/sh
# service-envelope: the envelope rows (tools/service_envelope.py), each step its
# own unit senv-* under MemoryMax=40G and RuntimeMaxSec=1800, one at a time.
# Run inside the light driver unit senv-driver-TAG.
# usage: envelope.sh IMAGE REV TAG "10k 100k"
S=/tank/fn/scratch/service-envelope
IMG=$1; REV=$2; TAG=$3; PARTS=$4
T="python3 $S/client/tools/service_envelope.py"
L=$S/logs; mkdir -p $L /dev/shm/senv
unit() {  # unit NAME CMD...: one senv-NAME unit, waited; its exit in $L/NAME.rc
  name=$1; shift
  systemd-run --user --quiet --collect --wait --unit=senv-$name -p MemoryMax=40G -p MemorySwapMax=0 \
    -p RuntimeMaxSec=1800 sh -c "$* > $L/$name.log 2>&1; echo \$? > $L/$name.rc"
  echo "$(date -u +%FT%TZ) senv-$name rc=$(cat $L/$name.rc 2>/dev/null || echo none)" >> $L/driver.log
}
M="$T measure --image $IMG --revision $REV"
for part in $PARTS; do
case $part in
10k)
# N = 10,000: one preload on tmpfs, cloned to tmpfs and to the pool.
unit load10k-$TAG "$T load --image $IMG --dir /dev/shm/senv/src10k-$TAG --to 10000"
unit clone10k-$TAG "$T clone --dir /dev/shm/senv/src10k-$TAG --to-dir /dev/shm/senv/t10k-$TAG && $T clone --dir /dev/shm/senv/src10k-$TAG --to-dir $S/z10k-$TAG"
unit t10k-$TAG "$M --dir /dev/shm/senv/t10k-$TAG --label t10k-$TAG --json $S/t10k-$TAG.json --steps latency,checkpoint,restart,rate"
# ZFS: not while marker-sharing measures (its units name marker).
while systemctl --user list-units --state=running --no-legend --plain | grep -qi marker; do sleep 60; done
unit z10k-$TAG "$M --dir $S/z10k-$TAG --label z10k-$TAG --json $S/z10k-$TAG.json --steps latency,checkpoint,restart,rate"
rm -rf /dev/shm/senv/src10k-$TAG /dev/shm/senv/t10k-$TAG
;;
100k)
# N = 100,000, tmpfs only, once: load and the warm rows on the loading owner;
# the full reopen; the checkpoint (PKT-191: the capture exhausted 32 GB) and
# the checkpoint-assisted reopen, then the rates.
D=/dev/shm/senv/t100k-$TAG
for p in a b c; do
  unit t100k-load-$p-$TAG "$M --dir $D --label t100k-load-$p-$TAG --json $S/t100k-load-$p-$TAG.json --load-to 100000 --steps load,latency --budget 1200 --row-budget 60"
  [ "$(cat $L/t100k-load-$p-$TAG.rc)" = 75 ] || break
done
unit t100k-reopen-$TAG "$M --dir $D --label t100k-reopen-$TAG --json $S/t100k-reopen-$TAG.json --steps restart --open-timeout 1700"
unit t100k-ckpt-$TAG "$M --dir $D --label t100k-ckpt-$TAG --json $S/t100k-ckpt-$TAG.json --steps checkpoint,restart,rate --open-timeout 1200"
;;
esac
done
echo "$(date -u +%FT%TZ) done $TAG $PARTS" >> $L/driver.log

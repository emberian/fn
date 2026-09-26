#!/bin/sh
# service-envelope: N = 100,000 continuation driver (replaces envelope.sh's
# 100k part, whose three load units could not reach 100,000 at the measured
# growth of the POST cost; each unit stays under 30 minutes).
# usage: envelope-100k.sh IMAGE REV TAG   (run in senv-driver-100k-TAG)
S=/tank/fn/scratch/service-envelope
IMG=$1; REV=$2; TAG=$3
T="python3 $S/client/tools/service_envelope.py"
L=$S/logs; D=/dev/shm/senv/t100k-$TAG
unit() {
  name=$1; shift
  systemd-run --user --quiet --collect --wait --unit=senv-$name -p MemoryMax=40G -p MemorySwapMax=0 \
    -p RuntimeMaxSec=1800 sh -c "$* > $L/$name.log 2>&1; echo \$? > $L/$name.rc"
  echo "$(date -u +%FT%TZ) senv-$name rc=$(cat $L/$name.rc 2>/dev/null || echo none)" >> $L/driver.log
}
M="$T measure --image $IMG --revision $REV"
while systemctl --user is-active --quiet senv-t100k-load-a-$TAG; do sleep 30; done
echo "$(date -u +%FT%TZ) senv-t100k-load-a-$TAG rc=$(cat $L/t100k-load-a-$TAG.rc 2>/dev/null || echo none)" >> $L/driver.log
last=a
for p in b c d e f g h i; do
  [ "$(cat $L/t100k-load-$last-$TAG.rc 2>/dev/null)" = 75 ] || break
  unit t100k-load-$p-$TAG "$M --dir $D --label t100k-load-$p-$TAG --json $S/t100k-load-$p-$TAG.json --load-to 100000 --steps load,latency --budget 1200 --row-budget 60 --open-timeout 500"
  last=$p
done
if [ "$(cat $L/t100k-load-$last-$TAG.rc 2>/dev/null)" = 0 ]; then
  unit t100k-reopen-$TAG "$M --dir $D --label t100k-reopen-$TAG --json $S/t100k-reopen-$TAG.json --steps restart --open-timeout 1700"
  unit t100k-ckpt-$TAG "$M --dir $D --label t100k-ckpt-$TAG --json $S/t100k-ckpt-$TAG.json --steps checkpoint,restart,rate --open-timeout 1200"
  unit t100k-fullclone-$TAG "$T clone --drop-checkpoint --dir $D --to-dir $D-full"
  unit t100k-full-$TAG "$M --dir $D-full --label t100k-full-$TAG --json $S/t100k-full-$TAG.json --steps restart --open-timeout 1700"
  rm -rf $D-full
fi
echo "$(date -u +%FT%TZ) done 100k $TAG last=$last" >> $L/driver.log

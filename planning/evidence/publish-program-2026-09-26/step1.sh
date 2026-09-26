#!/bin/sh
# Step 1 (measure first), the base image 17ff24aa alone: the sync-family
# syscall counts of `store probe 100` on tmpfs and on ZFS; the N = 10,000 POST
# curve at 2 KiB under the default profile with the in-process profiler
# (post_n.py --prof, tmpfs: the stall question); then the matched probe/POST
# rows at N = 1,000 and N = 10,000 on tmpfs and ZFS (measure.sh).
set -u
S=/tank/fn/scratch/publish-program; H=$S/harness; OUT=$S/step1; T=$S/native-base-17ff24aa/tree
mkdir -p $OUT
export LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib ACL2_CUSTOMIZATION=NONE FN_CLIENT_TREE=$T
log() { echo "$(date -u +%FT%TZ) load=$(cut -d' ' -f1-3 /proc/loadavg) $*" >> $OUT/step1.log; }
log "start pool=$(zfs list -H -o used,avail tank | tr '\t' '/') arc=$(awk '/^size /{printf "%.1fG", $3/1073741824}' /proc/spl/kstat/zfs/arcstats)"
log "syncs tmpfs: $(sh $H/syncs.sh base $T 100 tmpfs $OUT 2>&1 | tail -1)"
log "syncs zfs: $(sh $H/syncs.sh base $T 100 zfs $OUT 2>&1 | tail -1)"
log "post curve n=10000 p=2048 default tmpfs prof: start"
python3 $H/post_n.py --image $T/build/fn-host-developer --work /dev/shm/publish-program/postn-2k --n 10000 --octets 2048 --profile default --prof $OUT/prof-post-n10000-p2048.txt --out $OUT/post-n10000-p2048 >> $OUT/post-n10000-p2048.log 2>&1
log "post curve: rc=$? $(tail -1 $OUT/post-n10000-p2048.log | cut -c1-400)"
rm -rf /dev/shm/publish-program/postn-2k
sh $H/measure.sh $OUT 1 1000 base=$T >> $OUT/measure.log 2>&1
log "measure n=1000 done"
sh $H/measure.sh $OUT 1 10000 base=$T >> $OUT/measure.log 2>&1
log "measure n=10000 done"
log "done"
touch $OUT/step1.done

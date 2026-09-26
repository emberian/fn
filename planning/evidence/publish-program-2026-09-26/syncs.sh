#!/bin/sh
# Sync-family syscall counts: `store probe N` under strace -f -c, one image,
# on the named filesystem (tmpfs or zfs; the counts do not depend on it).
# usage: syncs.sh LABEL TREE N FS OUTDIR
set -u
L=$1; T=$2; N=$3; FS=$4; OUT=$5
export ACL2_CUSTOMIZATION=NONE LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
if [ $FS = tmpfs ]; then W=/dev/shm/publish-program/sync-$L; else W=/tank/fn/scratch/publish-program/sync-$L; fi
rm -rf $W; mkdir -p $W $OUT
I=$T/build/fn-host-developer
printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n[control]\npath = "%s"\n' $W/store $W/c.sock > $W/c.toml
$I --fn operator $W/c.toml init --profile scale --max-transactions 1048576 --max-article-octets 2048 fn.letters fn.test > $W/init.out 2>&1
strace -f -c -o $OUT/syncs-probe-$L-$FS-n$N.txt -e trace=fsync,fdatasync,syncfs,sync_file_range,rename,renameat,renameat2,link,linkat,unlink,unlinkat $I --fn store $W/store probe $N > $W/probe.out 2>&1
echo "label=$L fs=$FS n=$N rc=$? $(tail -1 $W/probe.out)"; rm -rf $W

#!/bin/sh
# Sync-family syscall counts: `store probe N` under strace -f -c, one image.
# usage: syncs.sh LABEL TREE N OUTDIR
set -u
L=$1; T=$2; N=$3; OUT=$4
export ACL2_CUSTOMIZATION=NONE LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
W=/dev/shm/commit-regression/sync-$L; rm -rf $W; mkdir -p $W $OUT
I=$T/build/fn-host-developer
printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n[control]\npath = "%s"\n' $W/store $W/c.sock > $W/c.toml
$I --fn operator $W/c.toml init --profile scale --max-transactions 1048576 --max-article-octets 2048 fn.letters fn.test > $W/init.out 2>&1
strace -f -c -o $OUT/syncs-probe-$L-n$N.txt -e trace=fsync,fdatasync,syncfs,sync_file_range,rename,renameat,renameat2,link,linkat,unlink,unlinkat $I --fn store $W/store probe $N > $W/probe.out 2>&1
echo "label=$L n=$N rc=$? $(tail -1 $W/probe.out)"; rm -rf $W

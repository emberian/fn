#!/bin/sh
# Matched harness: for each repetition, image and filesystem, in interleaved
# order: `store STORE probe N` (x payload, scale profile, 2 KiB) timed with
# /usr/bin/time, then 100 POSTs of 2 KiB (post.py).  Every image runs with
# the same launcher form, OpenSSL prefix, init flags and client.
# usage: measure.sh OUTDIR REPS N LABEL=TREE ...
set -u
OUT=$1; REPS=$2; N=$3; shift 3
S=/tank/fn/scratch/commit-regression
export ACL2_CUSTOMIZATION=NONE LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib FN_CLIENT_TREE=$S/client
mkdir -p $OUT
rep=1
while [ $rep -le $REPS ]; do
  for pair in "$@"; do
    L=${pair%%=*}; T=${pair#*=}; I=$T/build/fn-host-developer
    for fs in tmpfs zfs; do
      if [ $fs = tmpfs ]; then B=/dev/shm/commit-regression/m; else B=$S/m; fi
      W=$B/$L-$fs-$rep; rm -rf $W; mkdir -p $W
      printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n[control]\npath = "%s"\n' $W/store $W/c.sock > $W/c.toml
      $I --fn operator $W/c.toml init --profile scale --max-transactions 1048576 --max-article-octets 2048 fn.letters fn.test > $W/init.out 2>&1 || echo "init failed $L $fs"
      /usr/bin/time -f 'wall=%e user=%U sys=%S maxrss_kib=%M' -o $W/time.txt $I --fn store $W/store probe $N > $W/probe.out 2>&1
      rc=$?
      echo "probe label=$L fs=$fs rep=$rep n=$N rc=$rc $(cat $W/time.txt) $(tail -1 $W/probe.out)" | tee -a $OUT/probe.log
      rm -rf $W
      W=$B/$L-$fs-$rep-post
      rm -rf $W
      echo "post label=$L fs=$fs rep=$rep $(python3 $S/post.py --image $I --work $W --n 100 --octets 2048 2>&1 | tail -1)" | tee -a $OUT/post.log
      rm -rf $W
    done
  done
  rep=$((rep+1))
done
echo "done $(date -u +%FT%TZ)" >> $OUT/probe.log

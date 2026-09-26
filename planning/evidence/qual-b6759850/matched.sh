#!/bin/sh
# qual-b6759850 matched commit-cost comparison, candidate b6759850 vs deployed bbf52159,
# commit-regression's own harness shape (its measure.sh and post.py, copied unchanged in form):
# per repetition, interleaved image order, ZFS scratch: `store STORE probe N` timed
# (scale profile, max-transactions 1048576, 2 KiB articles), then POSTs of 2 KiB over NNTP
# (post.py: per-POST median/p95, owner CPU).  Developer images (probe is a developer verb).
set -u
S=/tank/fn/scratch/qual-b6759850
OUT=$S/matched; mkdir -p $OUT
export ACL2_CUSTOMIZATION=NONE LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib FN_CLIENT_TREE=$S/tree
NEW=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer
OLD=/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host-developer
sha256sum $NEW.core $OLD.core > $OUT/images.sha256
for rep in 1 2; do
  for N in 1000 2000; do
    for pair in "b6759850=$NEW" "bbf52159=$OLD"; do
      L=${pair%%=*}; I=${pair#*=}
      W=$S/matched-work/$L-$N-$rep; rm -rf $W; mkdir -p $W
      printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n[control]\npath = "%s"\n' $W/store $W/c.sock > $W/c.toml
      $I --fn operator $W/c.toml init --profile scale --max-transactions 1048576 --max-article-octets 2048 fn.letters fn.test > $W/init.out 2>&1 || echo "init failed $L"
      /usr/bin/time -f 'wall=%e user=%U sys=%S maxrss_kib=%M' -o $W/time.txt $I --fn store $W/store probe $N > $W/probe.out 2>&1
      rc=$?
      echo "probe label=$L rep=$rep n=$N rc=$rc $(cat $W/time.txt) $(tail -1 $W/probe.out)" | tee -a $OUT/probe.log
      rm -rf $W
    done
  done
  for pair in "b6759850=$NEW" "bbf52159=$OLD"; do
    L=${pair%%=*}; I=${pair#*=}
    W=$S/matched-work/$L-post-$rep; rm -rf $W
    echo "post label=$L rep=$rep n=1000 $(python3 $S/post.py --image $I --work $W --n 1000 --octets 2048 2>&1 | tail -1)" | tee -a $OUT/post.log
    rm -rf $W
  done
done
echo "done $(date -u +%FT%TZ)" >> $OUT/probe.log

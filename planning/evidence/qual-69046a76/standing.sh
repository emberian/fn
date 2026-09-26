#!/bin/sh
# qual-69046a76 STANDING CASES (PKT-481): on all four images, bounds_join LargeReplyTests
# (a 3 MiB ARTICLE and a multi-MiB OVER served whole, owner alive, clean exit), then the raw
# runs: bigart.py (1, 2, 3 MiB ARTICLE) and bigover.py (2,000 articles x 2,000 octets of
# References: the served 2,000-article OVER's time, PKT-491), on the fix's 4 MiB profile and
# on the scale preset (T=1,048,576, H=4 GiB) with A raised to 4 MiB.
set -u
. /tank/fn/scratch/qual-69046a76/env.sh
R=$S/standing; rm -rf $R; mkdir -p $R
cd $S/tree
for img in fn-host fn-host-developer fn-host-dtn fn-host-dtn-developer; do
  { echo "# LargeReplyTests on $I/$img start $(date -u +%FT%TZ)"; s=$(date +%s)
    FN_NATIVE_HOST=$I/$img timeout 3600 python3 -m unittest -v tests.test_native_bounds_join.LargeReplyTests 2>&1
    echo "# rc=$? wall=$(( $(date +%s) - s ))"; } > $R/largereply-$img.log 2>&1
done
python3 $S/bigart.py $R/bigart $I/fn-host=prod $I/fn-host-developer=dev $I/fn-host-dtn=dtn $I/fn-host-dtn-developer=dtndev -- 1048576 2097152 3145728 > $R/bigart.log 2>&1; echo "rc=$?" >> $R/bigart.log
SCALE="--profile scale --max-transactions 1048576 --max-history-octets 4294967296 --max-article-octets 4194304"
QUAL_INIT="$SCALE" python3 $S/bigart.py $R/bigart-scale $I/fn-host=prod $I/fn-host-developer=dev -- 3145728 > $R/bigart-scale.log 2>&1; echo "rc=$?" >> $R/bigart-scale.log
for img in fn-host fn-host-developer fn-host-dtn fn-host-dtn-developer; do
  python3 $S/bigover.py $R/over-$img $I/$img 2000 2000 > $R/bigover-$img.log 2>&1; echo "rc=$?" >> $R/bigover-$img.log
done
QUAL_INIT="$SCALE" python3 $S/bigover.py $R/over-scale-fn-host $I/fn-host 2000 2000 > $R/bigover-scale-fn-host.log 2>&1; echo "rc=$?" >> $R/bigover-scale-fn-host.log
for d in $R/over-* $R/bigart $R/bigart-scale; do rm -rf $d/*/store $d/store; done
( cd $R && sha256sum *.log > SHA256SUMS )
touch $S/done.standing; echo STANDING-DONE

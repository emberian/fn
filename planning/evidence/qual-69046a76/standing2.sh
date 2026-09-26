#!/bin/sh
# qual-69046a76 standing cases, part 2 (the DTN images omit operator run: prod and dev only)
set -u
. /tank/fn/scratch/qual-69046a76/env.sh
R=$S/standing
cd $S/tree
SCALE="--profile scale --max-transactions 1048576 --max-history-octets 4294967296 --max-article-octets 4194304"
rm -rf $R/bigart-scale
QUAL_INIT="$SCALE" python3 $S/bigart.py $R/bigart-scale $I/fn-host=prod $I/fn-host-developer=dev -- 3145728 > $R/bigart-scale.log 2>&1; echo "rc=$?" >> $R/bigart-scale.log
for img in fn-host fn-host-developer; do
  rm -rf $R/over-$img
  python3 $S/bigover.py $R/over-$img $I/$img 2000 2000 > $R/bigover-$img.log 2>&1; echo "rc=$?" >> $R/bigover-$img.log
done
rm -rf $R/over-scale-fn-host
QUAL_INIT="$SCALE" python3 $S/bigover.py $R/over-scale-fn-host $I/fn-host 2000 2000 > $R/bigover-scale-fn-host.log 2>&1; echo "rc=$?" >> $R/bigover-scale-fn-host.log
for d in $R/over-* $R/bigart $R/bigart-scale; do rm -rf $d/*/store $d/store; done
( cd $R && sha256sum *.log > SHA256SUMS )
touch $S/done.standing; echo STANDING-DONE

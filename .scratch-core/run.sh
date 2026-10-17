#!/bin/sh
# usage: run.sh TAG BUILD_DIR   -> /tank/fn/scratch/n-mem3/core-growth/TAG.{measure.json,tally.tsv,log}
D=/tank/fn/scratch/n-mem3/core-growth; T=$1; B=$2
cd $D
python3 /tank/fn/scratch/n-mem3/ifb/tree/tools/runtime_image/node_measure.py core $B/fn-host > $T.measure.json 2>$T.measure.err
core=$(sed -n 's/.*--core "\([^"]*\)".*/\1/p' $B/fn-host)
export SBCL_HOME=/tank/fn/sbcl/lib/sbcl/ TALLY_OUT=$D/$T.tally.tsv
/tank/fn/sbcl/bin/sbcl --tls-limit 65536 --dynamic-space-size 8000MB --control-stack-size 1024KB --disable-ldb --core "$core" --noinform --end-runtime-options --no-userinit --no-sysinit --eval "(load \"$D/tally.lisp\")" --disable-debugger --end-toplevel-options > $T.log 2>&1
echo "rc=$?" >> $T.log

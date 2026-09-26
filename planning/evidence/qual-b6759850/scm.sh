#!/bin/sh
# served crash model on the harness-repaired copy (load list only: two include-books before host/store-node-host.lisp)
S=/tank/fn/scratch/qual-b6759850
export NS_TREE=$S/ptree NS_TAG=scm
. $S/env.sh
cd $S/ptree
{ echo "# served_crash_model on ptree start $(date -u +%FT%TZ) FN_NATIVE_HOST=$FN_NATIVE_HOST"; s=$(date +%s)
  timeout 3600 python3 -m unittest -v tests.test_native_served_crash_model 2>&1; echo "# rc=$? wall=$(( $(date +%s) - s ))"; } > $S/logs/rerun/served_crash_model.ptree.log
touch $S/done.scm

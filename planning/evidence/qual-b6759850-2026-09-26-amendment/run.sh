#!/bin/sh
# qual-harness-c18: one module (or test) on the frozen b6759850 images from the scratch tree.
# Usage: TAG=label [NS_HOST=fn-host-developer] sh run.sh LOGNAME tests.module[.Class.test] ...
set -u
. /tank/fn/scratch/qual-harness-c18/env.sh
name=$1; shift
cd $T
log=$S/logs/$name.log
{ echo "# $name start $(date -u +%FT%TZ) cwd $T"
  echo "# FN_NATIVE_HOST $FN_NATIVE_HOST"
  echo "# FN_NATIVE_CRASH_HOST $FN_NATIVE_CRASH_HOST"
  echo "# FN_NATIVE_BP_HOST $FN_NATIVE_BP_HOST FN_NATIVE_BP_NODE_HOST $FN_NATIVE_BP_NODE_HOST"
  echo "# overlay $(cat $S/overlay.sha256 2>/dev/null | tr '\n' ' ')"
  s=$(date +%s)
  timeout 3600 python3 -m unittest -v "$@" 2>&1
  echo "# rc=$? wall=$(( $(date +%s) - s )) end $(date -u +%FT%TZ)"; } > $log 2>&1
echo "$name: $(grep -E '^(OK|FAILED)' $log | tail -1) $(tail -1 $log)" >> $S/logs/summary.log

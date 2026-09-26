#!/bin/sh
# qual-b6759850 module runner: tools/test_budget.py (180 s a module, 20 s a test)
# over the named modules on one image, one report per label; then every module
# the budget terminated runs once more WHOLE (test_budget.py --one, no budget)
# so it still has a verdict, recorded as over budget.
# Usage: NS_TAG=label [NS_HOST=fn-host-developer] [NS_BP_IMAGE=...] sh brun.sh tests.m1 tests.m2 ...
set -u
. /tank/fn/scratch/qual-b6759850/env.sh
L=$S/blogs/$NS_TAG; mkdir -p $L
cd $T
{ echo "# label $NS_TAG start $(date -u +%FT%TZ) cwd $T"
  echo "# FN_NATIVE_HOST $FN_NATIVE_HOST"
  echo "# FN_NATIVE_BP_HOST $FN_NATIVE_BP_HOST FN_NATIVE_BP_NODE_HOST $FN_NATIVE_BP_NODE_HOST"
  env | grep -E '^(FN_|LD_LIBRARY_PATH|SBCL_HOME)' | sort | sed 's/^/# env /'
  python3 tools/test_budget.py "$@" --logs $L --json $S/breport-$NS_TAG.json
  echo "# test_budget rc=$? end $(date -u +%FT%TZ)"; } > $S/logs/budget-$NS_TAG.log 2>&1
# whole reruns of the terminated modules
python3 - "$S/breport-$NS_TAG.json" > $S/killed-$NS_TAG.txt <<'PY'
import json,sys
for r in json.load(open(sys.argv[1])):
    if r.get("terminated"): print(r["module"])
PY
for m in $(cat $S/killed-$NS_TAG.txt); do
  log=$L/$m.whole.log
  { echo "# whole $m start $(date -u +%FT%TZ)"; s=$(date +%s)
    timeout 3600 python3 -m unittest -v $m 2>&1
    echo "# rc=$? wall=$(( $(date +%s) - s )) end $(date -u +%FT%TZ)"; } > $log 2>&1
  echo "$m whole: $(grep -E '^(OK|FAILED)' $log | tail -1) $(tail -1 $log)" >> $S/logs/budget-$NS_TAG.log
done
touch $S/done.$NS_TAG
echo "DONE $NS_TAG"

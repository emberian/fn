#!/bin/sh
# The native request verb's four labs (qual-bbf52159 labs.sh, paths changed) and
# the four-node mission, signed and unsigned, plus the ambiguous-peer case, on the DTN developer image.
set -u
. /tank/fn/scratch/qual-b6759850/env.sh
cd $S/tree
IMG=$I/fn-host-dtn-developer
R=$S/request-labs; rm -rf $R; mkdir -p $R
sha256sum $IMG $IMG.core > $R/image.sha256
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 0 --native --work $R/control > $R/control.out 2>&1; echo "control rc=$?" | tee -a $R/rcs
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 1 --native --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-carried-1 > $R/dtn7-carried-1.out 2>&1; echo "dtn7-carried-1 rc=$?" | tee -a $R/rcs
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 2 --native --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-carried-2 > $R/dtn7-carried-2.out 2>&1; echo "dtn7-carried-2 rc=$?" | tee -a $R/rcs
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 1 --native --b-trusts neighbour --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-unauthorized > $R/dtn7-unauthorized.out 2>&1; echo "dtn7-unauthorized rc=$?" | tee -a $R/rcs
M=$S/missions; rm -rf $M; mkdir -p $M
for rep in unsigned signed; do
  s=$(date +%s)
  python3 tests/bp-dtn7/run_mission_four_node.py --image $IMG --owner-image $I/fn-host-developer --dtn7-repo /tank/fn/dtn7/repo --work $M/$rep --report $rep --openssl $FN_TEST_OPENSSL > $M/$rep.out 2>&1
  echo "mission-$rep rc=$? wall=$(( $(date +%s) - s ))" | tee -a $M/rcs
done
python3 tests/bp-dtn7/run_mission_four_node.py --image $IMG --owner-image $I/fn-host-developer --dtn7-repo /tank/fn/dtn7/repo --work $M/ambiguous --case ambiguous-peer --openssl $FN_TEST_OPENSSL > $M/ambiguous.out 2>&1; echo "ambiguous-peer rc=$?" | tee -a $M/rcs
echo LABS-DONE

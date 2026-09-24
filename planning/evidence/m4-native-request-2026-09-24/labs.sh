#!/bin/sh
set -u
S=/tank/fn/scratch/m4-native-request
cd $S/img-tree
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
IMG=build/fn-host-dtn-developer
R=$S/final; rm -rf $R; mkdir -p $R
sha256sum $IMG $IMG.core > $R/image.sha256
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 0 --native --work $R/control > $R/control.out 2>&1; echo "control rc=$?"
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 1 --native --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-carried-1 > $R/dtn7-carried-1.out 2>&1; echo "dtn7-carried-1 rc=$?"
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 2 --native --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-carried-2 > $R/dtn7-carried-2.out 2>&1; echo "dtn7-carried-2 rc=$?"
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 1 --native --b-trusts neighbour --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-unauthorized > $R/dtn7-unauthorized.out 2>&1; echo "dtn7-unauthorized rc=$?"
echo ALLDONE

#!/bin/sh
set -u
S=/tank/fn/scratch/d23-bp; T=$S/img-tree; cd $T
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
IMG=build/fn-host-dtn-developer
sha256sum $IMG $IMG.core
R=$S/final2; rm -rf $R; mkdir -p $R
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 1 --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-carried-1 > $R/dtn7-carried-1.out 2>&1; echo "dtn7-carried-1 rc=$?"
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 2 --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-carried-2 > $R/dtn7-carried-2.out 2>&1; echo "dtn7-carried-2 rc=$?"
python3 tests/bp-dtn7/run_four_node_lab.py --run-base $R/four-dtn7 --revision "$(cat $S/REV)" --dtn7-repo /tank/fn/dtn7/repo --image $IMG > $R/four-dtn7.out 2>&1; echo "four-dtn7 rc=$? $(tail -1 $R/four-dtn7.out)"
echo ALLDONE

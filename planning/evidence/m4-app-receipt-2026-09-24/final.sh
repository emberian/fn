#!/bin/sh
# m4-app-receipt final: rebuild the DTN pair from the lane tree, run the labs, then the native modules.
set -u
S=/tank/fn/scratch/m4-app-receipt
T=$S/tree
cd "$T"
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
for p in production developer; do
  img=build/fn-host-dtn; [ $p = developer ] && img=build/fn-host-dtn-developer
  FN_NATIVE_PROFILE=$p FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=$img FN_NATIVE_LOG=build/lane/native-build-dtn-$p.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -1
  echo "undefined lines: $(grep -ci undefined build/lane/native-build-dtn-$p.log)"
done
sha256sum build/fn-host-dtn build/fn-host-dtn.core build/fn-host-dtn-developer build/fn-host-dtn-developer.core
IMG=build/fn-host-dtn-developer
R=$S/final; rm -rf $R; mkdir -p $R
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 0 --work $R/control > $R/control.out 2>&1; echo "control rc=$?"
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 1 --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-neighbour > $R/dtn7-neighbour.out 2>&1; echo "dtn7-neighbour rc=$?"
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $IMG --relays 1 --b-trusts source --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-source > $R/dtn7-source.out 2>&1; echo "dtn7-source rc=$?"
python3 tests/bp-dtn7/run_four_node_lab.py --run-base $R/four-dtn7 --revision lane-m4-app-receipt --dtn7-repo /tank/fn/dtn7/repo --image $IMG > $R/four-dtn7.out 2>&1; echo "four-dtn7 rc=$? $(cat $R/four-dtn7.out | tail -1)"
python3 tests/bp-dtn7/run_four_node_lab.py --run-base $R/four-mock --revision lane-m4-app-receipt > $R/four-mock.out 2>&1; echo "four-mock rc=$? $(tail -1 $R/four-mock.out)"
NS_TAG=final $S/run.sh test_bp_node_native test_bp_service_native test_bp_contact_relay_native test_bp_contact_native test_bp_receive_integrity_native
echo ALLDONE

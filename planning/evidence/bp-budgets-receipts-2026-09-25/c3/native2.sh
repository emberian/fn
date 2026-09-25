#!/bin/sh
# bp-budgets lane (continuation 2): certify the dtn roots at edb208fe from the
# cache (receipt-send is the only changed book), build the DTN developer
# image, run tests.test_bp_node_native and the dtn7 app-receipt lab with
# --no-contact-tick.  Every process is ours.
set -u
S=/tank/fn/scratch/bp-budgets
T=$S/dtn-edb208fe
L=$S/native-logs-edb208fe
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_ACL2=$ACL2 FN_CERT_CACHE=/tank/fn/certcache
mkdir -p $L; cd "$T"; mkdir -p build/lane
echo "tree rev: $(cat REV)"
swarm-build python3 tools/certify_books.py --incremental --jobs 2 --timeout-seconds 300 $(cat $S/dtnroots.txt) > $L/dtn-certify.out 2>&1
echo "dtn certify rc=$? $(tail -n 3 $L/dtn-certify.out | tr '\n' ' ')"
python3 tools/proof_artifacts.py validate --profile dtn --acl2 "$ACL2" > $L/validate-dtn.txt 2>&1 || { tail -20 $L/validate-dtn.txt; echo VALIDATE-FAILED; exit 1; }
tail -n 2 $L/validate-dtn.txt
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn-developer FN_NATIVE_LOG=$L/native-build-dtn-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -2
echo "undefined lines: $(grep -ci undefined $L/native-build-dtn-developer.log)"
sha256sum build/fn-host-dtn-developer build/fn-host-dtn-developer.core | tee $L/SHA256SUMS
B=$T/build
export FN_NATIVE_SOURCE_ROOT=$T FN_NATIVE_BP_NODE_HOST=$B/fn-host-dtn-developer FN_NATIVE_BP_HOST=$B/fn-host-dtn-developer FN_NATIVE_DTN_DEVELOPER_HOST=$B/fn-host-dtn-developer
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag2; mkdir -p $S/diag2
s=$(date +%s)
systemd-run --user --scope -q -p MemoryMax=24G timeout 3600 python3 -m unittest -v tests.test_bp_node_native > $L/test_bp_node_native.log 2>&1 < /dev/null
echo "test_bp_node_native rc=$? wall=$(( $(date +%s)-s ))s $(tail -n 4 $L/test_bp_node_native.log | grep -E '^(OK|FAILED)')"
R=$S/lab2; rm -rf $R; mkdir -p $R
systemd-run --user --scope -q -p MemoryMax=24G python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image build/fn-host-dtn-developer --relays 1 --no-contact-tick --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-no-tick > $L/lab-dtn7-no-tick.out 2>&1
echo "lab dtn7 --no-contact-tick rc=$?"
systemd-run --user --scope -q -p MemoryMax=24G python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image build/fn-host-dtn-developer --relays 0 --no-contact-tick --work $R/control-no-tick > $L/lab-control-no-tick.out 2>&1
echo "lab control --no-contact-tick rc=$?"
echo ALLDONE

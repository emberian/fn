#!/bin/sh
# spike/bp native run 2: the connection-local receipt transfer (host change
# only; books unchanged), rebuilt DTN images, the module, and the labs with
# `bp-obligation request' (--native --no-cuts) on the production image.
set -u
T=${1:?gate tree}
S=/tank/fn/scratch/spike-bp
L=$S/native-logs-2
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_ACL2=$ACL2 FN_CERT_CACHE=/tank/fn/certcache
mkdir -p $L; cd "$T"
for prof in developer production; do
  FN_NATIVE_PROFILE=$prof FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn-$prof FN_NATIVE_LOG=$L/native-build-dtn-$prof.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -1
  echo "$prof undefined lines: $(grep -ci undefined $L/native-build-dtn-$prof.log)"
done
sha256sum build/fn-host-dtn-developer build/fn-host-dtn-developer.core build/fn-host-dtn-production build/fn-host-dtn-production.core build/fn-host build/fn-host.core | tee $L/IMAGES.SHA256
B=$T/build
DEV=$B/fn-host-dtn-developer PROD=$B/fn-host-dtn-production
export FN_NATIVE_SOURCE_ROOT=$T FN_NATIVE_BP_NODE_HOST=$DEV FN_NATIVE_BP_HOST=$DEV FN_NATIVE_DTN_DEVELOPER_HOST=$DEV FN_NATIVE_DEVELOPER_HOST=$DEV
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag2; mkdir -p $S/diag2
run() { tag=$1; shift; s=$(date +%s); systemd-run --user --scope -q -p MemoryMax=24G timeout 3600 "$@" > $L/$tag.log 2>&1 < /dev/null; echo "$tag rc=$? wall=$(( $(date +%s)-s ))s"; }
R=$S/lab2; rm -rf $R; mkdir -p $R
LAB="python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image $PROD --setup-image $DEV --dtn7-repo /tank/fn/dtn7/repo"
run lab-r1-present-native $LAB --relays 1 --native --no-cuts --no-contact-tick --work $R/r1-present-native
run lab-r1-removed-native $LAB --relays 1 --native --no-cuts --routes removed --settle 20 --work $R/r1-removed-native
run lab-r0-fragment-native $LAB --relays 0 --native --no-cuts --no-contact-tick --b-transfer-mru 4096 --article-lines 200 --work $R/r0-fragment-native
FN_TEST_OPENSSL=$FN_OPENSSL_PREFIX/bin/openssl run lab-r3-signed $LAB --relays 3 --native --no-cuts --no-contact-tick --settle 60 --signed-receipts $B/fn-host --work $R/r3-signed
run test_bp_node_native python3 -m unittest -v tests.test_bp_node_native
grep -E '^(OK|FAILED)' $L/test_bp_node_native.log
echo ALLDONE

#!/bin/sh
# bp-routing-2, deputy's rerun: build the default developer image from this
# lane's tree (the reader image), then the full test_bp_node_native module.
set -u
S=/tank/fn/scratch/bp-routing-2; T=$S/tree; L=$S/logs2
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_ACL2=$ACL2 FN_CERT_CACHE=/tank/fn/certcache
mkdir -p $L; cd $T
ROOTS=$(python3 -c "import sys; sys.path.insert(0,'tools'); from pathlib import Path; import proof_artifacts as p; print(' '.join(p.profile_roots(Path('.'), 'default')))")
echo "default roots: $(echo $ROOTS | wc -w)"
swarm-build python3 tools/certify_books.py --incremental --jobs 2 --timeout-seconds 300 $ROOTS > $L/default-certify.out 2>&1
echo "default certify rc=$? $(tail -n 2 $L/default-certify.out | head -1 | cut -c1-200)"
python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > $L/validate-default.txt 2>&1 || { tail -20 $L/validate-default.txt; echo VALIDATE-FAILED; exit 1; }
tail -n 1 $L/validate-default.txt
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=$L/native-build-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -1
echo "undefined lines: $(grep -ci undefined $L/native-build-developer.log)"
sha256sum build/fn-host-developer build/fn-host-developer.core $L/native-build-developer.log build/fn-host-dtn-developer build/fn-host-dtn-developer.core tests/test_bp_node_native.py | tee $L/IMAGE-SHA256SUMS
B=$T/build
export FN_NATIVE_SOURCE_ROOT=$T FN_NATIVE_BP_NODE_HOST=$B/fn-host-dtn-developer FN_NATIVE_READER_HOST=$B/fn-host-developer
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag2; mkdir -p $S/diag2
s=$(date +%s)
systemd-run --user --scope -q -p MemoryMax=24G timeout 3600 python3 -m unittest -v tests.test_bp_node_native > $L/test_bp_node_native.log 2>&1 < /dev/null
echo "test_bp_node_native rc=$? wall=$(( $(date +%s)-s ))s $(tail -n 4 $L/test_bp_node_native.log | grep -E '^(OK|FAILED)') ok=$(grep -c '\.\.\. ok' $L/test_bp_node_native.log)"
sha256sum $L/test_bp_node_native.log
echo ALLDONE

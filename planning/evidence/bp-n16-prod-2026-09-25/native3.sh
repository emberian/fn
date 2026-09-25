#!/bin/sh
# bp-n16-prod-2: at the lane tree, certify dtn and default roots from the
# cache, build the DTN and the default developer images, run the whole
# tests.test_bp_node_native module once with FN_NATIVE_READER_HOST set.
set -u
S=/tank/fn/scratch/bp-n16-prod; T=$S/t5e8; L=$S/logs3
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_ACL2=$ACL2 FN_CERT_CACHE=/tank/fn/certcache
mkdir -p $L; cd $T
echo "tree rev: $(cat REV)"
for P in dtn default; do
  ROOTS=$(python3 -c "import sys; sys.path.insert(0,'tools'); from pathlib import Path; import proof_artifacts as p; print(' '.join(p.profile_roots(Path('.'), '$P')))")
  echo "$P roots: $(echo $ROOTS | wc -w)"
  swarm-build python3 tools/certify_books.py --incremental --jobs 2 --timeout-seconds 300 $ROOTS > $L/$P-certify.out 2>&1
  echo "$P certify rc=$? $(tail -n 3 $L/$P-certify.out | tr '\n' ' ' | cut -c1-300)"
  python3 tools/proof_artifacts.py validate --profile $P --acl2 "$ACL2" > $L/validate-$P.txt 2>&1 || { tail -20 $L/validate-$P.txt; echo VALIDATE-FAILED $P; exit 1; }
  tail -n 1 $L/validate-$P.txt
done
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn-developer FN_NATIVE_LOG=$L/native-build-dtn-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -1
echo "dtn undefined lines: $(grep -ci undefined $L/native-build-dtn-developer.log)"
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=$L/native-build-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -1
echo "default undefined lines: $(grep -ci undefined $L/native-build-developer.log)"
sha256sum build/fn-host-developer build/fn-host-developer.core $L/native-build-developer.log build/fn-host-dtn-developer build/fn-host-dtn-developer.core $L/native-build-dtn-developer.log tests/test_bp_node_native.py host/native/bp-node.lisp | tee $L/IMAGE-SHA256SUMS
B=$T/build
export FN_NATIVE_SOURCE_ROOT=$T FN_NATIVE_BP_NODE_HOST=$B/fn-host-dtn-developer FN_NATIVE_BP_HOST=$B/fn-host-dtn-developer FN_NATIVE_DTN_DEVELOPER_HOST=$B/fn-host-dtn-developer FN_NATIVE_READER_HOST=$B/fn-host-developer
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag3; mkdir -p $S/diag3
s=$(date +%s)
echo "start $(date -u +%FT%TZ)"
systemd-run --user --scope -q -p MemoryMax=24G timeout 3600 python3 -m unittest -v tests.test_bp_node_native > $L/test_bp_node_native.log 2>&1 < /dev/null
echo "test_bp_node_native rc=$? wall=$(( $(date +%s)-s ))s end $(date -u +%FT%TZ) $(tail -n 4 $L/test_bp_node_native.log | grep -E '^(OK|FAILED)') ok=$(grep -c '\.\.\. ok' $L/test_bp_node_native.log)"
sha256sum $L/test_bp_node_native.log
echo ALLDONE

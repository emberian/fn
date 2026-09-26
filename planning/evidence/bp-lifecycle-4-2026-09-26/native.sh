#!/bin/sh
# bp-lifecycle-4 (from bp-lifecycle-3): at lane commit REV (unpacked into $S/tREV), install the dtn
# and default roots from the cache (certifying what is missing), build the DTN
# and default developer images, then run the BP modules named after REV (or
# the six of item 4 and the fragment module) once each under a 24G scope.
# Usage: native.sh REV [MODULE...]
set -u
REV=$1; shift
MODS=${*:-"test_bp_service_native test_bp_contact_native test_bp_contact_relay_native test_bp_app_native test_bp_node_native test_bp_receive_integrity_native test_bp_fragment_node_native"}
S=/tank/fn/scratch/bp-lifecycle-4; T=$S/t$REV; L=$S/logs-$REV${LOGSUFFIX:-}
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_ACL2=$ACL2 FN_CERT_CACHE=/tank/fn/certcache PYTHONDONTWRITEBYTECODE=1
mkdir -p $L; cd $T
if [ ! -x build/fn-host-dtn-developer ]; then
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
sha256sum build/fn-host-developer build/fn-host-developer.core build/fn-host-dtn-developer build/fn-host-dtn-developer.core $L/native-build-developer.log $L/native-build-dtn-developer.log | tee $L/IMAGE-SHA256SUMS
fi
B=$T/build
export FN_NATIVE_SOURCE_ROOT=$T FN_NATIVE_HOST=$B/fn-host-developer FN_NATIVE_DEVELOPER_HOST=$B/fn-host-developer FN_NATIVE_CRASH_HOST=$B/fn-host-developer
export FN_NATIVE_DTN_HOST=$B/fn-host-dtn-developer FN_NATIVE_DTN_DEVELOPER_HOST=$B/fn-host-dtn-developer
export FN_NATIVE_BP_HOST=$B/fn-host-dtn-developer FN_NATIVE_BP_NODE_HOST=$B/fn-host-dtn-developer
export FN_NATIVE_CONTACT_SENDER=$B/fn-host-dtn-developer FN_NATIVE_CONTACT_RECEIVER=$B/fn-host-dtn-developer
export FN_NATIVE_READER_HOST=$B/fn-host-developer
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag-$REV; mkdir -p $S/diag-$REV
for M in $MODS; do
  case $M in test_bp_fragment_node_native*) export FN_NATIVE_DEVELOPER_HOST=$B/fn-host-dtn-developer; TO=10800;; *) export FN_NATIVE_DEVELOPER_HOST=$B/fn-host-developer; TO=3600;; esac
  s=$(date +%s)
  systemd-run --user --scope -q -p MemoryMax=24G timeout $TO python3 -m unittest -v tests.$M > $L/$M.log 2>&1 < /dev/null
  echo "$M rc=$? wall=$(( $(date +%s)-s ))s $(tail -n 4 $L/$M.log | grep -E '^(OK|FAILED)') ok=$(grep -c '\.\.\. ok' $L/$M.log)"
  sha256sum $L/$M.log
done
echo ALLDONE

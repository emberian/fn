#!/bin/sh
# peering-tls-pull: build the developer image from the lane's gate tree on
# hbox and run the native cases.  Run ON hbox:
#   sh image.sh /tank/fn/gates/peering-tls-pull-rN [build|test|both]
# The nodes' stores live under /tank/fn/scratch/peering-tls-pull/tmp (TMPDIR);
# the test module runs under systemd-run MemoryMax=24G and tools/test_budget.py.
set -u
T=$1; WHAT=${2:-both}
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_ACL2=$ACL2 FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib FN_TEST_OPENSSL=$FN_OPENSSL_PREFIX/bin/openssl
export FN_OPENSSL=$FN_OPENSSL_PREFIX/bin/openssl
cd "$T"
mkdir -p build/lane
if [ "$WHAT" = build ] || [ "$WHAT" = both ]; then
python3 tools/proof_artifacts.py acquire --profile default --root "$T" --cache /tank/fn/certcache --acl2 "$ACL2" > build/lane/acquire.txt 2>&1 || { tail -5 build/lane/acquire.txt; echo ACQUIRE-FAILED; exit 1; }
python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/lane/validate.txt 2>&1 || { tail -8 build/lane/validate.txt; echo VALIDATE-FAILED; exit 1; }
tail -n 2 build/lane/validate.txt
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/lane/native-build-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -2
echo "undefined lines: $(grep -ci undefined build/lane/native-build-developer.log)"
grep -i -B2 -A6 "undefined" build/lane/native-build-developer.log | head -40
sha256sum build/fn-host-developer build/fn-host-developer.core build/lane/native-build-developer.log
fi
if [ "$WHAT" = test ] || [ "$WHAT" = both ]; then
export FN_NATIVE_HOST=$T/build/fn-host-developer
S=/tank/fn/scratch/peering-tls-pull
mkdir -p $S/tmp
export TMPDIR=$S/tmp
rm -rf build/lane/pull-evidence; mkdir -p build/lane/pull-evidence
FN_PULL_EVIDENCE=$T/build/lane/pull-evidence FN_INN_SRC=/tank/fn/inn/2.7.4 systemd-run --user --wait --pipe --quiet -p MemoryMax=24G --working-directory="$T" env FN_NATIVE_HOST=$FN_NATIVE_HOST FN_PULL_EVIDENCE=$T/build/lane/pull-evidence FN_INN_SRC=/tank/fn/inn/2.7.4 TMPDIR=$TMPDIR FN_OPENSSL_PREFIX=$FN_OPENSSL_PREFIX LD_LIBRARY_PATH=$LD_LIBRARY_PATH python3 tools/test_budget.py tests.test_native_peer_pull > build/lane/native-peer-pull.log 2>&1; echo "peer-pull rc=$?"
grep -hE "NATIVE-PULL-WITNESS|^(OK|FAILED)|Error|ok$|FAIL|skipped|OVER|seconds" build/lane/native-peer-pull.log | cut -c1-400
sha256sum build/lane/native-*.log
fi

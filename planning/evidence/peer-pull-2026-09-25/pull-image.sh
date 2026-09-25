#!/bin/sh
# peer-pull: build the developer image from the lane tree on hbox and run the
# native pull cases (tests/test_native_peer_pull.py, whole).  Run ON hbox:
#   sh pull-image.sh /tank/fn/scratch/peer-pull/gate-rN [build|test|both]
set -u
T=$1; WHAT=${2:-both}
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_ACL2=$ACL2 FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib FN_TEST_OPENSSL=$FN_OPENSSL_PREFIX/bin/openssl
cd "$T"
mkdir -p build/lane
if [ "$WHAT" != test ]; then
python3 tools/proof_artifacts.py acquire --profile default --root "$T" --cache /tank/fn/certcache --acl2 "$ACL2" > build/lane/acquire.txt 2>&1 || { tail -5 build/lane/acquire.txt; echo ACQUIRE-FAILED; exit 1; }
python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/lane/validate.txt 2>&1 || { tail -8 build/lane/validate.txt; echo VALIDATE-FAILED; exit 1; }
tail -n 2 build/lane/validate.txt
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/lane/native-build-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -2
echo "undefined lines: $(grep -ci undefined build/lane/native-build-developer.log)"
grep -i -B2 -A6 "undefined" build/lane/native-build-developer.log | head -40
sha256sum build/fn-host-developer build/fn-host-developer.core build/lane/native-build-developer.log
fi
if [ "$WHAT" != build ]; then
rm -rf build/lane/pull-evidence; mkdir -p build/lane/pull-evidence
FN_PULL_EVIDENCE=$T/build/lane/pull-evidence FN_INN_SRC=/tank/fn/inn/2.7.4 FN_NATIVE_HOST=$T/build/fn-host-developer python3 -m unittest -v tests.test_native_peer_pull > build/lane/native-peer-pull.log 2>&1; echo "native rc=$?"
grep -E "NATIVE-PULL-WITNESS|^(OK|FAILED)|Error|ok$|FAIL|skipped" build/lane/native-peer-pull.log
sha256sum build/lane/native-peer-pull.log build/lane/pull-evidence/*
fi

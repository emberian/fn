#!/bin/sh
# control-c2c3: build the developer image from the lane tree and run the native C2 case.
set -u
T=$1
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_ACL2=$ACL2 FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
cd "$T"
mkdir -p build/lane
python3 tools/proof_artifacts.py acquire --profile default --root "$T" --cache /tank/fn/certcache --acl2 "$ACL2" > build/lane/acquire.txt 2>&1 || { tail -5 build/lane/acquire.txt; echo ACQUIRE-FAILED; exit 1; }
python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/lane/validate.txt 2>&1 || { tail -8 build/lane/validate.txt; echo VALIDATE-FAILED; exit 1; }
tail -n 2 build/lane/validate.txt
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/lane/native-build-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -2
echo "undefined lines: $(grep -ci undefined build/lane/native-build-developer.log)"
sha256sum build/fn-host-developer build/fn-host-developer.core build/lane/native-build-developer.log
FN_NATIVE_HOST=$T/build/fn-host-developer python3 -m unittest -v tests.test_native_control_authority > build/lane/native-control-authority.log 2>&1; echo "native rc=$?"
grep -E "NATIVE-CONTROL-AUTHORITY-WITNESS|^(OK|FAILED)|Error|ok$|FAIL" build/lane/native-control-authority.log
sha256sum build/lane/native-control-authority.log

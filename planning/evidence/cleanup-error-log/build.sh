#!/bin/sh
set -eu
S=/tank/fn/scratch/cleanup-error-log
ROOT=$S/tree
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
cd $ROOT
mkdir -p build/freeze
python3 tools/proof_artifacts.py acquire --profile default --root "$ROOT" --cache "$CACHE" --acl2 "$ACL2" > build/freeze/acquire-default.txt 2>&1
FN_ACL2=$ACL2 python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/freeze/validate-default.txt 2>&1
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host FN_NATIVE_LOG=build/freeze/native-build-production.log swarm-build sh tools/build_native_host.sh > build/freeze/build-production.txt 2>&1
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/freeze/native-build-developer.log swarm-build sh tools/build_native_host.sh > build/freeze/build-developer.txt 2>&1
IMG=$S/images/$1
sh packaging/freeze-native-image.sh "$ROOT/build" "$IMG" "$FN_OPENSSL_PREFIX" > build/freeze/freeze.txt 2>&1 || true
ls -la build/fn-host* "$IMG" 2>&1
echo BUILD-DONE

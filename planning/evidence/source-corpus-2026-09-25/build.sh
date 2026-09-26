#!/bin/sh
set -eu
ROOT=/tank/fn/scratch/source-corpus/tree
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
cd "$ROOT"
mkdir -p build/freeze
python3 tools/proof_artifacts.py acquire --profile default --root "$ROOT" --cache "$CACHE" --acl2 "$ACL2" > build/freeze/acquire-default.txt 2>&1 || { tail -20 build/freeze/acquire-default.txt; exit 1; }
FN_ACL2=$ACL2 python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/freeze/validate-default.txt 2>&1 || { tail -20 build/freeze/validate-default.txt; exit 1; }
echo "== build developer"
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/freeze/native-build-developer.log swarm-build sh tools/build_native_host.sh > build/freeze/dev.out 2>&1 || { tail -30 build/freeze/dev.out; tail -30 build/freeze/native-build-developer.log; exit 1; }
sha256sum build/fn-host* | tee build/freeze/images.sha256
echo "== done"

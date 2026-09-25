#!/bin/sh
# usage: build.sh TREE -- acquire/validate the default profile's certificates and build the developer and profiling images
set -eu
ROOT=$1
S=/tank/fn/scratch/rep-wave-c
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
cd "$ROOT"; mkdir -p build/freeze
FN_ACL2=$ACL2 python3 tools/proof_artifacts.py acquire --profile default --acl2 "$ACL2" --cache "$CACHE" > build/freeze/acquire-default.txt 2>&1 || { tail -30 build/freeze/acquire-default.txt; exit 1; }
tail -3 build/freeze/acquire-default.txt
FN_ACL2=$ACL2 python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/freeze/validate-default.txt 2>&1 || { tail -20 build/freeze/validate-default.txt; exit 1; }
tail -3 build/freeze/validate-default.txt
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/freeze/native-build-developer.log swarm-build sh tools/build_native_host.sh
awk -v hook=$S/prof-hook.lisp '/^\(defttag nil\)/{while((getline l < hook)>0) print l} {print}' host/native/build.lisp > build/prof-build.lisp
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=build/prof-build.lisp FN_NATIVE_IMAGE=build/fn-host-developer-prof FN_NATIVE_LOG=build/freeze/native-build-prof.log swarm-build sh tools/build_native_host.sh
sha256sum build/fn-host-developer* build/freeze/*.log build/freeze/*.txt | tee build/freeze/image.sha256
echo BUILD-OK

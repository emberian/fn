#!/bin/sh
# dtn-node-image lane: acquire the certified set and build the DTN pair from this tree.
set -eu
T=/tank/fn/scratch/dtn-node-image/tree
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
cd "$T"
mkdir -p build/lane
for p in dtn default; do
  python3 tools/proof_artifacts.py acquire --profile $p --root "$T" --cache "$CACHE" --acl2 "$ACL2" > build/lane/acquire-$p.txt 2>&1 || { cat build/lane/acquire-$p.txt; exit 1; }
  FN_ACL2=$ACL2 python3 tools/proof_artifacts.py validate --profile $p --acl2 "$ACL2" > build/lane/validate-$p.txt 2>&1 || { cat build/lane/validate-$p.txt; exit 1; }
  tail -n 2 build/lane/validate-$p.txt
done
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn FN_NATIVE_LOG=build/lane/native-build-dtn.log swarm-build sh tools/build_native_host.sh
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn-developer FN_NATIVE_LOG=build/lane/native-build-dtn-developer.log swarm-build sh tools/build_native_host.sh
sha256sum build/fn-host-dtn build/fn-host-dtn.core build/fn-host-dtn-developer build/fn-host-dtn-developer.core

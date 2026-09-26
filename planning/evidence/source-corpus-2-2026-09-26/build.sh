#!/bin/sh
set -eu
ROOT=${ROOT:-/tank/fn/scratch/source-corpus-2/tree}
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
cd "$ROOT"
mkdir -p build/freeze
python3 tools/proof_artifacts.py acquire --profile dtn --root "$ROOT" --cache "$CACHE" --acl2 "$ACL2" > build/freeze/acquire-dtn.txt 2>&1 || { tail -20 build/freeze/acquire-dtn.txt; exit 1; }
FN_ACL2=$ACL2 python3 tools/proof_artifacts.py validate --profile dtn --acl2 "$ACL2" > build/freeze/validate-dtn.txt 2>&1 || { tail -20 build/freeze/validate-dtn.txt; exit 1; }
echo "== build dtn developer"
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn-developer FN_NATIVE_LOG=build/freeze/native-build-dtn-developer.log swarm-build sh tools/build_native_host.sh > build/freeze/dtn-dev.out 2>&1 || { tail -30 build/freeze/dtn-dev.out; tail -30 build/freeze/native-build-dtn-developer.log; exit 1; }
# PKT-284: build_native_host.sh can exit 0 after an ACL2 error; read the log
if grep -n -E "ACL2 Error|HARD ACL2 ERROR|Raw Lisp Break|debugger invoked|Unhandled" build/freeze/native-build-dtn-developer.log; then echo "== build log has errors"; exit 1; fi
sha256sum build/fn-host* | tee build/freeze/images.sha256
echo "== done"

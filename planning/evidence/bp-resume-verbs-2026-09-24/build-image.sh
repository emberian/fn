#!/bin/sh
# bp-resume-verbs lane: build the DTN developer image from the lane tree.
set -u
S=/tank/fn/scratch/bp-resume
T=$S/img-tree
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
export FN_ACL2=$ACL2 FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
cd "$T"
mkdir -p build/lane
python3 tools/proof_artifacts.py acquire --profile dtn --root "$T" --cache "$CACHE" --acl2 "$ACL2" > build/lane/acquire-dtn.txt 2>&1 || {
  echo "acquire refused; composing per-book pairs (certs.py install-partial)"
  python3 tools/certs.py --root . --cache "$CACHE" --acl2 "$ACL2" --toolchain-identity d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0 install-partial $(python3 tools/proof_artifacts.py roots --profile dtn | grep -E "^(books|tests|host)/") > build/lane/install-dtn.txt 2>&1
  grep -v "installed:" build/lane/install-dtn.txt | tail -3; }
python3 tools/proof_artifacts.py validate --profile dtn --acl2 "$ACL2" > build/lane/validate-dtn.txt 2>&1 || { tail -8 build/lane/validate-dtn.txt; echo VALIDATE-FAILED; exit 1; }
tail -n 2 build/lane/validate-dtn.txt
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn-developer FN_NATIVE_LOG=build/lane/native-build-dtn-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -1
echo "undefined lines: $(grep -ci undefined build/lane/native-build-dtn-developer.log)"
sha256sum build/fn-host-dtn-developer build/fn-host-dtn-developer.core
echo BUILD-DONE

#!/bin/sh
set -u
S=/tank/fn/scratch/m4-native-request
T=$S/img-tree
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
export FN_ACL2=$ACL2 FN_CERT_CACHE=$CACHE FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
cd "$T"
python3 tools/proof_artifacts.py acquire --profile default --root "$T" --cache "$CACHE" --acl2 "$ACL2" > build/lane/acquire-default.txt 2>&1 || {
  python3 tools/certs.py --root . --cache "$CACHE" --acl2 "$ACL2" --toolchain-identity d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0 install-partial $(python3 tools/proof_artifacts.py roots --profile default | grep -E "^(books|tests|host)/") > build/lane/install-default.txt 2>&1; }
python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/lane/validate-default.txt 2>&1 || { tail -5 build/lane/validate-default.txt; echo VALIDATE-DEFAULT-FAILED; }
tail -n 1 build/lane/validate-default.txt
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/lane/native-build-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -1
echo "default undefined lines: $(grep -ci undefined build/lane/native-build-developer.log)"
sha256sum build/fn-host-developer build/fn-host-developer.core
export FN_NATIVE_SOURCE_ROOT=$T FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer FN_NATIVE_BP_NODE_HOST=$T/build/fn-host-dtn-developer FN_NATIVE_DTN_DEVELOPER_HOST=$T/build/fn-host-dtn-developer
L=$S/tests; mkdir -p $L
for m in test_bp_obligation_native test_native_image_profiles test_bp_node_native; do
  s=$(date +%s)
  timeout 3600 python3 -m unittest tests.$m > $L/$m.log 2>&1; rc=$?
  echo "$m rc=$rc $(( $(date +%s) - s ))s $(tail -1 $L/$m.log) $(sha256sum $L/$m.log | cut -c1-16)"
done
echo TESTS-DONE

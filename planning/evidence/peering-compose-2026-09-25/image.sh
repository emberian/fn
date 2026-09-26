#!/bin/sh
# peering-compose: build the developer image from the lane's gate tree on
# hbox and run the native cases.  Run ON hbox:
#   sh image.sh /tank/fn/gates/peering-compose-rN [build|test|trace|both]
# `trace` runs the packet-7 decline case against the pre-packet image of
# lane/peer-keys (tree 81a2c7b6) with FN_KS_REOPEN_EXPECT=acts.
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
rm -rf build/lane/pull-evidence; mkdir -p build/lane/pull-evidence
python3 -m unittest -v tests.test_native_peer_invite > build/lane/native-peer-invite.log 2>&1; echo "peer-invite rc=$?"
python3 -m unittest -v tests.test_native_key_statements > build/lane/native-key-statements.log 2>&1; echo "key-statements rc=$?"
FN_PULL_EVIDENCE=$T/build/lane/pull-evidence FN_INN_SRC=/tank/fn/inn/2.7.4 python3 -m unittest -v tests.test_native_peer_pull > build/lane/native-peer-pull.log 2>&1; echo "peer-pull rc=$?"
grep -hE "^(OK|FAILED)|Error|ok$|FAIL|skipped" build/lane/native-peer-invite.log build/lane/native-key-statements.log build/lane/native-peer-pull.log
sha256sum build/lane/native-*.log
fi
if [ "$WHAT" = trace ]; then
FN_KS_REOPEN_EXPECT=acts FN_NATIVE_HOST=/tank/fn/scratch/peer-keys/tree-81a2c7b6/build/fn-host-developer python3 -m unittest -v tests.test_native_key_statements.NativeKeyStatementTests.test_a_decline_across_a_restart_with_a_grant_added > build/lane/native-ks-trace-old.log 2>&1; echo "trace rc=$?"
grep -E "WITNESS|^(OK|FAILED)" build/lane/native-ks-trace-old.log
sha256sum build/lane/native-ks-trace-old.log /tank/fn/scratch/peer-keys/tree-81a2c7b6/build/fn-host-developer.core
fi

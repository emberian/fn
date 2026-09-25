#!/bin/sh
# spike/control: certify the image closure and build the developer image on hbox.
set -u
S=/tank/fn/scratch/spike-control
T=$S/tree
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
cd "$T"
mkdir -p build/lane
ROOTS="$(cat $S/roots.txt) tests/acl2/control-exec-tests tests/acl2/control-tests"
TC=$(python3 tools/acl2_toolchain.py identity "$ACL2")
echo "== install-partial $(date -u +%H:%M:%S)"
python3 tools/certs.py --cache /tank/fn/certcache --toolchain-identity "$TC" --acl2 "$ACL2" install-partial $ROOTS 2>&1 | tail -4
echo "== certify $(date -u +%H:%M:%S)"
FN_ACL2=$ACL2 FN_ACL2_TIMEOUT_SECONDS=1800 FN_CERT_CACHE=/tank/fn/certcache \
  swarm-build python3 tools/certify_books.py --jobs 14 --incremental --no-publish ${PCERT:+--pcert} $ROOTS > build/lane/certify.log 2>&1
echo "certify rc=$?"
tail -15 build/lane/certify.log
[ "${SKIP_IMAGE:-}" = 1 ] && exit 0
echo "== validate $(date -u +%H:%M:%S)"
python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/lane/validate.txt 2>&1 || { tail -8 build/lane/validate.txt; echo VALIDATE-FAILED; exit 1; }
tail -n 2 build/lane/validate.txt
echo "== image $(date -u +%H:%M:%S)"
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/lane/native-build-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -3
echo "undefined lines: $(grep -ci undefined build/lane/native-build-developer.log)"
sha256sum build/fn-host-developer build/fn-host-developer.core
echo "== done $(date -u +%H:%M:%S)"

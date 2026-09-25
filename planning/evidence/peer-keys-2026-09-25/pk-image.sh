#!/bin/sh
# peer-keys: certify the default image closure incrementally on hbox, build the developer image, run SCN-053 natively.
set -u
T=$1; L=$2
mkdir -p $L
cd $T
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib FN_TEST_OPENSSL=$FN_OPENSSL_PREFIX/bin/openssl
ROOTS=$(python3 -c "
import sys; sys.path.insert(0,'tools')
from pathlib import Path
import proof_artifacts as p
print(' '.join(sorted(set(p.profile_roots(Path('.'),'default')))))")
echo roots $(echo "$ROOTS" | wc -w)
date -u +cert-start=%FT%TZ
swarm-build python3 tools/certify_books.py --incremental --jobs 8 --timeout-seconds 1800 $ROOTS > $L/certify-image.log 2>&1 || { echo CERT-FAILED; tail -5 $L/certify-image.log; exit 1; }
tail -3 $L/certify-image.log
date -u +build-start=%FT%TZ
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=$L/native-build-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -2
echo "undefined lines: $(grep -ci undefined $L/native-build-developer.log)"
sha256sum build/fn-host-developer build/fn-host-developer.core $L/native-build-developer.log | tee $L/image.sha256
date -u +test-start=%FT%TZ
FN_NATIVE_HOST=$T/build/fn-host-developer python3 -m unittest -v tests.test_native_key_statements > $L/native-key-statements.log 2>&1; echo "native rc=$?"
grep -E "NATIVE-KEY-STATEMENT-WITNESS|^(OK|FAILED)|Error|ok$|FAIL" $L/native-key-statements.log
sha256sum $L/native-key-statements.log

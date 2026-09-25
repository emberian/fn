#!/bin/sh
# operator-verdicts: certify the default closure incrementally, build the developer and production images.
set -eu
T=/tank/fn/scratch/operator-verdicts/tree; L=/tank/fn/scratch/operator-verdicts/logs
mkdir -p $L
cd $T
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
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
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=$L/native-build-developer.log swarm-build sh tools/build_native_host.sh
FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host FN_NATIVE_LOG=$L/native-build-production.log swarm-build sh tools/build_native_host.sh
date -u +done=%FT%TZ
sha256sum build/fn-host build/fn-host-developer | tee $L/image.sha256
echo BUILD-OK

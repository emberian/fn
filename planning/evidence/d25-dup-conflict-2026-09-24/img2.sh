#!/bin/sh
set -x
S=/tank/fn/scratch/d25-dup
T=$S/img
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
cd $T || exit 1
date -u +%FT%TZ > $S/img.start
swarm-build python3 tools/certify_books.py --incremental --jobs 4 --timeout-seconds 1800 $(cat roots.txt) || exit 3
python3 tools/proof_artifacts.py acquire --profile default --root $T --cache $FN_CERT_CACHE --acl2 $FN_ACL2 || exit 4
python3 tools/proof_artifacts.py validate --profile default --root $T --cache $FN_CERT_CACHE --acl2 $FN_ACL2 || exit 5
FN_NATIVE_PROFILE=production swarm-build sh tools/build_native_host.sh || exit 6
FN_NATIVE_PROFILE=developer swarm-build sh tools/build_native_host.sh || exit 7
ls -la build/ | grep fn-host
sha256sum build/fn-host build/fn-host.core build/fn-host-developer build/fn-host-developer.core > $S/image.sha256
date -u +%FT%TZ > $S/img.end
echo IMAGE-DONE

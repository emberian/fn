#!/bin/sh
# spike-storage: certify the image closure incrementally from the cache, build dev + production images
set -u
S=/tank/fn/scratch/spike-storage; T=$S/tree; L=$S/logs
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
cd $T
python3 tools/proof_artifacts.py roots --profile default 2>/dev/null | grep "^books/\|^tests/" > $L/roots.txt
swarm-build python3 tools/certify_books.py --incremental --jobs 8 --timeout-seconds 1200 $(cat $L/roots.txt) > $L/cert.log 2>&1
echo cert rc=$?; tail -3 $L/cert.log
python3 tools/proof_artifacts.py acquire --profile default --acl2 $FN_ACL2 --cache $FN_CERT_CACHE > $L/acquire.log 2>&1; echo acquire rc=$?; tail -2 $L/acquire.log
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=$L/native-build-developer.log swarm-build sh tools/build_native_host.sh > $L/build-developer.out 2>&1; echo dev rc=$?
FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host FN_NATIVE_LOG=$L/native-build-production.log swarm-build sh tools/build_native_host.sh > $L/build-production.out 2>&1; echo prod rc=$?
sha256sum build/fn-host* | tee $L/image.sha256
echo SETUP-DONE

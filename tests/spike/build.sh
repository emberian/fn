#!/bin/sh
# spike-storage: rebuild the developer image (and production when $1=all) from the synced tree; certs come from the cache.
set -u
S=/tank/fn/scratch/spike-storage; T=$S/tree; L=$S/logs
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
cd $T
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=$L/native-build-developer.log swarm-build sh tools/build_native_host.sh > $L/build-developer.out 2>&1; echo dev rc=$?
tail -3 $L/build-developer.out
if [ "${1:-}" = all ]; then
FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host FN_NATIVE_LOG=$L/native-build-production.log swarm-build sh tools/build_native_host.sh > $L/build-production.out 2>&1; echo prod rc=$?
FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn FN_NATIVE_LOG=$L/native-build-dtn.log swarm-build sh tools/build_native_host.sh > $L/build-dtn.out 2>&1; echo dtn rc=$?
fi
sha256sum build/fn-host* | tee $L/image.sha256

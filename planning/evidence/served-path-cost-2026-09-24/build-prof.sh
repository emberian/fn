#!/bin/sh
set -eu
ROOT=$1
cd "$ROOT"
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
awk '/^\(defttag nil\)/{while((getline l < "/tank/fn/scratch/served-path-cost/sprof-hook.lisp")>0) print l} {print}' host/native/build.lisp > build/prof-build.lisp
FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=build/prof-build.lisp FN_NATIVE_IMAGE=build/fn-host-developer-prof FN_NATIVE_LOG=build/freeze/native-build-prof.log swarm-build sh tools/build_native_host.sh
echo PROF-OK

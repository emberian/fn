#!/bin/sh
# usage: prof-build.sh TREE -- the profiling twin (hot-path-scans-2 build.sh recipe) of TREE s developer image
set -eu
T=$1; M=/tank/fn/scratch/served-path-scale-2/m
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
cd $T
awk -v hook=/tank/fn/scratch/hot-path-scans-2/prof-hook.lisp "/^\(defttag nil\)/{while((getline l < hook)>0) print l} {print}" host/native/build.lisp > build/prof-build.lisp
grep -c prof-raw build/prof-build.lisp
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=build/prof-build.lisp FN_NATIVE_IMAGE=build/fn-host-developer-prof FN_NATIVE_LOG=$M/prof-build-$(basename $(dirname $T)).log swarm-build sh tools/build_native_host.sh
sha256sum build/fn-host-developer-prof.core
echo PROF-BUILD-OK

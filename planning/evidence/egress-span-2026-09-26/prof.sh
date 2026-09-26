#!/bin/sh
# egress-span: the profiling twin of the lane's developer image (perf-ledger's
# setup.sh recipe: prof-raw.lisp spliced before (defttag nil)), in the
# hbox_native tree whose certified books and artifact set it reuses.
S=/tank/fn/scratch/egress-span/native-a6660cb8; T=$S/tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
cd $T
awk -v hook=/tank/fn/scratch/perf-ledger/prof-hook.lisp '/^\(defttag nil\)/{while((getline l < hook)>0) print l} {print}' host/native/build.lisp > build/prof-build.lisp
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=build/prof-build.lisp FN_NATIVE_IMAGE=build/fn-host-developer-prof FN_NATIVE_LOG=$S/logs/native-build-prof.log swarm-build sh tools/build_native_host.sh > $S/build-prof.out 2>&1
echo prof rc=$?
sha256sum build/fn-host-developer build/fn-host-developer.core build/fn-host-developer-prof build/fn-host-developer-prof.core | tee $S/prof-image.sha256

#!/bin/sh
# perf-ledger: ship-side setup on hbox. usage: setup.sh -- certify the default
# profile roots from the cache, build the developer image and its profiling
# twin (prof-raw.lisp: FN_PROF_LOAD, FN_SPROF_DIR) from /tank/fn/scratch/perf-ledger/tree.
set -u
S=/tank/fn/scratch/perf-ledger; T=$S/tree
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g; CACHE=/tank/fn/certcache
export FN_ACL2=$ACL2 FN_CERT_CACHE=$CACHE FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
cd $T && mkdir -p build/freeze
python3 tools/proof_artifacts.py roots --profile default 2>/dev/null | grep "^books/\|^tests/" > $S/roots.txt
swarm-build python3 tools/certify_books.py --incremental --jobs 8 --timeout-seconds 900 $(cat $S/roots.txt) > $S/cert.log 2>&1; echo cert rc=$?
python3 tools/proof_artifacts.py acquire --profile default --acl2 "$ACL2" --cache "$CACHE" > build/freeze/acquire.txt 2>&1; echo acquire rc=$?
python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/freeze/validate.txt 2>&1; echo validate rc=$?
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/freeze/native-build-developer.log swarm-build sh tools/build_native_host.sh > $S/build-dev.log 2>&1; echo dev rc=$?
echo "(progn! (set-raw-mode t) (load \"$S/prof-raw.lisp\"))" > $S/prof-hook.lisp
awk -v hook=$S/prof-hook.lisp '/^\(defttag nil\)/{while((getline l < hook)>0) print l} {print}' host/native/build.lisp > build/prof-build.lisp
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=build/prof-build.lisp FN_NATIVE_IMAGE=build/fn-host-developer-prof FN_NATIVE_LOG=build/freeze/native-build-prof.log swarm-build sh tools/build_native_host.sh > $S/build-prof.log 2>&1; echo prof rc=$?
sha256sum build/fn-host-developer build/fn-host-developer.core build/fn-host-developer-prof build/fn-host-developer-prof.core | tee $S/image.sha256
echo SETUP-DONE

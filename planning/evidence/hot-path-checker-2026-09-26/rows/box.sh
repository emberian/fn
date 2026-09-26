#!/bin/sh
set -u
T=/tank/fn/scratch/hot-path-checker/tree-56f94181; H=/tank/fn/scratch/hot-path-checker/hook; R=/tank/fn/scratch/hot-path-checker/results-56f94181
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
cd $T
printf '(progn! (set-raw-mode t) (load "%s/prof-raw.lisp"))\n' $H > $H/prof-hook.lisp
python3 tools/proof_artifacts.py roots --profile default 2>/dev/null | grep '^books/\|^tests/' > $R/roots.txt
swarm-build python3 tools/certify_books.py --incremental --jobs 8 --timeout-seconds 900 $(cat $R/roots.txt) > $R/cert.log 2>&1
echo "cert rc=$?" > $R/setup.out
mkdir -p build/freeze
python3 tools/proof_artifacts.py acquire --profile default --acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache > build/freeze/acquire-default.txt 2>&1 || { echo acquire-failed >> $R/setup.out; echo 3 > $R/done; exit 3; }
python3 tools/proof_artifacts.py validate --profile default --acl2 /tank/fn/toolchains/w28/acl2-literal-4g > build/freeze/validate-default.txt 2>&1 || { echo validate-failed >> $R/setup.out; echo 4 > $R/done; exit 4; }
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/freeze/native-build-developer.log swarm-build sh tools/build_native_host.sh >> $R/setup.out 2>&1 || { echo 5 > $R/done; exit 5; }
awk -v hook=$H/prof-hook.lisp '/^\(defttag nil\)/{while((getline l < hook)>0) print l} {print}' host/native/build.lisp > build/prof-build.lisp
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=build/prof-build.lisp FN_NATIVE_IMAGE=build/fn-host-developer-prof FN_NATIVE_LOG=build/freeze/native-build-prof.log swarm-build sh tools/build_native_host.sh >> $R/setup.out 2>&1 || { echo 6 > $R/done; exit 6; }
sha256sum build/fn-host-developer* > $R/image.sha256
python3 tools/scale_probe.py run --tree $T --hook $H --work /dev/shm/hot-path-checker-56f94181 --out $R --vary both --samples 32 > $R/runs.out 2>&1
rm -rf /dev/shm/hot-path-checker-56f94181
(cd $R && sha256sum *.json *.log *.out > SHA256SUMS)

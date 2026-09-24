#!/bin/sh
# d23-issuer-authority lane: build the DTN developer image from the lane
# commit, then the release-authority labs (control, 1 relay with and without
# the release row, 2 relays with it).
set -u
S=/tank/fn/scratch/d23-issuer
REV=$(cat $S/REV)
T=$S/img-tree
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
export FN_ACL2=$ACL2 FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
cd "$T"
mkdir -p build/lane
p=dtn
python3 tools/proof_artifacts.py acquire --profile $p --root "$T" --cache "$CACHE" --acl2 "$ACL2" > build/lane/acquire-$p.txt 2>&1 || {
  echo "acquire refused; composing per-book pairs (certs.py install-partial)"
  python3 tools/certs.py --root . --cache "$CACHE" --acl2 "$ACL2" --toolchain-identity d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0 install-partial $(python3 tools/proof_artifacts.py roots --profile $p | grep -E "^(books|tests|host)/") > build/lane/install-$p.txt 2>&1
  grep -v "installed:" build/lane/install-$p.txt | tail -3; }
python3 tools/proof_artifacts.py validate --profile $p --acl2 "$ACL2" > build/lane/validate-$p.txt 2>&1 || { tail -5 build/lane/validate-$p.txt; echo VALIDATE-FAILED; exit 1; }
tail -n 2 build/lane/validate-$p.txt
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn-developer FN_NATIVE_LOG=build/lane/native-build-dtn-developer.log swarm-build sh tools/build_native_host.sh 2>&1 | tail -1
echo "undefined lines: $(grep -ci undefined build/lane/native-build-dtn-developer.log)"
sha256sum build/fn-host-dtn-developer build/fn-host-dtn-developer.core
IMG=$T/build/fn-host-dtn-developer
LAB=$S/lab-src/tests/bp-dtn7/run_fn_dtn7_app_receipt.py
R=$S/final; rm -rf $R; mkdir -p $R
cd $S/lab-src
python3 $LAB --image $IMG --relays 0 --work $R/control > $R/control.out 2>&1; echo "control rc=$?"
python3 $LAB --image $IMG --relays 1 --a-releases none --dtn7-repo /tank/fn/dtn7/repo --work $R/relay1-none > $R/relay1-none.out 2>&1; echo "relay1-none rc=$?"
python3 $LAB --image $IMG --relays 1 --a-releases listed --dtn7-repo /tank/fn/dtn7/repo --work $R/relay1-listed > $R/relay1-listed.out 2>&1; echo "relay1-listed rc=$?"
python3 $LAB --image $IMG --relays 2 --a-releases listed --dtn7-repo /tank/fn/dtn7/repo --work $R/relay2-listed > $R/relay2-listed.out 2>&1; echo "relay2-listed rc=$?"
echo ALLDONE

#!/bin/sh
# signed-receipts lane: build the DTN developer image from the lane commit,
# then the two signed-receipt labs (one dtn7 relay, A's return boundary
# carries B with NO release row and require-signed-receipts).
set -u
S=/tank/fn/scratch/signed-receipts
REV=$(cat $S/REV)  # archived to $S/src.tar
T=$S/img-tree
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
ENROLL=/tank/fn/scratch/qual-c3420013/tree/build/fn-host-developer
export FN_ACL2=$ACL2 FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib FN_TEST_OPENSSL=$FN_OPENSSL_PREFIX/bin/openssl
rm -rf $T $S/lab-src; mkdir -p $T $S/lab-src
tar -x -C $T -f $S/src.tar
tar -x -C $S/lab-src -f $S/src.tar
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
sha256sum build/fn-host-dtn-developer build/fn-host-dtn-developer.core $ENROLL
IMG=$T/build/fn-host-dtn-developer
LAB=$S/lab-src/tests/bp-dtn7/run_fn_dtn7_app_receipt.py
R=$S/final; rm -rf $R; mkdir -p $R
cd $S/lab-src
python3 $LAB --image $IMG --relays 1 --a-releases none --signed-receipts $ENROLL --dtn7-repo /tank/fn/dtn7/repo --work $R/relay1-signed > $R/relay1-signed.out 2>&1; echo "relay1-signed rc=$?"
python3 $LAB --image $IMG --relays 1 --a-releases none --signed-receipts $ENROLL --flip-signature --dtn7-repo /tank/fn/dtn7/repo --work $R/relay1-flipped > $R/relay1-flipped.out 2>&1; echo "relay1-flipped rc=$?"
echo ALLDONE

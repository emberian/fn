#!/bin/sh
# usage: build.sh TREE LABEL -- certify the default proof_artifacts roots in
# place (incremental, from /tank/fn/certcache), then build the developer image.
set -u
T=$1; L=$2; S=/tank/fn/scratch/d24-peer
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g; CACHE=/tank/fn/certcache
export FN_ACL2=$ACL2 FN_CERT_CACHE=$CACHE FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
cd $T; mkdir -p build/freeze
python3 tools/proof_artifacts.py roots --profile default 2>/dev/null | grep "^books/\|^tests/" > $S/$L-roots.txt
swarm-build python3 tools/certify_books.py --incremental --jobs 8 --timeout-seconds 900 $(cat $S/$L-roots.txt) > $S/$L-cert.log 2>&1
echo cert rc=$?; tail -2 $S/$L-cert.log
python3 tools/proof_artifacts.py acquire --profile default --acl2 "$ACL2" --cache "$CACHE" > build/freeze/acquire-default.txt 2>&1 || { tail -30 build/freeze/acquire-default.txt; exit 1; }
python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/freeze/validate-default.txt 2>&1 || { tail -20 build/freeze/validate-default.txt; exit 1; }
tail -2 build/freeze/validate-default.txt
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/freeze/native-build-developer.log swarm-build sh tools/build_native_host.sh > $S/$L-image.log 2>&1
echo image rc=$?; tail -2 $S/$L-image.log
sha256sum build/fn-host-developer build/fn-host-developer.core | tee $S/$L-image.sha256

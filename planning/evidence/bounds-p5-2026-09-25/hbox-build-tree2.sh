#!/bin/sh
# Build both images from tree2 = adbf4c9c + the three replay-fix files of dev (b5f7340d).
set -eu
S=/tank/fn/scratch/bounds-p5
T=$S/tree2
cd $T
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
mkdir -p $S/bin; ln -sf $FN_ACL2 $S/bin/acl2; export PATH=$S/bin:$PATH
B=$(grep -ho "include-book \"[^\"]*\"" host/native/build.lisp host/*.lisp 2>/dev/null | sed "s/include-book \"//; s/\"$//; s#^\.\./##" | grep "^books/" | sort -u)
swarm-build python3 tools/certify_books.py --incremental --jobs 14 --timeout-seconds 1800 $B tests/acl2/checkpoint-pack-chain-tests tests/acl2/store-compact-verb-tests tests/acl2/config-physical-replay-tests > $S/certify-tree2.log 2>&1 || { tail -15 $S/certify-tree2.log; exit 1; }
tail -3 $S/certify-tree2.log
for P in developer production; do if [ $P = developer ]; then I=build/fn-host-developer; else I=build/fn-host; fi; FN_NATIVE_PROFILE=$P FN_NATIVE_IMAGE=$I FN_NATIVE_LOG=build/native-$P.log swarm-build sh tools/build_native_host.sh > $S/build-$P-tree2.log 2>&1 || { tail -20 build/native-$P.log; exit 1; }; done
sha256sum build/fn-host.core build/fn-host-developer.core $S/certify-tree2.log

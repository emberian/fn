#!/bin/sh
# usage: native.sh N   -- run the source-corpus module against the lane's developer image
T=/tank/fn/scratch/source-corpus/tree
L=/tank/fn/scratch/source-corpus/logs
mkdir -p $L
cd $T
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_TEST_OPENSSL=/tank/fn/toolchains/openssl-3.5.8/bin/openssl
export FN_NATIVE_HOST=$T/build/fn-host-developer FN_NATIVE_SOURCE_ROOT=$T PYTHONDONTWRITEBYTECODE=1
systemd-run --user --scope -q -p MemoryMax=24G python3 -m unittest -v tests.test_native_source_corpus > $L/native-$1.log 2>&1
echo rc=$?
sha256sum $L/native-$1.log

#!/bin/sh
# usage: native.sh N [MODULE]   (TREE defaults to $S/tree; MODULE to tests.test_native_source_corpus_bp)
S=/tank/fn/scratch/source-corpus-2
TREE=${TREE:-$S/tree}
MODULE=${2:-tests.test_native_source_corpus_bp}
cd $TREE
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib PYTHONDONTWRITEBYTECODE=1
export FN_TEST_OPENSSL=/tank/fn/toolchains/openssl-3.5.8/bin/openssl
export FN_NATIVE_HOST=$TREE/build/fn-host-developer FN_NATIVE_DTN_HOST=$TREE/build/fn-host-dtn-developer FN_DTN7_REPO=/tank/fn/dtn7/repo
rm -rf $S/diag$1; mkdir -p $S/diag$1
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag$1
T0=$(date +%s); python3 -m unittest -v $MODULE > $S/native-$1.log 2>&1; echo "rc=$? wall=$(($(date +%s)-T0))" >> $S/native-$1.log

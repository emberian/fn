#!/bin/sh
# spike/control: run the two-node control lab against the developer image.
set -u
S=/tank/fn/scratch/spike-control
T=$S/tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
cd "$T"
REV=$(cat $S/rev.txt)
LOG=$S/lab-$REV.log
FN_RUN_HYBRID_E2E=1 FN_TEST_OPENSSL=$FN_OPENSSL_PREFIX/bin/openssl FN_NATIVE_HOST=$T/build/fn-host-developer \
  python3 -m unittest -v tests.test_native_control_exec > $LOG 2>&1
echo "lab rc=$?"
sha256sum $LOG build/fn-host-developer build/fn-host-developer.core
grep -E "^LAB|^(OK|FAILED)|Error|FAIL" $LOG | cut -c1-240

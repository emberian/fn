#!/bin/sh
# usage: ntest.sh <image> <source-sha> <log> <test-selector...>
IMG=$1; SRC=$2; LOG=$3; shift 3
cd /tank/fn/scratch/transit-436/tree-a3e10e74
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_NATIVE_HOST=$IMG FN_NATIVE_IMAGE_SOURCE_SHA=$SRC
export FN_NATIVE_LAUNCHER_SHA256=$(sha256sum $IMG | cut -d' ' -f1) FN_NATIVE_CORE_SHA256=$(sha256sum $IMG.core | cut -d' ' -f1)
RT=$(dirname $IMG)/runtime/sbcl; [ -f "$RT" ] || RT=$(grep -o "/[^\" ]*bin/sbcl" $IMG | head -1)
export FN_NATIVE_RUNTIME_SHA256=$(sha256sum $RT | cut -d' ' -f1)
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_NATIVE_DEVELOPER_HOST=$IMG FN_NATIVE_DEVELOPER_CORE_SHA256=$FN_NATIVE_CORE_SHA256 FN_NATIVE_DEVELOPER_LAUNCHER_SHA256=$FN_NATIVE_LAUNCHER_SHA256
echo "runtime=$RT"
python3 -m unittest -v "$@" > $LOG 2>&1; echo "rc=$?"
tail -25 $LOG; sha256sum $LOG

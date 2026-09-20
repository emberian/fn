#!/bin/sh
# Build build/fn-host: one SBCL image holding ACL2, the certified books the
# hosts drive, the :program host wrappers, and host/native/io.lisp.
#
# Requires `make certify` to have produced certificates: an uncertified book
# fails this build rather than being loaded with a warning.
set -eu
cd "$(dirname "$0")/.."
ACL2="${FN_ACL2:-acl2}"
# FN_NATIVE_BUILD selects the session script and FN_NATIVE_IMAGE the image it
# saves; the two must agree, because the `save-exec` path lives in the script.
# The default pair is the deployment image. host/native/build-dtn.lisp is the
# DTN-only variant and says in its own header what it leaves out.
BUILD="${FN_NATIVE_BUILD:-host/native/build.lisp}"
IMAGE="${FN_NATIVE_IMAGE:-build/fn-host}"
LOG="${FN_NATIVE_LOG:-build/native-host-build.log}"
mkdir -p build
rm -f "$IMAGE" "$IMAGE.core"
if ! ACL2_CUSTOMIZATION=NONE ACL2_SYSTEM_BOOKS= env -u ACL2_SYSTEM_BOOKS \
     "$ACL2" < "$BUILD" > "$LOG" 2>&1; then
    echo "build_native_host: acl2 exited with status $?; see $LOG" >&2
    exit 1
fi
if grep -q -E 'ACL2 Error|HARD ACL2 ERROR|ABORTING from raw Lisp|Uncertified' "$LOG"; then
    echo "build_native_host: error or uncertified-book marker in $LOG" >&2
    grep -n -E 'ACL2 Error|HARD ACL2 ERROR|ABORTING from raw Lisp|Uncertified' "$LOG" | head -5 >&2
    exit 1
fi
if ! grep -q 'FN_NATIVE_BUILD_LOADED' "$LOG"; then
    echo "build_native_host: ready marker missing from $LOG" >&2
    exit 1
fi
if [ ! -x "$IMAGE" ] || [ ! -s "$IMAGE.core" ]; then
    echo "build_native_host: save-exec produced no image; see $LOG" >&2
    exit 1
fi
echo "built $IMAGE ($(du -h "$IMAGE.core" | cut -f1) core)"

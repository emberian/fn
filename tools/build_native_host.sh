#!/bin/sh
# Build build/fn-host: one SBCL image holding ACL2, the certified books the
# hosts drive, the :program host wrappers, and host/native/io.lisp.
#
# Requires `make certify` to have produced certificates: an uncertified book
# fails this build rather than being loaded with a warning.
set -eu
cd "$(dirname "$0")/.."
ACL2="${FN_ACL2:-acl2}"
LOG=build/native-host-build.log
mkdir -p build
rm -f build/fn-host build/fn-host.core
if ! ACL2_CUSTOMIZATION=NONE ACL2_SYSTEM_BOOKS= env -u ACL2_SYSTEM_BOOKS \
     "$ACL2" < host/native/build.lisp > "$LOG" 2>&1; then
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
if [ ! -x build/fn-host ] || [ ! -s build/fn-host.core ]; then
    echo "build_native_host: save-exec produced no image; see $LOG" >&2
    exit 1
fi
echo "built build/fn-host ($(du -h build/fn-host.core | cut -f1) core)"

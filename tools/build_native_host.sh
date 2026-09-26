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
# saves.  The main build reads the latter at save-exec; specialized build
# scripts still document the matching path they require.
# The default pair is the production deployment image.  The developer profile
# is explicit and gets a different default output, so diagnostic service
# entries cannot replace the production image by accident. host/native/build-dtn.lisp
# is the DTN-only variant and says in its own header what it leaves out.
BUILD="${FN_NATIVE_BUILD:-host/native/build.lisp}"
PROFILE="${FN_NATIVE_PROFILE:-production}"
case "$PROFILE" in
  production) DEFAULT_IMAGE=build/fn-host ;;
  developer) DEFAULT_IMAGE=build/fn-host-developer ;;
  *) echo "build_native_host: FN_NATIVE_PROFILE must be production or developer" >&2; exit 2 ;;
esac
if [ "$BUILD" = host/native/build-dtn.lisp ]; then
    case "$PROFILE" in
      production) DEFAULT_IMAGE=build/fn-host-dtn ;;
      developer) DEFAULT_IMAGE=build/fn-host-dtn-developer ;;
    esac
fi
IMAGE="${FN_NATIVE_IMAGE:-$DEFAULT_IMAGE}"
# TLS is the system's libssl (OpenSSL 3.0+ or LibreSSL 3+; tls.lisp checks
# every function it calls at build and at start).  FN_OPENSSL_PREFIX is
# optional: set, it names another matched libcrypto/libssl pair.
if [ -n "${FN_OPENSSL_PREFIX:-}" ]; then
    export FN_OPENSSL_PREFIX
    LD_LIBRARY_PATH="$FN_OPENSSL_PREFIX/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    export LD_LIBRARY_PATH
fi
# ML-DSA-65 is the vendored PQClean library, built into lib/ beside the
# image's core, where the restarted image loads it (signatures.lisp).
LIBDIR=$(dirname "$IMAGE")/lib
sh tools/build_mldsa65.sh "$LIBDIR" >&2
case $(uname -s) in
  Darwin) FN_MLDSA_LIBRARY=$(cd "$LIBDIR" && pwd)/libfn-mldsa65.dylib ;;
  *) FN_MLDSA_LIBRARY=$(cd "$LIBDIR" && pwd)/libfn-mldsa65.so ;;
esac
export FN_MLDSA_LIBRARY
openssl_hint() {
    if grep -q -E 'OpenSSL|LibreSSL|TLS library|libcrypto|libssl' "$LOG" 2>/dev/null; then
        echo "build_native_host: the log names the TLS library; the system needs OpenSSL 3.0+ or LibreSSL 3+ (FN_OPENSSL_PREFIX now: ${FN_OPENSSL_PREFIX:-unset})" >&2
    fi
    if grep -q -E 'ML-DSA' "$LOG" 2>/dev/null; then
        echo "build_native_host: the log names ML-DSA-65; the library is $FN_MLDSA_LIBRARY (tools/build_mldsa65.sh)" >&2
    fi
}
LOG="${FN_NATIVE_LOG:-build/native-host-build.log}"
mkdir -p build
rm -f "$IMAGE" "$IMAGE.core"
if ! FN_NATIVE_PROFILE="$PROFILE" FN_NATIVE_IMAGE="$IMAGE" \
     ACL2_CUSTOMIZATION=NONE ACL2_SYSTEM_BOOKS= env -u ACL2_SYSTEM_BOOKS \
     "$ACL2" < "$BUILD" > "$LOG" 2>&1; then
    echo "build_native_host: acl2 exited with status $?; see $LOG" >&2
    openssl_hint
    exit 1
fi
if grep -q -E 'ACL2 Error|HARD ACL2 ERROR|ABORTING from raw Lisp|Uncertified' "$LOG"; then
    echo "build_native_host: error or uncertified-book marker in $LOG" >&2
    grep -n -E 'ACL2 Error|HARD ACL2 ERROR|ABORTING from raw Lisp|Uncertified' "$LOG" | head -5 >&2
    openssl_hint
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
echo "built $IMAGE profile=$PROFILE ($(du -h "$IMAGE.core" | cut -f1) core)"

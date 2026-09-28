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
# The saved world (HST-025; gpt-6's wave-5 review s.4): the production
# release is stripped (host/native/strip-world.lisp, with IMAGE.world-deps
# beside it); the developer image is full.  FN_NATIVE_WORLD=full with the
# production profile is the reference image (build/fn-host-reference), the
# unstripped twin of the release that qualification compares it against;
# FN_NATIVE_WORLD=stripped with the developer profile is its developer twin
# (build/fn-host-developer-stripped), for the developer-only witnesses.
case "$PROFILE" in
  production) DEFAULT_WORLD=stripped ;;
  developer) DEFAULT_WORLD=full ;;
esac
WORLD="${FN_NATIVE_WORLD:-$DEFAULT_WORLD}"
case "$WORLD" in
  stripped|full) ;;
  *) echo "build_native_host: FN_NATIVE_WORLD must be stripped or full" >&2; exit 2 ;;
esac
if [ "$WORLD" != "$DEFAULT_WORLD" ] && [ "$BUILD" = host/native/build.lisp ]; then
    case "$PROFILE" in
      production) DEFAULT_IMAGE=build/fn-host-reference ;;
      developer) DEFAULT_IMAGE=build/fn-host-developer-stripped ;;
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
# The LZ4 block encoder (vendored LZ4 1.10.0, third_party/lz4/UPSTREAM.txt),
# built into the same lib/: the append's candidate blocks (host/native/lz4.lisp);
# ACL2's proved decoder checks every candidate and does every read.
sh tools/build_lz4.sh "$LIBDIR" >&2
case $(uname -s) in
  Darwin) FN_LZ4_LIBRARY=$(cd "$LIBDIR" && pwd)/libfn-lz4.dylib ;;
  *) FN_LZ4_LIBRARY=$(cd "$LIBDIR" && pwd)/libfn-lz4.so ;;
esac
export FN_LZ4_LIBRARY
# BLAKE3 (fn's digest) is the vendored C behind host/native/fn-blake3.c,
# built beside it; host/native/digest.lisp loads it at build and every start.
sh tools/build_blake3.sh "$LIBDIR" >&2
case $(uname -s) in
  Darwin) FN_BLAKE3_LIBRARY=$(cd "$LIBDIR" && pwd)/libfn-blake3.dylib ;;
  *) FN_BLAKE3_LIBRARY=$(cd "$LIBDIR" && pwd)/libfn-blake3.so ;;
esac
export FN_BLAKE3_LIBRARY
openssl_hint() {
    if grep -q -E 'OpenSSL|LibreSSL|TLS library|libcrypto|libssl' "$LOG" 2>/dev/null; then
        echo "build_native_host: the log names the TLS library; the system needs OpenSSL 3.0+ or LibreSSL 3+ (FN_OPENSSL_PREFIX now: ${FN_OPENSSL_PREFIX:-unset})" >&2
    fi
    if grep -q -E 'ML-DSA' "$LOG" 2>/dev/null; then
        echo "build_native_host: the log names ML-DSA-65; the library is $FN_MLDSA_LIBRARY (tools/build_mldsa65.sh)" >&2
    fi
    if grep -q -E 'BLAKE3|native digest' "$LOG" 2>/dev/null; then
        echo "build_native_host: the log names the native digest; the library is $FN_BLAKE3_LIBRARY (tools/build_blake3.sh)" >&2
    fi
}
LOG="${FN_NATIVE_LOG:-build/native-host-build.log}"
mkdir -p build
rm -f "$IMAGE" "$IMAGE.core" "$IMAGE.world-deps"
if ! FN_NATIVE_PROFILE="$PROFILE" FN_NATIVE_IMAGE="$IMAGE" FN_NATIVE_WORLD="$WORLD" \
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
# Every book loads its compiled file.  Without one ACL2 processes the book's
# events and compiles each definition in core, and SBCL keeps every such
# definition's source form in the image: 114 books without a .fasl grew the
# production core by 8.9 MB (image-growth, 2026-09-28; the cache had lost
# them, tools/certs.py install_entry/write_entry).  Recertify the named books
# (tools/certify_books.py --recertify BOOK) so the cache holds their .fasl.
if grep -q -E 'Unable to (complete )?load (of )?compiled file' "$LOG"; then
    echo "build_native_host: books loaded without their compiled file (.fasl) in $LOG:" >&2
    grep -A2 -E 'Unable to (complete )?load (of )?compiled file' "$LOG" \
        | tr -d '\\\n' | grep -o -E '/[^ ]*\.lisp' | sort -u | head -20 >&2
    exit 1
fi
if ! grep -q 'FN_NATIVE_BUILD_LOADED' "$LOG"; then
    echo "build_native_host: ready marker missing from $LOG" >&2
    exit 1
fi
# The world loaded once (lane image-umbrella; tools/extract/world.py): the
# script included its umbrella book first and no later include-book added a
# book, and the thread-local storage the build used is within its budget.
# Each top-level include-book reloads the compiled files of its closure and
# each load of a constrained stub takes a TLS index SBCL never frees; the
# saved launcher runs at --tls-limit FN_TLS_LIMIT (below), whose capacity in
# SBCL's units is FN_TLS_LIMIT * 8.  FN_TLS_BUDGET_PERCENT (default 25) of
# the smaller of that and the build's own capacity is the budget: an image
# over it is refused here, not at a node's first thread.
case "$BUILD" in
    host/native/build.lisp|host/native/build-dtn.lisp|host/native/build-store-test.lisp)
        if ! grep -q 'FN_IMAGE_WORLD_CLOSED' "$LOG"; then
            echo "build_native_host: FN_IMAGE_WORLD_CLOSED missing from $LOG (an include-book after the umbrella added a book, or the umbrella is not first)" >&2
            exit 1
        fi ;;
esac
TLS_LINE=$(grep -a -o -E 'FN_NATIVE_TLS [0-9]+ [0-9]+' "$LOG" | tail -1 || true)
if [ -n "$TLS_LINE" ]; then
    TLS_USED=$(echo "$TLS_LINE" | cut -d' ' -f2)
    TLS_CAP=$(echo "$TLS_LINE" | cut -d' ' -f3)
    TLS_RUN=$(( ${FN_TLS_LIMIT:-65536} * 8 ))
    [ "$TLS_RUN" -lt "$TLS_CAP" ] && TLS_CAP=$TLS_RUN
    TLS_PCT=${FN_TLS_BUDGET_PERCENT:-25}
    if [ $(( TLS_USED * 100 )) -gt $(( TLS_CAP * TLS_PCT )) ]; then
        echo "build_native_host: the build used TLS index $TLS_USED of $TLS_CAP, over ${TLS_PCT}% (tools/tls_check.py --measure names the books)" >&2
        exit 1
    fi
    echo "build_native_host: TLS index $TLS_USED of $TLS_CAP ($(( TLS_USED * 100 / TLS_CAP ))%)" >&2
else
    case "$BUILD" in
        host/native/build.lisp|host/native/build-dtn.lisp|host/native/build-store-test.lisp)
            echo "build_native_host: FN_NATIVE_TLS missing from $LOG" >&2; exit 1 ;;
    esac
fi
# The saved world is the one asked for (host/native/strip-world.lisp).
if [ "$WORLD" = stripped ]; then
    if ! grep -q 'FN_NATIVE_WORLD_STRIPPED' "$LOG"; then
        echo "build_native_host: world-strip marker missing from $LOG" >&2
        exit 1
    fi
    if ! head -1 "$IMAGE.world-deps" 2>/dev/null | grep -q '^fn-world-deps 2$'; then
        echo "build_native_host: the stripped image has no dependency set $IMAGE.world-deps" >&2
        exit 1
    fi
elif ! grep -q 'FN_NATIVE_WORLD_FULL' "$LOG"; then
    echo "build_native_host: full-world marker missing from $LOG" >&2
    exit 1
fi
if [ ! -x "$IMAGE" ] || [ ! -s "$IMAGE.core" ]; then
    echo "build_native_host: save-exec produced no image; see $LOG" >&2
    exit 1
fi
# The launcher ACL2's save-exec writes execs SBCL with --tls-limit 16384
# (acl2-init.lisp hard-codes it).  The served world passed that limit at
# load (batch AV, "Thread local storage exhausted"), so images build under
# the 65536 wrapper (tools/hbox_native.sh); the saved launcher runs at the
# same limit, or run time could exhaust what build time did not.  The
# frozen launchers (packaging/freeze-native-image.sh) copy this exec line.
FN_TLS_LIMIT=${FN_TLS_LIMIT:-65536}
if ! grep -q -- '--tls-limit 16384 ' "$IMAGE" && ! grep -q -- "--tls-limit $FN_TLS_LIMIT " "$IMAGE"; then
    echo "build_native_host: the launcher $IMAGE names no known --tls-limit; see $LOG" >&2
    exit 1
fi
sed "s/--tls-limit 16384 /--tls-limit $FN_TLS_LIMIT /" "$IMAGE" > "$IMAGE.tls" && \
    chmod 755 "$IMAGE.tls" && mv "$IMAGE.tls" "$IMAGE" || {
    echo "build_native_host: could not set the launcher's --tls-limit" >&2; exit 1; }
grep -q -- "--tls-limit $FN_TLS_LIMIT " "$IMAGE" || {
    echo "build_native_host: the launcher does not run at --tls-limit $FN_TLS_LIMIT" >&2; exit 1; }
# The control stack (PKT-876).  ACL2's save-exec launcher passes
# --control-stack-size 64 (MiB) to every thread, while the installed launcher
# (packaging/fn) passes the profile's figure (books/heap-reservation.lisp
# fn-heap-stack-kib, 1,024 KiB): every native test that ran this launcher
# directly ran with 64 times the deployed stack and could not see a stack
# death the node dies of (thread-stacks: a full-replay open past ~30,000
# articles).  The build prints ACL2's figure (FN_NATIVE_STACK_KIB, build.lisp
# and build-dtn.lisp) and the launcher carries it; SBCL_USER_ARGS at run time
# still overrides it (the installed launcher's per-command figure; a test's
# named opt-in, tests/test_native_operator_verbs.py deployed_stack).
STACK_KIB=$(sed -n 's/.*FN_NATIVE_STACK_KIB \([0-9][0-9]*\).*/\1/p' "$LOG" | tail -1)
if [ -n "$STACK_KIB" ]; then
    grep -q -- '--control-stack-size 64 ' "$IMAGE" || {
        echo "build_native_host: the launcher $IMAGE names no --control-stack-size 64; see $LOG" >&2; exit 1; }
    sed "s/--control-stack-size 64 /--control-stack-size ${STACK_KIB}KB /" "$IMAGE" > "$IMAGE.stack" && \
        chmod 755 "$IMAGE.stack" && mv "$IMAGE.stack" "$IMAGE" || {
        echo "build_native_host: could not set the launcher's --control-stack-size" >&2; exit 1; }
    grep -q -- "--control-stack-size ${STACK_KIB}KB " "$IMAGE" || {
        echo "build_native_host: the launcher does not run at ${STACK_KIB} KiB of control stack" >&2; exit 1; }
else
    case "$BUILD" in
        host/native/build.lisp|host/native/build-dtn.lisp)
            echo "build_native_host: FN_NATIVE_STACK_KIB missing from $LOG" >&2; exit 1 ;;
    esac
    echo "build_native_host: $BUILD prints no stack figure; the launcher keeps ACL2's 64 MiB (not a served image)" >&2
fi
echo "built $IMAGE profile=$PROFILE world=$WORLD ($(du -h "$IMAGE.core" | cut -f1) core)"

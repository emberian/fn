#!/bin/sh
# tools/extract/build.sh TREE -- extract from the image's world in TREE (a
# tree whose books are certified, e.g. hbox_native's scratch tree) and build
# the CHICKEN program.  Writes TREE/build/extract/: served.json (the front
# end's IR), served.scm, erased.json, inventory.json, fntable.scm, probes.scm,
# served (the binary) and the logs.  Environment: FN_EXTRACT_ACL2 (the ACL2
# launcher: the image builds' tls64k wrapper by default), CHICKEN (its
# prefix), FN_EXTRACT_ROOTS (override the roots).
set -eu
TREE=$(cd "$1" && pwd)
ACL2=${FN_EXTRACT_ACL2:-/tank/fn/toolchains/w28/acl2-literal-4g-tls64k}
CHICKEN=${CHICKEN:-/tank/fn/toolchains/chicken-5.4.0}
OUT=$TREE/build/extract
X=$TREE/tools/extract
mkdir -p "$OUT"
# No product of an earlier build survives to stand in for this one's.
rm -f "$OUT/served.json" "$OUT/served.scm" "$OUT/erased.json" "$OUT/inventory.json" \
      "$OUT/fntable.scm" "$OUT/probes.scm" "$OUT/served" "$OUT/csc-served.args" "$OUT/link.args"
# The boundary: every function the driver calls (host/native/io.lisp calls
# each through fnn-call) -- the reader's served path, its store selection,
# the durable-extent realizers' ACL2 calls (host/native/extent.lisp), the
# exit codes, and the probes' entries (tools/extract/probes.py) -- and the
# EXTRA functions that are not boundary functions (the realizer's buffer
# stobjs' creators and the references the native digests fall back to,
# tools/extract/native.scm).  Both are DECLARED (definterface :root, in
# host/interfaces.lisp and host/interfaces-extract.lisp) and generated into
# roots.sh by tools/interface_emit.py.
. "$X/roots.sh"
ROOTS=${FN_EXTRACT_ROOTS:-$FN_EXTRACT_ROOTS_DECLARED}
EXTRA=${FN_EXTRACT_EXTRA:-$FN_EXTRACT_EXTRA_DECLARED}
python3 "$X/world.py" --check
# The world, loaded once per world digest and saved (world_image.sh).
WORLD=$(sh "$X/world_image.sh" "$TREE")
cat > "$OUT/extract.lsp" <<LSP
(ld "tools/extract/frontend.lisp")
(xt-extract-with (quote ($ROOTS)) (quote ($EXTRA)) "build/extract/served.json" state)
LSP
( cd "$TREE" && swarm-build "$WORLD" < "$OUT/extract.lsp" > "$OUT/extract.log" 2>&1 )
if grep -q "ACL2 Error" "$OUT/extract.log" || [ ! -s "$OUT/served.json" ]; then
    echo "extract: the front end failed; see $OUT/extract.log" >&2; exit 1
fi
cd "$OUT"
python3 "$X/chicken.py" served.json --out served.scm --erased erased.json \
    --inventory inventory.json --table fntable.scm
python3 "$X/probes.py" scheme probes.scm
cp "$X/runtime.scm" "$X/served-main.scm" "$X/native.scm" "$X/hostio.scm" .
# BLAKE3 is the images' own library (tools/build_blake3.sh, the vendored
# reference C behind host/native/fn-blake3.c), linked with its directory as
# the run path; libcrypto is for the Cancel-Lock SHA-256.
sh "$TREE/tools/build_blake3.sh" "$OUT/lib" > blake3.log 2>&1 || {
    echo "extract: tools/build_blake3.sh failed; see $OUT/blake3.log" >&2; exit 1; }
# The image's own libraries (tools/build_native_host.sh builds them into lib/
# beside the image's core, where the image loads them): ML-DSA-65 for the
# signature seam's verifier (A-SIG-NATIVE, native.scm) and the LZ4 block
# encoder the writable verbs' compressed append asks for candidates
# (host/native/lz4.lisp; hostio.scm a-hx-lz4-candidate).  Linked from that
# directory, with it as the run path, so the program calls the very files the
# image calls (the gate checks the resolved paths and digests).
IMGLIB=${FN_EXTRACT_IMAGE_LIB:-$TREE/build/lib}
for lib in libfn-mldsa65.so libfn-lz4.so; do
    [ -f "$IMGLIB/$lib" ] || {
        echo "extract: no $IMGLIB/$lib (build the developer image first: tools/build_native_host.sh)" >&2; exit 1; }
done
LINK="-L$OUT/lib -lfn-blake3 -Wl,-rpath,$OUT/lib -L$IMGLIB -lfn-mldsa65 -lfn-lz4 -Wl,-rpath,$IMGLIB"
printf '%s\n' "$LINK" > link.args
# The compiler options, recorded for the gate's extraction manifest (check.sh).
CSC_OPTS="-O3 -d0 -block -inline-global -lfa2"
printf '%s\n' "csc $CSC_OPTS served-main.scm -o served -L -lcrypto -L $LINK" > csc-served.args
PATH=$CHICKEN/bin:$PATH swarm-build csc $CSC_OPTS \
    served-main.scm -o served -L -lcrypto -L "$LINK" > csc.log 2>&1 || {
    echo "extract: csc failed; see $OUT/csc.log" >&2; tail -20 csc.log >&2; exit 1; }
echo "extract: built $OUT/served"

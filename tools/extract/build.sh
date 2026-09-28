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
      "$OUT/fntable.scm" "$OUT/probes.scm" "$OUT/served" "$OUT/csc-served.args"
# The boundary: every function the driver calls (host/native/io.lisp calls
# each through fnn-call).  The reader's served path, its store selection, the
# durable-extent realizers' ACL2 calls (host/native/extent.lisp), the exit
# codes, and the probes' entries (tools/extract/probes.py).
ROOTS=${FN_EXTRACT_ROOTS:-"create-fn-arena fn-reader-use-seed fn-reader-set-posting fn-reader-model-octets fn-reader-reset fn-reader-chunk fn-reader-outcome fn-reader-observe-clock fn-outcome-code fn-ns-file-render fn-intern-events fn-arx-entry-ok-buffer fn-arx-read-cache-entries fn-xo-open-store fn-reader-use-store fn-lzr-lz-read"}
# Not boundary functions: the realizer's buffer stobj's creator (the image
# holds the live fn-octets-rd; the program creates it once) and the
# references the native digests fall back to (tools/extract/native.scm): the
# three BLAKE3 entries and the Cancel-Lock hash's SHA-256.
EXTRA=${FN_EXTRACT_EXTRA:-"create-fn-octets-rd create-fn-octets-lg fn-blake3-stobj fn-blake3-of-prefixed-buffer fn-blake3-of-prefixed-range fn-sha256"}
python3 "$X/world.py" --check
cat > "$OUT/extract.lsp" <<LSP
(ld "tools/extract/world.lisp")
(ld "tools/extract/world-host.lisp")
(ld "tools/extract/frontend.lisp")
(xt-extract-with (quote ($ROOTS)) (quote ($EXTRA)) "build/extract/served.json" state)
LSP
( cd "$TREE" && swarm-build "$ACL2" < "$OUT/extract.lsp" > "$OUT/extract.log" 2>&1 )
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
# The compiler options, recorded for the gate's extraction manifest (check.sh).
CSC_OPTS="-O3 -d0 -block -inline-global -lfa2"
printf '%s\n' "csc $CSC_OPTS served-main.scm -o served -L -lcrypto -L -L$OUT/lib -lfn-blake3 -Wl,-rpath,$OUT/lib" > csc-served.args
PATH=$CHICKEN/bin:$PATH swarm-build csc $CSC_OPTS \
    served-main.scm -o served -L -lcrypto -L "-L$OUT/lib -lfn-blake3 -Wl,-rpath,$OUT/lib" > csc.log 2>&1 || {
    echo "extract: csc failed; see $OUT/csc.log" >&2; tail -20 csc.log >&2; exit 1; }
echo "extract: built $OUT/served"

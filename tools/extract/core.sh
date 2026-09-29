#!/bin/sh
# tools/extract/core.sh TREE -- build the Common Lisp product: an SBCL core
# with fn's functions (extracted from the image's world by the front end,
# compiled from tools/extract/cl.py's Lisp) and host/native, and nothing of
# ACL2 (ember 2026-09-28; A-TARGET-COMPILER).  Writes TREE/build/core/:
# core.json, packages.json, core-world.lisp (the front end's export),
# defs.lisp, packages.lisp, host-block.lisp, the logs, and fn-core (an
# executable: `fn-core --fn ...' is the image's CLI).  Environment:
# FN_EXTRACT_ACL2 (the ACL2 launcher, as build.sh), FN_EXTRACT_WORLD_IMAGE (a
# saved image of the extraction world; default world_image.sh's cache), SBCL
# (the SBCL the image runs on; default the toolchain's).
set -eu
TREE=$(cd "$1" && pwd)
X=$TREE/tools/extract
OUT=$TREE/build/core
ACL2=${FN_EXTRACT_ACL2:-/tank/fn/toolchains/w28/acl2-literal-4g-tls64k}
SBCL=${SBCL:-/tank/fn/sbcl/bin/sbcl}
SBCL_HOME=${SBCL_HOME:-/tank/fn/sbcl/lib/sbcl/}
export SBCL_HOME
mkdir -p "$OUT"
rm -f "$OUT/core.json" "$OUT/core-world.lisp" "$OUT/packages.json" "$OUT/defs.lisp" \
      "$OUT/packages.lisp" "$OUT/host-block.lisp" "$OUT/fn-core" "$OUT/defs.fasl" "$OUT/clruntime.fasl"
python3 "$X/host_tokens.py" "$TREE" "$OUT/tokens.lsp"
# the world, loaded once per world digest and saved (world_image.sh)
FN_EXTRACT_WORLD_IMAGE=${FN_EXTRACT_WORLD_IMAGE:-$(sh "$X/world_image.sh" "$TREE")}
{
  printf '(ld "tools/extract/frontend.lisp")\n(ld "tools/extract/core-export.lisp")\n(xt-core-export (quote\n'
  cat "$OUT/tokens.lsp"
  printf ') "build/core/core.json" "build/core/core-world.lisp" "build/core/packages.json" state)\n'
} > "$OUT/export.lsp"
( cd "$TREE" && swarm-build "$FN_EXTRACT_WORLD_IMAGE" < "$OUT/export.lsp" > "$OUT/export.log" 2>&1 )
if grep -q "ACL2 Error" "$OUT/export.log" || [ ! -s "$OUT/core.json" ] || [ ! -s "$OUT/core-world.lisp" ]; then
    echo "core: the front end's export failed; see $OUT/export.log" >&2; exit 1
fi
python3 "$X/cl.py" "$OUT/core.json" --out "$OUT/defs.lisp" --inventory "$OUT/inventory.json" \
    --packages "$OUT/packages.json" --packages-out "$OUT/packages.lisp"
python3 "$X/core_build.py" "$TREE" "$OUT/host-block.lisp"
# The image's libraries, as tools/build_native_host.sh names them for its build.
LIB=$TREE/build/lib
export FN_MLDSA_LIBRARY=$LIB/libfn-mldsa65.so FN_LZ4_LIBRARY=$LIB/libfn-lz4.so FN_BLAKE3_LIBRARY=$LIB/libfn-blake3.so
export FN_NATIVE_PROFILE=${FN_NATIVE_PROFILE:-developer}
# The image's runtime options (its launcher's: heap, control stack, thread-
# local storage, from the profile: tools/build_native_host.sh), saved into the
# core (:save-runtime-options), so the product runs as the image does.
IMAGE=${FN_EXTRACT_IMAGE:-$TREE/build/fn-host-developer}
opt() { sed -n "s/.*$1 \([^ ]*\) .*/\1/p" "$IMAGE" | head -1; }
HEAP=$(opt --dynamic-space-size); STACK=$(opt --control-stack-size); TLS=$(opt --tls-limit)
[ -n "$HEAP" ] && [ -n "$STACK" ] || { echo "core: cannot read the runtime options of $IMAGE" >&2; exit 1; }
( cd "$TREE" && XL_OUT="$OUT/" XL_X="$X/" swarm-build "$SBCL" ${TLS:+--tls-limit $TLS} --dynamic-space-size "$HEAP" --control-stack-size "$STACK" \
      --non-interactive --no-userinit --load "$X/core-main.lisp" > "$OUT/sbcl.log" 2>&1 ) || {
    echo "core: the SBCL build failed; see $OUT/sbcl.log" >&2; tail -30 "$OUT/sbcl.log" >&2; exit 1; }
[ -x "$OUT/fn-core" ] || { echo "core: no $OUT/fn-core" >&2; exit 1; }
# The image loads its libraries from lib/ beside its core: the same files here.
ln -sfn ../lib "$OUT/lib"
[ -f "$TREE/build/source-revision" ] && cp "$TREE/build/source-revision" "$OUT/source-revision"
echo "core: built $OUT/fn-core"

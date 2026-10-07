#!/bin/sh
# tools/extract/core.sh TREE -- build the Common Lisp product: an SBCL core
# with fn's functions and host/native, and nothing of ACL2 (ember 2026-09-28;
# A-TARGET-COMPILER).  The functions are the forms ACL2 itself installed,
# re-derived from the extraction world and ACL2's sources and macroexpanded by
# the image's SBCL (forms-export.lisp; X1/X2): not translated, not CHICKEN.  Writes TREE/build/core/:
# FN_CORE_OUT overrides the output directory (default build/core);
# FN_CORE_NAME selects the launcher/core basename (default fn-core). DTN
# names select build-dtn.lisp, its host roots and its extraction world/cache.
# Named products fix production/developer profile; fn-core defaults developer.
# core.json, packages.json, core-world.lisp (the front end's export),
# defs.lisp, manifest.tsv, runtime.tsv, packages.lisp, host-block.lisp, the logs, and fn-core (an
# executable: `fn-core --fn ...' is the image's CLI).  Environment:
# FN_EXTRACT_ACL2 (the ACL2 launcher, as build.sh), FN_EXTRACT_WORLD_IMAGE (a
# saved image of the extraction world; default world_image.sh's cache), SBCL
# (the SBCL the image runs on; default the toolchain's).
set -eu
TREE=$(cd "$1" && pwd)
X=$TREE/tools/extract
OUT=${FN_CORE_OUT:-$TREE/build/core}
ACL2=${FN_EXTRACT_ACL2:-/tank/fn/toolchains/w28/acl2-literal-4g-tls64k}
NAME=${FN_CORE_NAME:-fn-core}
case $NAME in fn-core|fn-host|fn-host-developer|fn-host-dtn|fn-host-dtn-developer) ;; *)
    echo "core: unsupported product name: $NAME" >&2; exit 2 ;; esac
case $NAME in
    fn-core) VARIANT=${FN_EXTRACT_VARIANT:-default} ;;
    fn-host-dtn*) VARIANT=dtn ;;
    *) VARIANT=default ;;
esac
case $VARIANT in
    dtn) BUILD=host/native/build-dtn.lisp; DEFAULT_IMAGE=fn-host-dtn ;;
    default) BUILD=host/native/build.lisp; DEFAULT_IMAGE=fn-host ;;
    *) echo "core: unsupported variant: $VARIANT" >&2; exit 2 ;;
esac
if [ -n "${FN_EXTRACT_VARIANT:-}" ] && [ "$FN_EXTRACT_VARIANT" != "$VARIANT" ]; then
    echo "core: product name $NAME requires $VARIANT variant" >&2; exit 2
fi
case $NAME in
    fn-core) PROFILE=${FN_NATIVE_PROFILE:-developer} ;;
    *-developer) PROFILE=developer ;;
    *) PROFILE=production ;;
esac
case $PROFILE in production|developer) ;; *) echo "core: unsupported profile: $PROFILE" >&2; exit 2 ;; esac
if [ -n "${FN_NATIVE_PROFILE:-}" ] && [ "$FN_NATIVE_PROFILE" != "$PROFILE" ]; then
    echo "core: product name $NAME requires $PROFILE profile" >&2; exit 2
fi
export FN_EXTRACT_VARIANT=$VARIANT FN_NATIVE_PROFILE=$PROFILE
[ "$PROFILE" != developer ] || DEFAULT_IMAGE=$DEFAULT_IMAGE-developer
IMAGE=${FN_EXTRACT_IMAGE:-$TREE/build/$DEFAULT_IMAGE}
SBCL=${SBCL:-$(sed -n 's/^exec "\([^"]*\)" .*/\1/p' "$IMAGE")}
SBCL_HOME=${SBCL_HOME:-$(sed -n "s/^export SBCL_HOME='\([^']*\)'/\1/p" "$IMAGE")}
[ -x "$SBCL" ] && [ -d "$SBCL_HOME" ] || {
    echo "core: cannot resolve the reference image's SBCL runtime/home" >&2; exit 1; }
export SBCL_HOME
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
rm -f "$OUT/core.json" "$OUT/core-world.lisp" "$OUT/packages.json" "$OUT/defs.lisp" \
      "$OUT/packages.lisp" "$OUT/host-block.lisp" "$OUT/manifest.tsv" "$OUT/runtime.tsv" "$OUT/gaps.txt" \
      "$OUT/defs.lisp.verified-sha256" "$OUT/export.log" "$OUT/verify.log" "$OUT/fn-core" "$OUT/fn-core.core" \
      "$OUT/$NAME" "$OUT/$NAME.core" "$OUT/source-revision" "$OUT/defs.fasl" "$OUT/clruntime.fasl"
python3 "$X/host_tokens.py" "$TREE" "$OUT/tokens.lsp" "$BUILD"
# the world, loaded once per world digest and saved (world_image.sh)
FN_EXTRACT_WORLD_IMAGE=${FN_EXTRACT_WORLD_IMAGE:-$(sh "$X/world_image.sh" "$TREE")}
TOOLCHAIN=$(python3 "$TREE/tools/acl2_toolchain.py" identity "$ACL2")
WORLD_KEY=$(python3 "$X/world.py" --digest "$TREE" --acl2 "$ACL2" --variant "$VARIANT" --toolchain-identity "$TOOLCHAIN")
python3 "$X/world_binding.py" check "$FN_EXTRACT_WORLD_IMAGE" "$WORLD_KEY" "$VARIANT"
# ACL2's source files (the forms ACL2 compiled where its world holds none), next to the toolchain's saved core
ACL2_SRC=${FN_EXTRACT_ACL2_SRC:-$(sed -n 's/.*--core "\(.*\)\/saved_acl2\.core".*/\1/p' "$ACL2")}
[ -d "$ACL2_SRC" ] && [ -f "$ACL2_SRC/axioms.lisp" ] || { echo "core: cannot find ACL2's sources (FN_EXTRACT_ACL2_SRC)" >&2; exit 1; }
EXPORT_DEADLINE=${FN_EXPORT_DEADLINE:-900}
{
  printf '(ld "tools/extract/frontend.lisp")\n(ld "tools/extract/core-export.lisp")\n(xt-core-export (quote\n'
  cat "$OUT/tokens.lsp"
  printf ') "%s/core.json" "%s/core-world.lisp" "%s/packages.json" state)\n' "$OUT" "$OUT" "$OUT"
  # the definitions: ACL2's own raw and *1* forms, macroexpanded (forms-export.lisp), under a deadline
  printf ':q\n(load "tools/extract/forms-export.lisp")\n(in-package "ACL2")\n(xt-fe-export (with-open-file (s "%s/tokens.lsp") (let ((*package* (find-package "ACL2"))) (read s))) "%s" "%s" "tools/extract/clruntime.lisp" "%s" :deadline %s)\n(sb-ext:exit)\n' \
      "$OUT" "$OUT" "$ACL2_SRC" "$WORLD_KEY" "$EXPORT_DEADLINE"
} > "$OUT/export.lsp"
# The export is measured at about 30 s on hbox once the image is cached (xt-fe-export: index 5 s, closure 20 s);
# EXPORT_DEADLINE is the in-image deadline (fails closed naming the phase and the last unit), the outer
# timeout is twice that plus the front end's own pass.
( cd "$TREE" && timeout $((2 * EXPORT_DEADLINE + 600)) swarm-build "$FN_EXTRACT_WORLD_IMAGE" < "$OUT/export.lsp" > "$OUT/export.log" 2>&1 ) || true
if grep -q "XT-FE TIMEOUT" "$OUT/export.log"; then
    echo "core: the export timed out: $(grep 'XT-FE TIMEOUT' "$OUT/export.log" | head -1); see $OUT/export.log" >&2; exit 1
fi
if grep -qE "ACL2 Error|HARD ACL2 ERROR|debugger invoked" "$OUT/export.log" || [ ! -s "$OUT/core.json" ] || [ ! -s "$OUT/core-world.lisp" ] \
   || [ ! -s "$OUT/defs.lisp" ] || [ ! -s "$OUT/manifest.tsv" ] || [ ! -s "$OUT/packages.lisp" ]; then
    echo "core: the export failed; see $OUT/export.log" >&2; exit 1
fi
# X2: a name no extracted unit, runtime entry or Common Lisp provides is refused here, by name
if [ -s "$OUT/gaps.txt" ]; then
    echo "core: the closure has names nothing provides (see $OUT/gaps.txt):" >&2; head -20 "$OUT/gaps.txt" >&2; exit 1
fi
# X1: a separate image run re-derives every unit from the world and ACL2's sources and compares
{
  printf '(ld "tools/extract/frontend.lisp")\n:q\n(load "tools/extract/forms-export.lisp")\n(in-package "ACL2")\n'
  printf '(xt-verify-defs "%s" "%s" "tools/extract/clruntime.lisp" "%s")\n(sb-ext:exit)\n' "$OUT" "$ACL2_SRC" "$WORLD_KEY"
} > "$OUT/verify.lsp"
( cd "$TREE" && timeout $((2 * EXPORT_DEADLINE)) swarm-build "$FN_EXTRACT_WORLD_IMAGE" < "$OUT/verify.lsp" > "$OUT/verify.log" 2>&1 ) || true
grep -q "XT-VERIFY-DEFS OK" "$OUT/verify.log" || {
    echo "core: xt-verify-defs refused the definitions:" >&2; grep -a "^  unit\|XT-VERIFY-DEFS\|VERIFY" "$OUT/verify.log" | head -20 >&2; exit 1; }
DEFS_SHA=$(python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$OUT/defs.lisp")
echo "$DEFS_SHA" > "$OUT/defs.lisp.verified-sha256"
python3 "$X/core_build.py" "$TREE" "$OUT/host-block.lisp" "$BUILD"
# The image's libraries, as tools/build_native_host.sh names them for its build.
LIB=$TREE/build/lib
export FN_DEFLATE_LIBRARY=$LIB/libfn-deflate.so
export FN_MLDSA_LIBRARY=$LIB/libfn-mldsa65.so FN_BLAKE3_LIBRARY=$LIB/libfn-blake3.so
# The image's runtime options (its launcher's: heap, control stack, thread-
# local storage, from the profile: tools/build_native_host.sh), recorded in
# the generated launcher, so the product runs as the image does.
opt() { sed -n "s/.*$1 \([^ ]*\) .*/\1/p" "$IMAGE" | head -1; }
HEAP=$(opt --dynamic-space-size); STACK=$(opt --control-stack-size); TLS=$(opt --tls-limit)
[ -n "$HEAP" ] && [ -n "$STACK" ] || { echo "core: cannot read the runtime options of $IMAGE" >&2; exit 1; }
# the file the SBCL build compiles is the file xt-verify-defs verified
[ "$(python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$OUT/defs.lisp")" = "$(cat "$OUT/defs.lisp.verified-sha256")" ] || {
    echo "core: defs.lisp changed after xt-verify-defs verified it" >&2; exit 1; }
( cd "$TREE" && XL_OUT="$OUT/" XL_X="$X/" swarm-build "$SBCL" ${TLS:+--tls-limit $TLS} --dynamic-space-size "$HEAP" --control-stack-size "$STACK" \
      --non-interactive --no-userinit --load "$X/core-main.lisp" > "$OUT/sbcl.log" 2>&1 ) || {
    echo "core: the SBCL build failed; see $OUT/sbcl.log" >&2; tail -30 "$OUT/sbcl.log" >&2; exit 1; }
[ -s "$OUT/fn-core.core" ] || { echo "core: no $OUT/fn-core.core" >&2; exit 1; }
# X2: judged at the end of the build, after host/native has defined the constrained functions it provides
if grep -aq "Undefined functions:\|Undefined variables:" "$OUT/sbcl.log"; then
    echo "core: SBCL reports undefined names after the whole build (X2); see $OUT/sbcl.log:" >&2
    awk '/Undefined (functions|variables):/{f=1} f' "$OUT/sbcl.log" | head -12 >&2; exit 1
fi
[ "$NAME" = fn-core ] || mv "$OUT/fn-core.core" "$OUT/$NAME.core"
python3 "$X/core_launcher.py" "$OUT/$NAME" --runtime "$SBCL" --home "$SBCL_HOME" \
    --core "$OUT/$NAME.core" --heap "$HEAP" --stack "$STACK" ${TLS:+--tls "$TLS"}
# The image loads its libraries from lib/ beside its core: the same files here.
ln -sfn "$LIB" "$OUT/lib"
[ -f "$TREE/build/source-revision" ] && cp "$TREE/build/source-revision" "$OUT/source-revision"
echo "core: built $OUT/$NAME"

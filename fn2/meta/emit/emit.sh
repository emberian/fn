#!/bin/sh
# Print fn2's world with ACL2 (registry and embedding), then emit the Lean presentation from it:
#   Fn2/Instances/LayerA.lean       the declaration registry (emit_lean.py)
#   Fn2/Instances/LayerAWorld.lean  the closed subset's functions, translated (emit_embed.py)
#   Fn2/Instances/LayerAKinds.lean  the kinds in the step language, translated (emit_embed.py)
# Run from anywhere; needs fn2/books/reference certified (fn2/tools/certify.sh books/reference.lisp).
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../../.." && pwd)
: "${ACL2:=$root/tools/acl2}"
: "${ACL2_SYSTEM_BOOKS:=$HOME/tools/acl2-fn/acl2-8.7/books}"
export ACL2_SYSTEM_BOOKS
cd "$root"
log=$(mktemp "${TMPDIR:-/tmp}/fn2-meta-print-XXXXXX")
"$ACL2" --timeout 900 < fn2/meta/emit/print-registry.lsp > "$log" 2>&1 || :
if ! grep -F 'FN2-META-PRINT-WORLD PASS' "$log" >/dev/null; then
  grep -F 'META ERROR' "$log" | head -40; tail -20 "$log"; echo "print-registry FAILED (log $log)"; exit 1
fi
src=$(git -C "$root" rev-parse --short HEAD)
python3 -I "$here/emit_lean.py" "$here/world.sexp" "$root/fn2/meta/Fn2/Instances/LayerA.lean" "dev $src"
python3 -I "$here/emit_embed.py" "$here/world.sexp" "$root/fn2/meta/Fn2/Instances/LayerAWorld.lean" \
  "$root/fn2/meta/Fn2/Instances/LayerAKinds.lean" Fn2.Instances.LayerA

#!/bin/sh
# Print fn2's world with ACL2 (registry and embedding), then emit the Lean presentation from it:
#   Fn2/Instances/LayerA.lean       the declaration registry (emit_lean.py)
#   Fn2/Instances/LayerAWorld.lean  the closed subset's functions, translated (emit_embed.py)
#   Fn2/Instances/LayerAKinds.lean  the kinds in the step language, translated (emit_embed.py)
#   Fn2/Instances/LayerAEqns{1..4}.lean  the dispatch equations, by rfl (emit_embed.py)
#   Fn2/Instances/LayerAPres.lean   the projection facts the core contracts read (emit_pres.py)
#   Fn2/Instances/LayerAPhase.lean  the served kinds' operations that keep PHASE (emit_pres.py)
# The registry is printed from reference (print-registry.lsp, world.sexp); the embedding from
# reference plus the measure's probe book (print-probe.lsp, world-probe.sexp), so the probe kinds
# are translated and measured beside the served ones.
# Run from anywhere; needs books/reference and meta/emit/meta-probe certified
# (tools/certify.sh books/reference.lisp meta/emit/meta-probe.lisp).
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../.." && pwd)
: "${ACL2:=$root/tools/acl2}"
: "${ACL2_SYSTEM_BOOKS:=$HOME/tools/acl2-fn/acl2-8.7/books}"
export ACL2_SYSTEM_BOOKS
cd "$root"
log=$(mktemp "${TMPDIR:-/tmp}/fn2-meta-print-XXXXXX")
"$ACL2" --timeout 900 < meta/emit/print-registry.lsp > "$log" 2>&1 || :
if ! grep -F 'FN2-META-PRINT-WORLD PASS' "$log" >/dev/null; then
  grep -F 'META ERROR' "$log" | head -40; tail -20 "$log"; echo "print-registry FAILED (log $log)"; exit 1
fi
"$ACL2" --timeout 900 < meta/emit/print-probe.lsp > "$log.probe" 2>&1 || :
if ! grep -F 'FN2-META-PRINT-WORLD PASS' "$log.probe" >/dev/null; then
  grep -F 'META ERROR' "$log.probe" | head -40; tail -20 "$log.probe"; echo "print-probe FAILED (log $log.probe)"; exit 1
fi
# FN2_EMIT_SRC names the source when the tree is a copy without .git (a box tree, tools/box_certify_bb2.sh).
src=${FN2_EMIT_SRC:-$(git -C "$root" rev-parse --short HEAD)}
python3 -I "$here/emit_lean.py" "$here/world.sexp" "$root/meta/Fn2/Instances/LayerA.lean" "dev $src"
python3 -I "$here/emit_embed.py" "$here/world-probe.sexp" "$root/meta/Fn2/Instances/LayerAWorld.lean" \
  "$root/meta/Fn2/Instances/LayerAKinds.lean" Fn2.Instances.LayerA \
  "$root/meta/Fn2/Instances/LayerAEqns1.lean" "$root/meta/Fn2/Instances/LayerAEqns2.lean" \
  "$root/meta/Fn2/Instances/LayerAEqns3.lean" "$root/meta/Fn2/Instances/LayerAEqns4.lean"
python3 -I "$here/emit_pres.py" "$here/world-probe.sexp" "$root/meta/Fn2/Instances/LayerAPres.lean" \
  Fn2.Instances.LayerAWorld "$root/meta/Fn2/Instances/LayerAPhase.lean" | tail -1

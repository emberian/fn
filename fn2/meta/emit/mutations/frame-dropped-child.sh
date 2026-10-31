#!/bin/sh
# Mutation control for the measure's frame check (LEAN-METATHEORY section 6): the narrowed
# signature of scribe's :RESET arm still takes FN2-POOL but no longer returns it, as a narrowing
# that misses a child an operation writes would print it (24fce1ecd: a function returns what its
# paths write). The declaration still calls FN2-CORE-RESET, which writes the pool, so the
# interpreter writes a child outside the returns and the frame check must name it; the result
# check also differs (one child fewer). Lean-only: mutates the emitted LayerAKinds.lean and restores it.
#
# Usage, from fn2/meta: emit/mutations/frame-dropped-child.sh RECORD.sexp
set -u
record=${1:?the recorder output (build/lean-meta/arms-record.sexp)}
kinds=Fn2/Instances/LayerAKinds.lean
out=${OUT:-../../build/lean-meta/mutation-frame}
mkdir -p "$out"
cp "$kinds" "$out/LayerAKinds.lean.orig"
python3 -I - "$kinds" <<'PY'
import sys
p = sys.argv[1]
s = open(p).read()
a = '{ tag := ":RESET", sig := some ⟨["FN2-SCRIBE", "FN2-MACHINES", "FN2-POOL", "FN2-CONTROL"], ["FN2-SCRIBE", "FN2-MACHINES", "FN2-POOL", "FN2-CONTROL"], 4⟩'
b = '{ tag := ":RESET", sig := some ⟨["FN2-SCRIBE", "FN2-MACHINES", "FN2-POOL", "FN2-CONTROL"], ["FN2-SCRIBE", "FN2-MACHINES", "FN2-CONTROL"], 4⟩'
assert s.count(a) == 1, "the :RESET signature moved; update the mutation"
open(p, "w").write(s.replace(a, b))
PY
lake build fn2-measure > "$out/build.log" 2>&1; echo "build exit $?"
(ulimit -s 65520; lake exe fn2-measure "$record") > "$out/measure.txt" 2>&1; echo "measure exit $?"
cp "$out/LayerAKinds.lean.orig" "$kinds"
lake build fn2-measure > "$out/build-restored.log" 2>&1; echo "restored build exit $?"
grep -A3 "RESET-CHILDREN\|TOTAL" "$out/measure.txt"

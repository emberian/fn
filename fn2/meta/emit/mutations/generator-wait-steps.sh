#!/bin/sh
# Mutation control for the measure (LEAN-METATHEORY section 8): a generator-only change that no
# declaration shows. The generator's (:wait :completion ...) charges *fn2-work-small* instead of
# *fn2-work-mailbox* when the step names no :steps. The declarations are unchanged, so the
# interpreter (which reads the declarations) still agrees with the recorded ACL2 run, and the
# translated generated functions of every arm with a bare :wait must not.
#
# Usage, from a worktree whose books certify (it mutates that worktree's machine-arms.lisp and
# restores it): fn2/meta/emit/mutations/generator-wait-steps.sh RECORD.sexp
# Writes build/lean-meta/mutation-wait/: the mutant world, the measure's report, the logs.
set -u
root=$(git rev-parse --show-toplevel)
cd "$root"
record=${1:?the recorder output (build/lean-meta/arms-record.sexp)}
# the Lean project and emitters to use (default: this worktree's)
meta=${META:-$root/fn2/meta}
out=build/lean-meta/mutation-wait
mkdir -p "$out"
export ACL2_SYSTEM_BOOKS=${ACL2_SYSTEM_BOOKS:-$HOME/tools/acl2-fn/acl2-8.7/books}
book=fn2/books/machine-arms.lisp
sed -i '' "s/(fn2-arms-kw :steps (cdr args) '\*fn2-work-mailbox\*)/(fn2-arms-kw :steps (cdr args) '*fn2-work-small*)/" "$book"
git diff --stat "$book"
fn2/tools/certify.sh books/machines-a-run.lisp > "$out/certify-mutant.log" 2>&1; echo "certify-mutant exit $?"
cat > "$out/print.lsp" <<'LSP'
(in-package "ACL2")
(include-book "fn2/books/machines-a-run")
:q
(load "META/emit/print-world.lisp")
(in-package "ACL2")
(setq *meta-assembled* nil)
(meta-print-world "build/lean-meta/mutation-wait/world-mutant.sexp")
LSP
sed -i '' "s#META/#$meta/#" "$out/print.lsp"
tools/acl2 --timeout 600 < "$out/print.lsp" > "$out/print.log" 2>&1
grep -c 'FN2-META-PRINT-WORLD PASS' "$out/print.log"
git checkout -- "$book"
fn2/tools/certify.sh books/machines-a-run.lisp > "$out/certify-restored.log" 2>&1; echo "certify-restored exit $?"
# The mutant's Lean side in a scratch copy of fn2/meta (Mathlib shared through .lake/packages).
rm -rf "$out/meta"
mkdir -p "$out/meta/.lake"
cp -R "$meta/Fn2" "$meta/Fn2.lean" "$meta/lakefile.toml" "$meta/lake-manifest.json" "$meta/lean-toolchain" "$out/meta/"
ln -s "$(cd "$meta/.lake/packages" && pwd -P)" "$out/meta/.lake/packages"
python3 -I "$meta/emit/emit_embed.py" "$out/world-mutant.sexp" "$out/meta/Fn2/Instances/LayerAWorld.lean" \
  "$out/meta/Fn2/Instances/LayerAKinds.lean" Fn2.Instances.LayerA
(cd "$out/meta" && lake build fn2-measure > ../build.log 2>&1; echo "lean build exit $?")
ulimit -s 65520
"$out/meta/.lake/build/bin/fn2-measure" "$record" > "$out/measure.txt" 2>&1; echo "measure exit $?"
grep "MEASURE TOTAL\|generated differs" "$out/measure.txt" | head -20
echo MUTATION-DONE

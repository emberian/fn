#!/bin/sh
# Mutation control for the independent expression reader (LEAN-METATHEORY sections 6 and 12,
# decision 7): a defect in the generator's expression rewrite, present when the simulator runs.
# fn2-arms-index-constant reads *K-ADMISSION-ORDINAL* as the KIND formal instead of ORDINAL, so
# echo's draining arm frees and reclaims in partition 1 (its kind) instead of 0 (its ordinal).
# The record is made with the mutant: ACL2 executes the mutant generated code, so the generated
# column agrees with it. An interpreter that reads expressions through the same rewrite (the
# printer before decision 7) agrees too and the defect is invisible: this script shows that by
# printing the mutant world's draining expression through the rewrite. The independent reader
# (Fn2.Arms.readExpr) reads the declaration and must differ on the draining calls that free.
#
# Usage, from a worktree whose reference and simulator books certify (it mutates that worktree's
# machine-arms.lisp, certifies, records, prints, restores and re-certifies):
#   fn2/meta/emit/mutations/rewrite-index-constant.sh
# Writes build/lean-meta/mutation-rewrite/.
set -u
root=$(git rev-parse --show-toplevel)
cd "$root"
meta=${META:-$root/fn2/meta}
out=build/lean-meta/mutation-rewrite
mkdir -p "$out"
export ACL2_SYSTEM_BOOKS=${ACL2_SYSTEM_BOOKS:-$HOME/tools/acl2-fn/acl2-8.7/books}
book=fn2/books/machine-arms.lisp
sed -i '' "s/(fn2-columns-sym kind \"-ADMISSION-ORDINAL\*\"))) 'ordinal)/(fn2-columns-sym kind \"-ADMISSION-ORDINAL*\"))) 'kind)/" "$book"
git diff --stat "$book"
fn2/tools/certify.sh books/reference.lisp sim/sim-recovery.lisp sim/check.lisp > "$out/certify-mutant.log" 2>&1; echo "certify-mutant exit $?"
# the record, with the mutant generator
sed "s#build/lean-meta/arms-record.sexp#$out/arms-record-mutant.sexp#" fn2/meta/emit/record-arms.lsp > "$out/record.lsp"
tools/acl2 --timeout 3600 < "$out/record.lsp" > "$out/record.log" 2>&1
grep -c 'FN2-META-RECORD PASS' "$out/record.log"
# the mutant world, printed for the independent reader
cat > "$out/print.lsp" <<LSP
(in-package "ACL2")
(include-book "fn2/books/reference")
:q
(load "$meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-world "$out/world-mutant.sexp")
LSP
tools/acl2 --timeout 900 < "$out/print.lsp" > "$out/print.log" 2>&1
grep -c 'FN2-META-PRINT-WORLD PASS' "$out/print.log"
# what the shared rewrite makes of the draining arm's ordinal (the printer before decision 7)
cat > "$out/shared.lsp" <<LSP
(in-package "ACL2")
(include-book "fn2/books/reference")
:q
(in-package "ACL2")
(let* ((w (w *the-live-state*))
       (env (fn2-arms-env 'fn2-echo :draining nil nil nil t w)))
  (format t "~&META SHARED ~s~%"
          (multiple-value-list (fn2-arms-expr '(fn2-machine-free-head *fn2-echo-admission-ordinal*) env nil 1000))))
LSP
tools/acl2 --timeout 900 < "$out/shared.lsp" > "$out/shared.log" 2>&1
grep 'META SHARED' "$out/shared.log"
git checkout -- "$book"
fn2/tools/certify.sh books/reference.lisp sim/sim-recovery.lisp sim/check.lisp > "$out/certify-restored.log" 2>&1; echo "certify-restored exit $?"
# the mutant's Lean side in a scratch copy of fn2/meta (Mathlib shared through .lake/packages)
rm -rf "$out/meta"
mkdir -p "$out/meta/.lake"
cp -R "$meta/Fn2" "$meta/Fn2.lean" "$meta/lakefile.toml" "$meta/lake-manifest.json" "$meta/lean-toolchain" "$out/meta/"
ln -s "$(cd "$meta/.lake/packages" && pwd -P)" "$out/meta/.lake/packages"
python3 -I "$meta/emit/emit_embed.py" "$out/world-mutant.sexp" "$out/meta/Fn2/Instances/LayerAWorld.lean" \
  "$out/meta/Fn2/Instances/LayerAKinds.lean" Fn2.Instances.LayerA
(cd "$out/meta" && lake build fn2-measure > ../build.log 2>&1; echo "lean build exit $?")
ulimit -s 65520
"$out/meta/.lake/build/bin/fn2-measure" "$out/arms-record-mutant.sexp" > "$out/measure.txt" 2>&1; echo "measure exit $?"
grep "MEASURE TOTAL\|differs" "$out/measure.txt" | head -20
echo MUTATION-DONE

#!/bin/sh
# Historical: ran at 137695dfc against the table-only exporter (registry.sexp, print-registry.lsp of
# that revision); its result is the .diff beside it. LEAN-METATHEORY section 8 cites it.
# Mutation control 1b (Astra's control 1): the common deadline field narrows from u60 to u32.
set -u
cd /Users/ember/dev/fn/build/lanes/fn2/lean-meta
S=build/lean-meta-scratch
export ACL2_SYSTEM_BOOKS=$HOME/tools/acl2-fn/acl2-8.7/books
python3 - <<'PY'
p='fn2/books/machines.lisp'; s=open(p).read()
old="(ready-next :u32) (wait-reason :u8) (deadline :u60)))"
assert s.count(old)==1
open(p,'w').write(s.replace(old,"(ready-next :u32) (wait-reason :u8) (deadline :u32)))"))
PY
git diff --stat fn2/books/machines.lisp
fn2/tools/certify.sh books/reference.lisp > $S/mut1b-certify.log 2>&1; echo "certify-mutant1b exit $?"
tools/acl2 --timeout 300 < fn2/meta/emit/print-registry.lsp > $S/mut1b-print.log 2>&1
grep -c 'FN2-META-PRINT-REGISTRY PASS' $S/mut1b-print.log
cp fn2/meta/emit/registry.sexp $S/registry-mutant1b.sexp
python3 -I fn2/meta/emit/emit_lean.py $S/registry-mutant1b.sexp $S/LayerA-mutant1b.lean "origin/fn2/main 137695dfc"
git checkout -- fn2/books/machines.lisp
cp $S/registry-base.sexp fn2/meta/emit/registry.sexp
fn2/tools/certify.sh books/reference.lisp > $S/restore1b-certify.log 2>&1; echo "certify-restored1b exit $?"
cmp $S/registry-base.sexp $S/registry-mutant1b.sexp && echo "REGISTRY UNCHANGED under deadline mutation"
diff -u fn2/meta/Fn2/Instances/LayerA.lean $S/LayerA-mutant1b.lean > $S/mutation1b.diff; echo "diff1b lines $(wc -l < $S/mutation1b.diff)"
echo MUTATION1B-DONE

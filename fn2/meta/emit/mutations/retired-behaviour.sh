#!/bin/sh
# Historical: ran at 137695dfc against the table-only exporter (registry.sexp, print-registry.lsp of
# that revision); its result is the .diff beside it. LEAN-METATHEORY section 8 cites it.
# Mutation control 2 (Astra's): change generated behaviour, not the row.
# NAME-OBSERVES-P stops excluding the :retired phase; the registry row is untouched.
set -u
cd /Users/ember/dev/fn/build/lanes/fn2/lean-meta
S=build/lean-meta-scratch
export ACL2_SYSTEM_BOOKS=$HOME/tools/acl2-fn/acl2-8.7/books
python3 - <<'PY'
p='fn2/books/machines.lisp'; s=open(p).read()
old=",(if (member-eq :retired states) `(not (equal phase ,(position-eq :retired states))) t)"
assert s.count(old)==1
open(p,'w').write(s.replace(old,"t"))
PY
git diff --stat fn2/books/machines.lisp
fn2/tools/certify.sh books/reference.lisp > $S/mut2-certify.log 2>&1; echo "certify-mutant2 exit $?"
tools/acl2 --timeout 300 < fn2/meta/emit/print-registry.lsp > $S/mut2-print.log 2>&1
grep -c 'FN2-META-PRINT-REGISTRY PASS' $S/mut2-print.log
cp fn2/meta/emit/registry.sexp $S/registry-mutant2.sexp
python3 -I fn2/meta/emit/emit_lean.py $S/registry-mutant2.sexp $S/LayerA-mutant2.lean "origin/fn2/main 137695dfc"
git checkout -- fn2/books/machines.lisp
cp $S/registry-base.sexp fn2/meta/emit/registry.sexp
fn2/tools/certify.sh books/reference.lisp > $S/restore2-certify.log 2>&1; echo "certify-restored2 exit $?"
cmp $S/registry-base.sexp $S/registry-mutant2.sexp && echo "REGISTRY UNCHANGED under behaviour mutation"
diff -u fn2/meta/Fn2/Instances/LayerA.lean $S/LayerA-mutant2.lean > $S/mutation2.diff; echo "diff2 lines $(wc -l < $S/mutation2.diff)"
echo MUTATION2-DONE

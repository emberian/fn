#!/bin/sh
# Historical: ran at 137695dfc against the table-only exporter (registry.sexp, print-registry.lsp of
# that revision); its result is the .diff beside it. LEAN-METATHEORY section 8 cites it.
# Mutation control: defmachine's registry row drops each kind's first observed event.
set -u
cd /Users/ember/dev/fn/build/lanes/fn2/lean-meta
S=build/lean-meta-scratch
export ACL2_SYSTEM_BOOKS=$HOME/tools/acl2-fn/acl2-8.7/books
sed -i '' 's/:continuations ,continuations :observes ,observes/:continuations ,continuations :observes ,(cdr observes)/' books/machines.lisp
git diff --stat books/machines.lisp
tools/certify.sh books/reference.lisp > $S/mut-certify.log 2>&1; echo "certify-mutant exit $?"
tools/acl2 --timeout 300 < meta/emit/print-registry.lsp > $S/mut-print.log 2>&1
grep -c 'FN2-META-PRINT-REGISTRY PASS' $S/mut-print.log
cp meta/emit/registry.sexp $S/registry-mutant.sexp
python3 -I meta/emit/emit_lean.py $S/registry-mutant.sexp $S/LayerA-mutant.lean "MUTANT: defmachine row :observes (cdr observes)"
git checkout -- books/machines.lisp
cp $S/registry-base.sexp meta/emit/registry.sexp
tools/certify.sh books/reference.lisp > $S/restore-certify.log 2>&1; echo "certify-restored exit $?"
diff -u meta/Fn2/Instances/LayerA.lean $S/LayerA-mutant.lean > $S/mutation.diff; echo "diff lines $(wc -l < $S/mutation.diff)"
echo MUTATION-DONE

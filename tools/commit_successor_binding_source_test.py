"""Exact actual C/B claim and publication gate source controls; ACL2 unrun."""
from pathlib import Path
import unittest
import json
import commit_claimed_scan_transform as scan_transform
import lisp_rewrite as lr


def functions(text):
    out = {}
    def walk(n):
        if isinstance(n, lr.Lst):
            if len(n.items)>1 and isinstance(n.items[1], lr.Atom) and getattr(n.items[0], 'text', '') in ['defun', 'defthm']:
                out[n.items[1].text] = text[n.start:n.end]
            for child in n.items: walk(child)
        elif isinstance(n, lr.Pre): walk(n.node)
    for form in lr.parse(text).forms: walk(form)
    return out


class BindClaims(unittest.TestCase):
    def test_real_carrier_and_no_caller_ready_flag(self):
        s = Path('books/commit-successor-binding.lisp').read_text()
        forms = functions(s)
        emit = forms['fn2-commit-successor-emit-current-p']
        self.assertIn('(fn2-successor-binder-idle-p fn2-id-engine)', emit)
        self.assertIn('(fn2-successor-emit-claim-current-p ', emit)
        completed = forms['fn2-commit-successor-bind-complete']
        self.assertIn('(fn2-successor-bind-claim-ready-p ', completed)
        self.assertIn('(equal len (fn2-succ-txns-emit-len tx fn2-succ-txns))', completed)
        self.assertIn('(fn2-machine-wake-row id fn2-core)', completed)
        cancelled = forms['fn2-commit-successor-bind-cancel']
        self.assertIn('(fn2-successor-bind-claim-cancelled-p ', cancelled)
        self.assertIn('*fn2-commit-state-dropping*', cancelled)
        self.assertIn('(= (fn2-commit-cb-wrote row fn2-commit) 0)', cancelled)
        self.assertNotIn('(fn2-successor-', completed.split('(defun ')[0])

    def test_one_registration_before_return_and_no_generic_schema_bypass(self):
        forms = functions(Path('books/commit.lisp').read_text())
        scan = forms['fn2-commit-txn-scan-claimed']
        self.assertIn('(fn2-commit-successor-emit-current-p tx txgen slot gen end', scan)
        common = forms['fn2-commit-admit-txn-claimed']
        self.assertLess(common.index('(fn2-commit-txn-open '), common.index('(fn2-commit-successor-bind-register '))
        self.assertIn('(mv :uncertain batch event fn2-core)', common)
        generic = forms['fn2-commit-admit-txn']
        self.assertIn('(fn2-commit-admit-txn-claimed *fn2-none* 0 ', generic)
        typed = forms['fn2-commit-admit-successor']
        self.assertIn('(fn2-commit-successor-emit-current-p tx txgen', typed)
        for name in ['fn2-commit-put-members', 'fn2-commit-put-txn-member']:
            self.assertIn('(bind-state *fn2-commit-bind-state-none*)', forms[name])
        self.assertIn('(equal (fn2-machine-cb-bind-pending id fn2-core) 0)', forms['fn2-commit-start'])

    def test_all_actual_publication_and_cleanup_boundaries(self):
        forms = functions(Path('books/commit.lisp').read_text())
        self.assertIn('(fn2-machine-cb-bind-pending id fn2-core)', forms['fn2-commit-root-swap'])
        self.assertIn('(fn2-machine-cb-bind-pending id fn2-core)', forms['fn2-commit-settle-member'])
        arms = Path('books/commit-arms.lisp').read_text()
        self.assertEqual(arms.count('(:if (not (equal row-cb-bind-pending 0)) ((:yield))'), 2)
        self.assertIn('((not (equal row-cb-bind-pending 0)) (:stop :commit-settle))', arms)
        self.assertIn('((:more) (:charge :steps *fn2-work-stage* :runnable t))', arms)
        self.assertIn('((:busy) (:yield))', arms)
        lower = Path('books/commit-successor-binding-state.lisp').read_text()
        self.assertIn('(fn2-commit-successor-bind-member batch event', lower)
        self.assertIn('(- event (fn2-commit-first-key row fn2-commit))', lower)

    def test_prepared_actual_witness_and_structural_arity(self):
        fixture = Path('tests/commit-successor-binding-unit.lisp').read_text()
        for actual in ['(fn2-successor-stage ', '(fn2-successor-emit ', '(fn2-commit-admit-successor ',
                       '(fn2-successor-bind ', '(fn2-commit-successor-bind-complete ',
                       '(eq premature :owner)', '(eq changed-length :owner)', '(eq repeated :already)']:
            self.assertIn(actual, fixture)
        for file in ['books/commit.lisp','books/commit-arms.lisp','books/commit-successor-binding.lisp',
                     'books/commit-successor-binding-state.lisp','tests/commit-successor-binding-unit.lisp']:
            def walk(n):
                if isinstance(n, lr.Lst):
                    if n.items and getattr(n.items[0], 'text', '') == 'if': self.assertEqual(len(n.items),4,file)
                    for child in n.items: walk(child)
                elif isinstance(n, lr.Pre): walk(n.node)
            for form in lr.parse(Path(file)).forms: walk(form)

    def test_scanner_class_replay_and_original_public_shape(self):
        r = json.loads(Path('tools/fixtures/commit-claimed-scan-transformation.json').read_text())
        current = functions(Path('books/commit.lisp').read_text())
        actual = current['fn2-commit-txn-scan-claimed']
        self.assertEqual(actual.count(r['inserted_claim_guard']), 1)
        self.assertEqual(actual.replace(r['inserted_claim_guard'], ''),
                         scan_transform.transform(r['scanner_original_form']))
        self.assertEqual(current['fn2-commit-txn-scan-shape'], r['scanner_original_shape'])
        sample = '(fn2-commit-txn-scan a b c fn2-core)'
        changed = scan_transform.transform(sample)
        self.assertEqual(changed, '(fn2-commit-txn-scan-claimed a b c tx txgen fn2-core)')
        self.assertEqual(scan_transform.transform(changed), changed)

if __name__ == '__main__':
    unittest.main()

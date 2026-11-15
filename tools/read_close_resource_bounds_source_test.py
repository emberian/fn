"""Source-only checks; actual count theorems/constructor teeth remain unrun."""
import argparse
from pathlib import Path
import sys
import unittest
import lisp_rewrite as lisp

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(add_help=False)
p.add_argument('--provider-root', type=Path, default=ROOT)
args, remaining = p.parse_known_args()
sys.argv = [sys.argv[0], *remaining]
PROVIDER = args.provider_root


def event(path, head, name):
    return lisp.match(None, lisp.parse(path).forms, deep=False, head=head, name=name)[0].node


def check_actual_result(form):
    calls = lisp.match(None, [form], head='fn2-run-load-region-park-check')
    return bool(calls) and all(
        lisp.flat(m.node.items[1]) == '1'
        for m in lisp.match(None, [form], head='mv-nth'))


class CloseResourceBounds(unittest.TestCase):
    def test_only_actual_result_contracts_no_model_or_runtime_function(self):
        path = ROOT / 'books/read-close-resource-bounds.lisp'
        forms = lisp.parse(path).forms
        self.assertFalse(lisp.match(None, forms, head='defun'))
        self.assertFalse(lisp.match(None, forms, head='defun-nx'))
        for match in lisp.match(None, forms, deep=False, head='defthm'):
            self.assertTrue(check_actual_result(match.node.items[2]))

    def test_read_specialization_is_actual_canonical_region_call(self):
        actual = event(PROVIDER / 'books/machines-c-read.lisp', 'defun', 'fn2-read-source-close')
        call = lisp.match(None, [actual], head='fn2-run-load-region-park')[0].node
        theorem = event(ROOT / 'books/read-close-resource-bounds.lisp', 'defthm',
                        'fn2-read-source-close-lease-count-bound')
        check = lisp.match(None, [theorem.items[2]], head='fn2-run-load-region-park-check')[0].node
        self.assertEqual(lisp.flat(check.items[1]), '0')
        self.assertEqual([lisp.flat(x) for x in check.items[2:]],
                         [lisp.flat(x) for x in call.items[1:]])
        self.assertEqual(lisp.flat(theorem.items[2].items[2]),
                         '(+ 1 *fn2-b-range-source-cursors*)')

    def test_budget_hypothesis_and_whole_teeth_are_retained(self):
        theorem = event(ROOT / 'books/read-close-resource-bounds.lisp', 'defthm',
                        'fn2-run-load-region-park-check-within-budget')
        formula = theorem.items[2]
        self.assertEqual(lisp.flat(formula.items[0]), 'implies')
        self.assertEqual(lisp.flat(formula.items[1]),
                         '(<= (nfix (- (fn2-run-load-region-count n0 n1 n2) (nfix i))) budget)')
        text = (ROOT / 'tests/read-close-resource-bounds-unit.lisp').read_text()
        self.assertIn('(<= whole-count 2)', text)
        self.assertIn('(not (<= whole-count 1))', text)
        self.assertIn('(not (<= (nfix (- (fn2-run-load-region-count 2 0 0) (nfix 0))) 1))', text)
        for active in (0, 1, 2):
            self.assertIn(f'(fn2-read-close-count-control {active} ', text)
        self.assertNotIn(':verify-guards nil', text)
        self.assertNotIn('skip-proofs', text)

    def test_result_projection_mutation_is_rejected(self):
        theorem = event(ROOT / 'books/read-close-resource-bounds.lisp', 'defthm',
                        'fn2-run-load-region-park-check-within-budget')
        source = lisp.flat(theorem.items[2])
        changed = lisp.parse(source.replace('(mv-nth 1 ', '(mv-nth 0 ', 1)).forms[0]
        self.assertTrue(check_actual_result(theorem.items[2]))
        self.assertFalse(check_actual_result(changed))


if __name__ == '__main__':
    unittest.main()

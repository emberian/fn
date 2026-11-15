"""SOURCE controls for the unrun logical scalar-domain questions."""
from pathlib import Path
import json
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr
import reader_foundation_batch as rw


def canon(n):
    if isinstance(n, lr.Lst):
        return tuple(canon(x) for x in n.items)
    if isinstance(n, lr.Pre):
        return n.prefix, canon(n.node)
    return n.text if isinstance(n, lr.Str) else n.low


class ScalarDomainSource(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / 'tests/checkpoint-reader-scalar-domain-unit.lisp').read_text()
        self.node = rw.unique(self.text, '(defun-nx fn2-checkpoint-reader-scalar-domain-check ?*body)')

    def test_entire_observed_original_antecedent(self):
        observed = json.loads((ROOT / 'tools/fixtures/checkpoint-reader-scalar-domain.json').read_text())
        actual = [n for n in rw.walk(self.node) if len(n.items) == 2 and rw.atom(n.items[0]) == 'whole-h'][0]
        expected = [lr.parse(s).forms[0] for s in observed['original_hypotheses']]
        self.assertEqual(tuple(map(canon, actual.items[1].items[1:])), tuple(map(canon, expected)))
        self.assertEqual(len(expected), 16)

    def test_positive_uses_actual_explicit_guard_and_actual_checker(self):
        body = (ROOT / 'books/checkpoint.lisp').read_text()
        fn = rw.unique(body, '(defun fn2-checkpoint-check-step ?*body)')
        xargs = [n for n in rw.walk(fn) if n.items and rw.atom(n.items[0]) == 'xargs'][0]
        at = next(i for i, n in enumerate(xargs.items) if rw.atom(n) == ':guard')
        explicit_guard = xargs.items[at + 1]
        whole = [n for n in rw.walk(self.node) if len(n.items) == 2 and rw.atom(n.items[0]) == 'whole-guard'][0]
        self.assertEqual(canon(explicit_guard), canon(whole.items[1]))
        calls = [n for n in rw.walk(self.node) if len(n.items) > 2 and rw.atom(n.items[0]) == 'fn2-checkpoint-check-step']
        self.assertEqual(len(calls), 1)
        self.assertIn('typed-readonly', self.text)

    def test_four_ground_statements_are_real_predicate_questions(self):
        claims = [n for n in lr.parse(self.text).forms if isinstance(n, lr.Lst) and n.items and rw.atom(n.items[0]) == 'defthm']
        self.assertEqual(len(claims), 4)
        actual = {canon(n.items[2]) for n in claims}
        expected = {canon(lr.parse('(fn2-checkpoint-reader-scalar-domain-check :' + x + ')').forms[0])
                    for x in ('checker', 'hasher', 'digests', 'positive')}
        self.assertEqual(actual, expected)
        self.assertNotIn('skip-proofs', self.text)
        self.assertNotIn('defaxiom', self.text)


if __name__ == '__main__':
    unittest.main()

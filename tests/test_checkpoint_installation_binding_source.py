"""Preserve actual installation conjunction and concrete hash comparison."""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr
import checkpoint_installation_match_rewrite as rw

def tree(n):
    return n.low if hasattr(n, 'low') else [tree(x) for x in n.items]

F = '*fn2-format-checkpoint-installation-field-descriptor-storage-domain*'
def normalize(x, env=None):
    env = env or {}
    if isinstance(x, str):
        return env.get(x, F if x == 'f' else x)
    if x and x[0] == 'fn2-cpe-f':
        return normalize(['fn2-fields-value', ['+', 'base', x[1]], 'fn2-fields'], env)
    result = [normalize(v, env) for v in x]
    if result and result[0] == '=':
        result[0] = 'equal'  # comparison on the caller's actual numeric domain
    if result and result[0] == '+':
        terms = []
        for term in result[1:]:
            terms.extend(term[1:] if isinstance(term, list) and term and term[0] == '+' else [term])
        result = ['+'] + [t for t in terms if t != '0']
    return result

class Binding(unittest.TestCase):
    def test_all_original_field_equalities_preserved(self):
        before = (ROOT/'tools/fixtures/checkpoint-installation-match-before.lisp').read_text()
        old = tree(lr.parse(before).forms[0])[1][1:-1]
        helper = tree(lr.parse((ROOT/'books/checkpoint-installation-binding.lisp').read_text()).forms[-1])
        call = tree(lr.parse(rw.call()).forms[0])
        env = dict(zip(helper[2], call[1:]))
        actual = helper[-1][3:]
        self.assertEqual(len(actual), 9)
        self.assertEqual([normalize(x) for x in old], [normalize(x, env) for x in actual])

    def test_original_concrete_hash_test_and_caller_coverage_stay(self):
        before = (ROOT/'tools/fixtures/checkpoint-installation-match-before.lisp').read_text()
        transformed = rw.transform(before)
        old = tree(lr.parse(before).forms[0])[1][-1]
        new = tree(lr.parse(transformed).forms[0])[1][-1]
        self.assertEqual(old, new)
        source = (ROOT/'books/checkpoint-recovery-evidence-records.lisp').read_text()
        self.assertIn('(< (fn2-checkpoints-cut-commit c fn2-checkpoints) (fn2-cpe commit))', source)
        self.assertIn('(< (fn2-checkpoints-cut-event c fn2-checkpoints) event)', source)
        self.assertIn('(<= (+ base *fn2-journal-record-fields*) (fn2-fields-rows fn2-fields))', source)
        self.assertIn('*fn2-format-checkpoint-installation-num-fields*', (ROOT/'books/journal-record-body.lisp').read_text())

    def test_stale_or_ambiguous_matcher_refuses(self):
        before = (ROOT/'tools/fixtures/checkpoint-installation-match-before.lisp').read_text()
        with self.assertRaises(ValueError):
            rw.transform('(unrelated)')
        with self.assertRaises(ValueError):
            rw.transform(before + before)

if __name__ == '__main__':
    unittest.main()

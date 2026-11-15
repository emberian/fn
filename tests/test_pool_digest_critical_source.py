"""Source-only controls; does not admit or execute ACL2 witness events."""
import re
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr


def form(text, head, name):
    matches = lr.match(f'({head} {name} ?*body)', lr.parse(text).forms, deep=False)
    if len(matches) != 1:
        raise AssertionError((head, name, len(matches)))
    return matches[0].node


class CriticalSource(unittest.TestCase):
    def test_registered_formulas_are_exact_originals(self):
        source = (ROOT / 'books/pool-digest.lisp').read_text()
        witness = (ROOT / 'tests/pool-digest-critical-unit.lisp').read_text()
        for old, new in [
            ('fn2-rec-fetch-exec-refines', 'fn2-rec-fetch-critical-refinement'),
            ('fn2-rec-fetch-step-progress-bound', 'fn2-rec-fetch-critical-progress'),
            ('fn2-rec-fetch-step-result-state', 'fn2-rec-fetch-critical-state'),
        ]:
            original = lr.flat(form(source, 'defthm', old).items[2])
            original = re.sub(r'(?<![\w-])fn2-pool(?![\w-])', 'p', original)
            original = re.sub(r'(?<![\w-])fn2-digests(?![\w-])', 'd', original)
            registered = lr.flat(form(witness, 'defthm-owed', new).items[3])
            self.assertEqual(original, registered)

    def test_guard_removal_is_explicit_and_zero_argument(self):
        witness = (ROOT / 'tests/pool-digest-critical-unit.lisp').read_text()
        tooth = form(witness, 'defun', 'fn2-rdc-without-off-logical')
        self.assertEqual(lr.flat(tooth.items[2]), '()')
        self.assertEqual(lr.flat(tooth.items[-1]),
                         '(with-guard-checking :none (fn2-rdc-run :without-off))')
        self.assertIn('(fn2-assert-owed-teeth fn2-rec-fetch-critical-refinement', witness)


if __name__ == '__main__':
    unittest.main()

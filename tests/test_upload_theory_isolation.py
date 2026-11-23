"""Exact original declaration and caller-theory restoration controls."""
from pathlib import Path
import subprocess
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_source as ls
BASE = '00fde7162511e8fb912b4e5feeb0276efa9f7877'
LOCAL = ls.read_sexp("(local (in-theory (union-theories '(fn2-machine-initial-generation fn2-machine-initial-next-free) (theory 'fn2-columns-proof-theory))))")
def check(before, after):
    old = [ls.read_sexp(f) for f in ls.forms(before)]
    new = [ls.read_sexp(f) for f in ls.forms(after)]
    targets = [i for i, f in enumerate(old) if f[:2] == ['defmachine', 'fn2-upload']]
    assert len(targets) == 1
    i = targets[0]
    assert new[i] == ['encapsulate', [], LOCAL, old[i]]
    assert new[:i] == old[:i] and new[i + 1:] == old[i + 1:]
class UploadTheoryIsolation(unittest.TestCase):
    def setUp(self):
        self.before = subprocess.check_output(['git', 'show', BASE + ':books/upload-kind.lisp'], cwd=ROOT, text=True)
        self.after = (ROOT / 'books/upload-kind.lisp').read_text()
    def test_exact_macro_and_all_other_original_forms(self):
        check(self.before, self.after)
    def test_original_runtime_declaration_mutation_rejected(self):
        with self.assertRaises(AssertionError):
            check(self.before, self.after.replace('(ofield 12)', '(ofield 13)'))
    def test_nonlocal_theory_or_extra_event_rejected(self):
        with self.assertRaises(AssertionError):
            check(self.before, self.after.replace('(local (in-theory', '(in-theory', 1))
        with self.assertRaises(AssertionError):
            check(self.before, self.after + '\n(in-theory (disable fn2-upload-capacity))\n')
if __name__ == '__main__':
    unittest.main()

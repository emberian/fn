"""Actual six row specs preserve all claims and existing proof overrides."""
from pathlib import Path
import subprocess
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from add_preservation_frame_hints import add_preservation_spec_frame_hints as transform
import lisp_source as ls
OBS = ('fn2-b3-rows', 'fn2-digests-rows')
BASE = 'c9e40602de6cc977e3ec25365cadd70fa53087d8'
def forms(text):
    return [ls.read_sexp(f) for f in ls.forms(text)]
class SourceHashFrameHints(unittest.TestCase):
    def setUp(self):
        self.before = subprocess.check_output(['git', 'show', BASE + ':books/cns-source-hash.lisp'], cwd=ROOT, text=True)
    def test_actual_six_frames_only_and_idempotence(self):
        result = transform(self.before, 'b3', OBS)
        self.assertEqual(result, (ROOT / 'books/cns-source-hash.lisp').read_text())
        self.assertEqual(transform(result, 'b3', OBS), result)
        old, new = forms(self.before), forms(result)
        changed = 0
        for a, b in zip(old, new):
            if a[0] == 'fn2-b3-preserves':
                i = a.index(':specs') + 1
                for x, y in zip(a[i], b[i]):
                    if ':frame' in x:
                        self.assertEqual(y[:-2], x)
                        self.assertEqual(y[-2], ':hints')
                        changed += 1
                    else:
                        self.assertEqual(x, y)
                b[i] = a[i]
            self.assertEqual(a, b)
        self.assertEqual(len(old), len(new))
        self.assertEqual(changed, 6)
    def test_explicit_nil_spec_hint_is_preserved(self):
        original = self.before.replace(':frame fn2-b3)', ':frame fn2-b3 :hints nil)', 1)
        result = transform(original, 'b3', OBS)
        self.assertIn(':frame fn2-b3 :hints nil)', result)
        self.assertEqual(result.count(':hints (("Goal" :in-theory (e/d ('), 5)
    def test_other_macro_class_untouched(self):
        self.assertEqual(transform(self.before, 'pool', OBS), self.before)
if __name__ == '__main__':
    unittest.main()

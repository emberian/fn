"""Source geometry controls; these do not evaluate or admit ACL2 events."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT = Path(__file__).resolve().parents[1]

def check(text):
    forms = lr.parse(text).forms
    required = [
        '(defun fn2-c-source-endpoint-rows (profile) (declare (xargs :guard t)) (+ 1 (nfix (fn2-profile-t profile)) (* 2 (fn2-b-read-rows profile))))',
        '(defun fn2-c-source-successor-endpoint (read-rows tx) (declare (xargs :guard (and (natp read-rows) (natp tx)))) (+ read-rows tx))',
        '(defun fn2-c-source-sealer-endpoint (read-rows successor-rows) (declare (xargs :guard (and (natp read-rows) (natp successor-rows)))) (+ read-rows successor-rows))',
        '(unsigned-byte-p 32 (fn2-c-source-endpoint-rows profile))',
        '(fn2-c-source-readers-init (fn2-c-source-endpoint-rows profile) fn2-c-source-readers)',
    ]
    for pattern in required:
        if not lr.match(pattern, forms):
            raise ValueError('source endpoint geometry/registration changed: '+pattern)

class Source(unittest.TestCase):
    def test_actual(self):
        check((ROOT/'books/machines-c.lisp').read_text())
    def test_missing_read_endpoint_region(self):
        text=(ROOT/'books/machines-c.lisp').read_text().replace('(* 2 (fn2-b-read-rows profile))','(fn2-b-read-rows profile)',1)
        with self.assertRaises(ValueError): check(text)
    def test_missing_profile_overflow_refusal(self):
        text=(ROOT/'books/machines-c.lisp').read_text().replace('(unsigned-byte-p 32 (fn2-c-source-endpoint-rows profile))','t',1)
        with self.assertRaises(ValueError): check(text)
    def test_regions_disjoint_at_empty_and_nonempty_profiles(self):
        # Arithmetic control of the source formula, not executable initialization.
        for t, r in [(0,0),(0,3),(4,0),(7,11)]:
            reads=set(range(r)); successors=set(range(r,r+t+r)); sealer=r+t+r
            self.assertFalse(reads & successors)
            self.assertNotIn(sealer, reads|successors)
            self.assertEqual(len(reads|successors|{sealer}), 1+t+2*r)
if __name__ == '__main__': unittest.main()

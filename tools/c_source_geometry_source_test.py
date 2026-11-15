"""Source geometry controls; these do not evaluate or admit ACL2 events."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT = Path(__file__).resolve().parents[1]

def check(text):
    forms = lr.parse(text).forms
    required = [
        '(defun fn2-c-source-endpoint-rows (profile) (declare (xargs :guard t)) (+ 1 (nfix (fn2-profile-t profile)) (* 2 (fn2-b-read-rows profile)) (fn2-b-cursor-rows profile) (fn2-b-cns-rows profile)))',
        '(defun fn2-c-source-successor-endpoint (read-rows tx) (declare (xargs :guard (and (natp read-rows) (natp tx)))) (+ read-rows tx))',
        '(defun fn2-c-source-sealer-endpoint (read-rows successor-rows) (declare (xargs :guard (and (natp read-rows) (natp successor-rows)))) (+ read-rows successor-rows))',
        '(defun fn2-c-source-request-endpoint (read-rows successor-rows cursor-row) (declare (xargs :guard (and (natp read-rows) (natp successor-rows) (natp cursor-row)))) (+ 1 read-rows successor-rows cursor-row))',
        '(defun fn2-c-source-cns-endpoint (read-rows successor-rows cursor-rows cns-row) (declare (xargs :guard (and (natp read-rows) (natp successor-rows) (natp cursor-rows) (natp cns-row)))) (+ 1 read-rows successor-rows cursor-rows cns-row))',
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
        for t, r, x, n in [(0,0,0,0),(0,3,1,1),(4,0,0,0),(7,11,4,2)]:
            reads=set(range(r)); successors=set(range(r,r+t+r)); sealer=r+t+r
            self.assertFalse(reads & successors)
            self.assertNotIn(sealer, reads|successors)
            requests=set(range(sealer+1,sealer+1+x))
            self.assertFalse(requests & (reads|successors|{sealer}))
            cns=set(range(sealer+1+x,sealer+1+x+n))
            self.assertFalse(cns & (reads|successors|{sealer}|requests))
            self.assertEqual(len(reads|successors|{sealer}|requests|cns), 1+t+2*r+x+n)
if __name__ == '__main__': unittest.main()

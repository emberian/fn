"""tools/list_codec_check.py: which host dispatches count as octet-list codec sites."""
import unittest
from pathlib import Path
import tempfile

from tools import list_codec_check as c


def sites_of(text):
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "x.lisp"
        p.write_text(text)
        out = c.scan([p])
    for s in out:
        s.pop("file", None)
    return [(s["defun"], s["entry"]) for s in out]


class SiteTests(unittest.TestCase):
    def test_a_direct_conversion_in_a_dispatch_is_a_site(self):
        self.assertEqual(
            sites_of("(defun f (v) (fnn-core 'fn-frame-decode (fnn-octet-list v)))"),
            [("f", "fn-frame-decode")])

    def test_a_let_bound_conversion_is_a_site(self):
        self.assertEqual(
            sites_of("(defun f (v) (let* ((xs (and v (fnn-octet-list v)))) (fnn-core 'fn-x xs)))"),
            [("f", "fn-x")])

    def test_mapcar_of_the_conversion_is_a_site(self):
        self.assertEqual(
            sites_of("(defun f (vs) (fnn-owner-core 'fn-y (mapcar #'fnn-octet-list vs)))"),
            [("f", "fn-y")])

    def test_a_dispatch_without_a_conversion_is_not_a_site(self):
        self.assertEqual(sites_of("(defun f (n) (fnn-core 'fn-z n (length n)))"), [])

    def test_a_buffer_dispatch_is_not_a_site(self):
        self.assertEqual(
            sites_of("(defun f () (fnn-octets-fill v) (fnn-core-buffer-state 'fn-z-buffer))"), [])

    def test_a_host_call_that_is_not_a_dispatch_is_not_a_site(self):
        self.assertEqual(sites_of("(defun f (v) (fnn-octets (fnn-octet-list v)))"), [])


class ClassTests(unittest.TestCase):
    def test_the_classes_name_the_row_and_the_baseline_only_shrinks(self):
        base = c.load_baseline()
        sites = c.scan()
        c.classify(sites, base["classes"])
        now = c.counts(sites)
        for f, n in now.items():
            self.assertLessEqual(n, base["sites"].get(f, 0), f)
        self.assertLessEqual(sum(now.values()), base["total"])

    def test_an_identity_entry_outside_the_classes_is_not_counted(self):
        sites = [{"file": "h", "defun": "d", "entry": "fn-owner-post-boundary"}]
        c.classify(sites, c.load_baseline()["classes"])
        self.assertEqual(c.counts(sites), {})


if __name__ == "__main__":
    unittest.main()

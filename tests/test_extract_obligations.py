"""tools/extract/obligations.py: the canonical printer both sides evaluate (laptop SBCL), and the item
comparison (incomplete output, exclusions, a differing item)."""
import importlib.util
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("obligations", ROOT / "tools/extract/obligations.py")
ob = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ob)
SBCL = shutil.which("sbcl")


def lisp(body):
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "t.lisp"
        f.write_text('(defpackage "ACL2" (:use "COMMON-LISP"))\n(in-package "ACL2")\n' + ob.PRINTER + body)
        r = subprocess.run([SBCL, "--script", str(f)], capture_output=True, text=True, timeout=120)
    assert r.returncode == 0, r.stdout + r.stderr
    return r.stdout.strip().splitlines()


@unittest.skipUnless(SBCL, "SBCL required")
class PrinterTests(unittest.TestCase):
    def test_shared_structure_prints_in_full_and_a_cycle_is_named(self):
        out = lisp("""
(let* ((tail (list 1 2)) (shared (list (cons 'a tail) (cons 'b tail))) (copy (list (list 'a 1 2) (list 'b 1 2)))
       (cyc (list 1 2)))
  (setf (cdr (last cyc)) cyc)
  (format t "~a~%~a~%~a~%" (xt-ob-text shared) (xt-ob-text copy) (xt-ob-text cyc)))""")
        self.assertEqual(out[0], out[1])
        self.assertIn("#cycle", out[2])

    def test_atoms_print_independently_of_reader_state(self):
        out = lisp("""(format t "~a~%" (xt-ob-text (list (make-symbol "G7") :k 'foo "ab" #\\a 3/4 -2
  (make-array 3 :element-type '(unsigned-byte 8) :initial-contents '(1 2 3)))))""")
        self.assertEqual(out[0], '(#: KEYWORD::K ACL2::FOO "97,98" #\\97 3/4 -2 #A(3)(UNSIGNED-BYTE 8)(1 2 3))')

    def test_a_large_numeric_array_prints_a_hash_not_its_elements(self):
        out = lisp("""(let ((a (make-array 5000 :element-type '(unsigned-byte 64) :initial-element 7))
      (b (make-array 5000 :element-type '(unsigned-byte 64) :initial-element 7)))
  (setf (aref b 4999) 8)
  (format t "~a~%~a~%" (xt-ob-text a) (xt-ob-text b)))""")
        self.assertIn("hash", out[0])
        self.assertNotEqual(out[0], out[1])


class CompareTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.d = Path(self.tmp.name)
        (self.d / "expected.count").write_text("2\n")

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, image, core):
        (self.d / "image.out").write_text("\n".join(image) + "\n")
        (self.d / "core.out").write_text("\n".join(core) + "\n")

    def test_identical_items_pass(self):
        lines = ["OB VAR ACL2::*X* 1", "OB ENTRY ACL2::F ((1) NIL)", "OB-END 2"]
        self.write(lines, lines)
        self.assertEqual(ob.compare(self.d), 0)

    def test_a_differing_item_fails(self):
        self.write(["OB VAR ACL2::*X* 1", "OB ENTRY ACL2::F ((1) NIL)", "OB-END 2"],
                   ["OB VAR ACL2::*X* 1", "OB ENTRY ACL2::F (KEYWORD::UNKNOWN NIL)", "OB-END 2"])
        self.assertEqual(ob.compare(self.d), 1)

    def test_a_truncated_side_fails_even_when_the_printed_items_agree(self):
        self.write(["OB VAR ACL2::*X* 1", "OB ENTRY ACL2::F ((1) NIL)", "OB-END 2"], ["OB VAR ACL2::*X* 1"])
        self.assertEqual(ob.compare(self.d), 1)

    def test_book_paths_under_each_sides_checkout_compare_equal(self):
        img = '"%s"' % ob.encoded("/img/tree/books/a.lisp")
        core = '"%s"' % ob.encoded("/core/tree10/books/a.lisp")
        self.write(["OB WORLD ACL2::K (%s)" % img, "OB VAR ACL2::*X* 1", "OB-END 2"],
                   ["OB WORLD ACL2::K (%s)" % core, "OB VAR ACL2::*X* 1", "OB-END 2"])
        self.assertEqual(ob.compare(self.d), 1)
        (self.d / "image.root").write_text("/img/tree\n")
        (self.d / "core.root").write_text("/core/tree10\n")
        self.assertEqual(ob.compare(self.d), 0)

    def test_an_excluded_item_is_not_compared(self):
        self.write(["OB VAR ACL2::*AOKP* 1", "OB VAR ACL2::*X* 1", "OB-END 2"],
                   ["OB VAR ACL2::*AOKP* 2", "OB VAR ACL2::*X* 1", "OB-END 2"])
        self.assertEqual(ob.compare(self.d), 0)


if __name__ == "__main__":
    unittest.main()

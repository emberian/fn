"""tools/host_macro_order_check.py: the check refuses a macro used before its
definition in load order and passes the tree (lane ops-fixes)."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import host_macro_order_check as check  # noqa: E402


class HostMacroOrderTests(unittest.TestCase):
    def files(self, *texts):
        work = Path(tempfile.mkdtemp(prefix="fn-macro-order-"))
        paths = []
        for i, text in enumerate(texts):
            path = work / ("f%d.lisp" % i)
            path.write_text(text, encoding="utf-8")
            paths.append(path)
        return paths

    def test_the_tree_passes(self):
        self.assertEqual(check.check(check.load_order()), [])
        self.assertIn(ROOT / "host" / "native" / "io.lisp", check.load_order())

    def test_batch_aw_shape_is_refused(self):
        # The use above the definition, in one file (io.lisp at batch AW).
        early = check.check(self.files(
            "(defun f (log)\n  (fnn-log-with-kernel (log) (g log)))\n"
            "(defmacro fnn-log-with-kernel ((log) &body body)\n  `(progn ,log ,@body))\n"))
        self.assertEqual(len(early), 1, early)
        self.assertIn(":2 uses fnn-log-with-kernel before its definition", early[0])

    def test_a_use_in_an_earlier_loaded_file_is_refused(self):
        early = check.check(self.files("(defun f () (m 1))\n", "(defmacro m (x) x)\n"))
        self.assertEqual(len(early), 1, early)

    def test_uses_after_the_definition_and_in_comments_or_strings_pass(self):
        self.assertEqual(check.check(self.files(
            "; (m 1) in a comment\n(defun doc () \"(m 2) in a string\")\n"
            "(defmacro m (x) x)\n(defun f () (m 3))\n", "(defun g () (m 4))\n")), [])


if __name__ == "__main__":
    unittest.main()

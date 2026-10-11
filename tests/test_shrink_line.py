"""tools/shrink_line.py: the per-train book count and executable-line change."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import shrink_line  # noqa: E402

BOOK = """; a book
(defun fn-a (x) (fn-b x))

(defun fn-b (x)
  (+ x 1))

(defun fn-unreached (x) x)

(encapsulate ()
  (local (defun fn-local (x) x))
  (defun-inline fn-c (x)
    (fn-b x)))

(defabsstobj fn-st
  :exports ((fn-st-get :logic fn-st$a-get :exec fn-st$c-get)))

(defun fn-st$c-get (x)
  x)
"""
HOST = "(defun fnn-run () (fnn-call 'fn-a) (fn-c$inline 1) (fn-st-get 2))\n"


class ShrinkLineTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "books").mkdir()
        (self.root / "host" / "native").mkdir(parents=True)
        self.git("init", "-q")
        self.git("config", "user.email", "t@example.invalid")
        self.git("config", "user.name", "t")

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args], check=True,
                              capture_output=True, text=True).stdout.strip()

    def commit(self, files):
        for path, text in files.items():
            (self.root / path).parent.mkdir(parents=True, exist_ok=True)
            (self.root / path).write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "c")
        return self.git("rev-parse", "HEAD")

    def test_closure_from_host_names_through_inline_nested_and_exports(self):
        rev = self.commit({"books/a.lisp": BOOK, "host/native/run.lisp": HOST})
        m = shrink_line.measure(self.root, rev)
        self.assertEqual(m["books"], 1)
        # reached: fn-a (1 line), fn-b (2), fn-c (2, nested), fn-c$inline (0),
        # fn-st-get (0, an export edge), fn-st$c-get (2); fn-unreached and the local
        # definition are not
        self.assertEqual(m["executable_functions"], 6)
        self.assertEqual(m["executable_lines"], 1 + 2 + 2 + 2)

    def test_line_reports_the_change_against_the_base(self):
        base = self.commit({"books/a.lisp": BOOK, "host/native/run.lisp": HOST})
        grown = BOOK.replace("(+ x 1))", "(+ x (fn-new x)))") + "\n(defun fn-new (x)\n  (* x\n     2))\n"
        head = self.commit({"books/a.lisp": grown, "books/b.lisp": "(defun fn-z () 1)\n",
                            "tools/t.py": "x = 1\n"})
        line = shrink_line.line(self.root, base, head)
        self.assertIn("books 2 (+1)", line)
        self.assertIn("executable 10 lines (+3) in 7 functions (+1)", line)
        self.assertIn("net lines books +5 tools +1", line)
        # the base's measure is cached by tree id and reused
        self.assertTrue(any((self.root / shrink_line.CACHE).iterdir()))
        self.assertEqual(shrink_line.line(self.root, base, head), line)


if __name__ == "__main__":
    unittest.main()

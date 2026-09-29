"""tools/callers.py: call sites by file:line, classified, never from comments."""

import importlib.util
import io
import json
from contextlib import redirect_stdout
from pathlib import Path
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parent.parent / "tools"
SPEC = importlib.util.spec_from_file_location("callers", TOOLS / "callers.py")
callers = importlib.util.module_from_spec(SPEC)
sys.modules["callers"] = callers
SPEC.loader.exec_module(callers)

BOOK = """(in-package "ACL2")
; (fn-xy-step 1) in a comment is not a call
#| a block (fn-xy-step 2) #| nested |# still (fn-xy-step 3) |#
(defun fn-xy-step (x)
  (if (zp x) 0 (fn-xy-step (1- x))))

(defun fn-xy-stepper (x) (acl2::FN-XY-STEP x))

(defthm fn-xy-step-natp
  (natp (fn-xy-step x))
  :hints (("Goal" :in-theory (disable fn-xy-step))))

(defconst *fn-xy-doc* "(fn-xy-step 4) in a string")
(defmacro fn-xy-m (x) `(fn-xy-step ,x))
(defun fn-xy-q () '(#\\( fn-xy-step))
"""

HOST = """(in-package "FN-HOST")
(defun host-go (x) (acl2::fn-xy-step x))
(setf *table* (list #'fn-xy-step))
"""

TEST_PY = """def test_step():
    run("(fn-xy-step 3)")  # fn-xy-stepper is a different name
"""


class CallersTests(unittest.TestCase):
    def tree(self, directory: str) -> Path:
        root = Path(directory)
        (root / "books").mkdir()
        (root / "host").mkdir()
        (root / "tests").mkdir()
        (root / "build" / "lanes").mkdir(parents=True)
        (root / "books/xy.lisp").write_text(BOOK)
        (root / "host/go.lisp").write_text(HOST)
        (root / "tests/test_xy.py").write_text(TEST_PY)
        (root / "build/lanes/copy.lisp").write_text("(fn-xy-step 9)\n")
        return root

    def sites(self, root: Path) -> list[tuple[str, int, str, str]]:
        return [(site["file"], site["line"], site["kind"], site["event"])
                for site in callers.scan(root, ["fn-xy-step"],
                                         list(callers.DEFAULT_PLACES))]

    def test_calls_definitions_and_mentions_by_line_and_event(self):
        with tempfile.TemporaryDirectory() as directory:
            sites = self.sites(self.tree(directory))
        self.assertEqual(sites, [
            ("books/xy.lisp", 4, "define", "defun fn-xy-step"),
            ("books/xy.lisp", 5, "call", "defun fn-xy-step"),
            ("books/xy.lisp", 7, "call", "defun fn-xy-stepper"),
            ("books/xy.lisp", 10, "call", "defthm fn-xy-step-natp"),
            ("books/xy.lisp", 11, "mention", "defthm fn-xy-step-natp"),
            ("books/xy.lisp", 14, "call", "defmacro fn-xy-m"),
            # a quoted list's element after a character: data, not a call
            ("books/xy.lisp", 15, "mention", "defun fn-xy-q"),
            ("host/go.lisp", 2, "call", "defun host-go"),
            ("host/go.lisp", 3, "mention", "setf *table*"),
            ("tests/test_xy.py", 2, "text", ""),
        ])

    def test_the_theorem_named_after_the_function_is_not_a_definition_of_it(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory)
            sites = callers.scan(root, ["fn-xy-step-natp"], ["books"])
        self.assertEqual([(s["line"], s["kind"]) for s in sites], [(9, "define")])

    def test_cli_prints_file_line_and_exits_by_whether_anything_calls(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory)
            out = io.StringIO()
            with redirect_stdout(out):
                code = callers.main(["fn-xy-step", "--root", str(root)])
            self.assertEqual(code, 0)
            text = out.getvalue()
            self.assertIn("books/xy.lisp:7: call  in (defun fn-xy-stepper ...)", text)
            self.assertNotIn("mention", text.splitlines()[0])
            self.assertIn("define 1, call 5, mention 3, text 1", text)
            self.assertNotIn("build/", text)
            out = io.StringIO()
            with redirect_stdout(out):
                code = callers.main(["fn-xy-nothing", "--root", str(root), "--json"])
            self.assertEqual(code, 1)
            self.assertEqual(json.loads(out.getvalue())["sites"], [])


if __name__ == "__main__":
    unittest.main()

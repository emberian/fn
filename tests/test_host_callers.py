"""Teeth for tools/host_callers.py (lane uncalled-host-defuns): over a small
tree, a host definition is `called' through each kind of mention the tool
counts (a raw file's quoted `fnn-core' entry, a book, a Python bridge's form
built as text, a launcher, a registry row, a string literal), `test-only'
when only tests/ names it, and `zero' when nothing does -- including two
definitions that name only each other, a mention in a comment or a doc, and
a name that only extends a longer symbol."""
from __future__ import annotations

import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
os.environ["FN_CALLGRAPH_CACHE"] = "0"
import host_callers  # noqa: E402

TREE = {
    "host/x-host.lisp": """
(in-package "ACL2")
(defun fn-x-host-quoted (a) a)
(defun fn-x-host-book () 1)
(defun fn-x-host-bridge () 2)
(defun fn-x-host-launcher () 3)
(defun fn-x-host-registry () 4)
(defun fn-x-host-string () 5)
(defun fn-x-host-by-test () 6)
(defun fn-x-host-via-live () (fn-x-host-callee))
(defun fn-x-host-callee () 7)
(defun fn-x-host-ping () (fn-x-host-pong))
(defun fn-x-host-pong () (fn-x-host-ping))
; fn-x-host-commented is named only in this comment
(defun fn-x-host-commented () 8)
(defun fn-x-host-doc () 9)
(defun fn-x-host-prefix () 10)
""",
    "host/native/x.lisp": """
(in-package "ACL2")
(defun fnn-x-entry () (fnn-core 'fn-x-host-quoted 1) (fn-x-host-via-live))
(defvar *fnn-x-names* '("FN-X-HOST-STRING"))
(fnn-x-entry)
""",
    "books/x.lisp": "(defun fn-x-book () (fn-x-host-book))\n",
    "tools/x_bridge.py": 'FORM = "(fn-x-host-bridge)"\n',
    "packaging/fn-x": "exec sbcl --eval '(fn-x-host-launcher)'\n",
    "planning/requirements.json": '{"host": "fn-x-host-registry"}\n',
    "tests/test_x.py": 'CALL = "(fn-x-host-by-test)"\n',
    "docs/x.md": "`fn-x-host-doc` is documented here.\n",
    "tools/y.py": 'OTHER = "fn-x-host-prefix-longer"\n',
}


class HostCallersTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="fn-host-callers-")
        root = Path(cls.temp.name)
        for relative, text in TREE.items():
            (root / relative).parent.mkdir(parents=True, exist_ok=True)
            (root / relative).write_text(text)
        rows, unreadable = host_callers.table(root, sorted(TREE))
        cls.rows = {row["name"]: row for row in rows}
        cls.unreadable = unreadable

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def status(self, name):
        return self.rows[name]["status"]

    def test_every_kind_of_caller_makes_it_called(self):
        for name in ("fn-x-host-quoted", "fn-x-host-book", "fn-x-host-bridge",
                     "fn-x-host-launcher", "fn-x-host-registry", "fn-x-host-string",
                     "fn-x-host-via-live", "fn-x-host-callee", "fnn-x-entry"):
            self.assertEqual(self.status(name), "called", name)
        self.assertEqual(self.rows["fn-x-host-string"]["string"], 1)
        self.assertEqual(self.rows["fn-x-host-launcher"]["script"], 1)
        self.assertEqual(self.rows["fn-x-host-registry"]["registry"], 1)

    def test_a_test_caller_is_test_only(self):
        self.assertEqual(self.status("fn-x-host-by-test"), "test-only")

    def test_nothing_reaches_is_zero(self):
        for name in ("fn-x-host-commented", "fn-x-host-doc", "fn-x-host-prefix"):
            self.assertEqual(self.status(name), "zero", name)
            self.assertFalse(self.rows[name]["cluster"], name)
        self.assertEqual(self.rows["fn-x-host-doc"]["doc"], 1)

    def test_a_cluster_naming_only_itself_is_zero(self):
        for name in ("fn-x-host-ping", "fn-x-host-pong"):
            self.assertEqual(self.status(name), "zero", name)
            self.assertTrue(self.rows[name]["cluster"], name)

    def test_the_tree_read(self):
        self.assertEqual(self.unreadable, {})
        self.assertEqual(len(self.rows), 15)


if __name__ == "__main__":
    unittest.main()

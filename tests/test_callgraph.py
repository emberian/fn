"""tools/callgraph.py: the call graph through defun AND defmacro bodies.

Lane defprotocol's reply-code inventory saw a shallow closure once the NNTP
dispatcher became a macro; these tests pin that a macro's template is
followed, and that what the reader drops (comments, strings) is not an edge.
"""
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import callgraph                                              # noqa: E402

BOOK = r'''
(defmacro dispatch (archive-call)
  `(if (arm-keyword-p keyword)
       ,archive-call
     (arm-single session "501")))

(defun command (session keyword)
  ; a comment naming ghost-in-comment is not a call
  "a docstring naming ghost-in-string is not a call either"
  (dispatch (arm-archive session keyword)))

(defun arm-keyword-p (k) (stringp k))
(defun arm-single (s line) (list s line))
(defun arm-archive (s k) (list s k (deep-helper k)))
(defun deep-helper (k) k)
(defun ghost-in-comment (x) x)
(defun ghost-in-string (x) x)

(encapsulate ()
  (local (defun nested-local (x) (deep-helper x)))
  (mutual-recursion
   (defun even-walk (x) (if (consp x) (odd-walk (cdr x)) t))
   (defun odd-walk (x) (if (consp x) (even-walk (cdr x)) nil))))

(defmacro writes-a-defun (name)
  `(progn (defun not-a-definition (x) x)
          (defun ,name (y) (deep-helper y))))

(defun builds-from-a-quote (x) (list 'arm-single x))
'''


class CallgraphTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.TemporaryDirectory()
        path = Path(cls.dir.name) / "toy.lisp"
        path.write_text(BOOK, encoding="utf-8")
        cls.graph = callgraph.build([(path, "books/toy.lisp")])

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def test_a_macro_template_is_followed(self):
        reached = self.graph.reach("command")
        for name in ("dispatch", "arm-keyword-p", "arm-single", "arm-archive", "deep-helper"):
            self.assertIn(name, reached)
        self.assertEqual(reached["dispatch"], 1)
        self.assertEqual(reached["arm-single"], 2)   # through the macro
        self.assertEqual(self.graph.kind("dispatch"), "macro")

    def test_comments_and_strings_are_not_edges(self):
        reached = self.graph.reach("command")
        self.assertNotIn("ghost-in-comment", reached)
        self.assertNotIn("ghost-in-string", reached)

    def test_nested_definitions_are_definitions(self):
        for name in ("nested-local", "even-walk", "odd-walk"):
            self.assertIn(name, self.graph.definitions)
        self.assertIn("odd-walk", self.graph.reach("even-walk"))

    def test_a_template_defun_is_not_a_definition(self):
        self.assertNotIn("not-a-definition", self.graph.definitions)
        self.assertIn("deep-helper", self.graph.reach("writes-a-defun"))

    def test_a_quoted_symbol_is_a_mention(self):
        self.assertIn("arm-single", self.graph.reach("builds-from-a-quote"))

    def test_depth_and_callers(self):
        self.assertEqual(set(self.graph.reach("command", depth=1)), {"dispatch", "arm-archive"})
        self.assertIn("command", self.graph.callers("deep-helper"))


class TreeTests(unittest.TestCase):
    """The real dispatcher (books/nntp.lisp)."""

    def test_the_nntp_dispatcher_macro_reaches_its_arms(self):
        graph = callgraph.build(callgraph.ledger.book_paths())
        reached = graph.reach("fn-nntp-command")
        self.assertIn("fn-nntp-command-dispatch", reached)
        self.assertEqual(graph.kind("fn-nntp-command-dispatch"), "macro")
        # Only the macro's template names these.
        self.assertIn("fn-nntp-session-command", reached)
        self.assertIn("fn-nntp-keyword-tokenp", reached)
        self.assertEqual(graph.unreadable, {})


if __name__ == "__main__":
    unittest.main()

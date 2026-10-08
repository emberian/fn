"""tools/interfaces_relocate.py: each definterface moves next to its entry's definition."""
import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from tools import interface_emit, interfaces_relocate as ir

BUILD = ('(ld "host/a-host.lisp" :ld-error-action :error)\n(ld "host/b-host.lisp" :ld-error-action :error)\n'
         '(ld "host/c-host.lisp" :ld-error-action :error)\n(ld "host/d-host.lisp" :ld-error-action :error)\n'
         '(ld "host/native/e-model-host.lisp" :ld-error-action :error)\n')

E = '(in-package "ACL2")\n(defun fn-e-model (x) x)\n'

E_AFTER = '(in-package "ACL2")\n(defun fn-e-model (x) x)\n\n(definterface fn-e-model :class :common-lisp-compliant)\n'

A = """(in-package "ACL2")
(defun fn-a-simple (x) (declare (xargs :guard t)) x)
(defun fn-a-first (x) x)
(defun fn-a-second (x) (fn-a-first x))
(verify-guards fn-a-second)
(defun fn-a-third (x) x)
"""

B = """(in-package "ACL2")
(defun fn-b-entry (x) x)
(defthm fn-b-entry-holds (equal (fn-b-entry x) x))
"""

C = """(in-package "ACL2")
(include-book "../books/book")
(defun fn-c-entry (x) (fn-book-entry x))
"""

D = """(in-package "ACL2")
(include-book "../books/book")
(defun fn-d-entry (x) (fn-book-entry x))
"""

OTHER = '(in-package "ACL2")\n(defthm fn-other-holds (equal 1 1))\n'

TESTS = '(in-package "ACL2")\n(include-book "../../host/c-host")\n(include-book "../../host/d-host")\n'

BOOK = '(in-package "ACL2")\n(defun fn-book-entry (x) x)\n(defun fn-book-two (x) x)\n'

IFACES = """(in-package "ACL2")
(include-book "../books/definterface")
; the section header stays here

(definterface fn-a-simple :class :common-lisp-compliant)

; A comment about the second entry,
; over two lines.
(definterface fn-a-second :class :common-lisp-compliant)
(definterface fn-book-entry :class :common-lisp-compliant)

(definterface fn-a-third :class :common-lisp-compliant
  :keystones (fn-b-entry-holds))
(definterface fn-generated :class :program)
(definterface fn-c-entry :class :common-lisp-compliant)
(definterface fn-d-entry :class :common-lisp-compliant
  :keystones (fn-other-holds))
(definterface fn-e-model :class :common-lisp-compliant)
(definterface fn-book-two :class :common-lisp-compliant
  :keystones (fn-b-entry-holds))
"""

GUARDS = '(in-package "ACL2")\n(include-book "book")\n(verify-guards fn-book-entry)\n'

IFACES_AFTER = """(in-package "ACL2")
(include-book "../books/definterface")
(include-book "../books/book")
(include-book "../books/guards")
(include-book "../books/other")
; the section header stays here


(definterface fn-book-entry :class :common-lisp-compliant)

(definterface fn-generated :class :program)
(definterface fn-d-entry :class :common-lisp-compliant
  :keystones (fn-other-holds))
"""

A_AFTER = """(in-package "ACL2")
(include-book "../books/definterface")
(defun fn-a-simple (x) (declare (xargs :guard t)) x)

(definterface fn-a-simple :class :common-lisp-compliant)
(defun fn-a-first (x) x)
(defun fn-a-second (x) (fn-a-first x))
(verify-guards fn-a-second)

; A comment about the second entry,
; over two lines.
(definterface fn-a-second :class :common-lisp-compliant)
(defun fn-a-third (x) x)
"""

B_AFTER = """(in-package "ACL2")
(include-book "../books/definterface")
(include-book "../books/book")
(defun fn-b-entry (x) x)
(defthm fn-b-entry-holds (equal (fn-b-entry x) x))

(definterface fn-a-third :class :common-lisp-compliant
  :keystones (fn-b-entry-holds))

(definterface fn-book-two :class :common-lisp-compliant
  :keystones (fn-b-entry-holds))
"""


C_AFTER = """(in-package "ACL2")
(include-book "../books/book")
(include-book "../books/definterface")
(defun fn-c-entry (x) (fn-book-entry x))

(definterface fn-c-entry :class :common-lisp-compliant)
"""


class RelocateTests(unittest.TestCase):
    def tree(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        for relative, text in {"host/native/build.lisp": BUILD, "host/a-host.lisp": A,
                               "host/b-host.lisp": B, "books/book.lisp": BOOK,
                               "host/c-host.lisp": C, "host/d-host.lisp": D,
                               "books/other.lisp": OTHER, "tests/acl2/c-tests.lisp": TESTS,
                               "host/interfaces.lisp": IFACES,
                               "host/native/e-model-host.lisp": E,
                               "books/guards.lisp": GUARDS}.items():
            (root / relative).parent.mkdir(parents=True, exist_ok=True)
            (root / relative).write_text(text)
        return root

    def run_tool(self, root, *args):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = ir.main(["--root", str(root), *args])
        return code, out.getvalue()

    def test_the_output_is_the_hand_moved_files_byte_for_byte(self):
        root = self.tree()
        self.run_tool(root, "--write")
        self.assertEqual((root / "host/a-host.lisp").read_text(), A_AFTER)
        self.assertEqual((root / "host/b-host.lisp").read_text(), B_AFTER)
        self.assertEqual((root / "host/c-host.lisp").read_text(), C_AFTER,
                         "a certified book gets books/definterface included")
        self.assertEqual((root / "host/d-host.lisp").read_text(), D, "its keystone's book is not in its world")
        self.assertEqual((root / "host/native/e-model-host.lisp").read_text(), E_AFTER,
                         "an ld'd ACL2 file under host/native/ is a host file like one in host/")
        self.assertEqual((root / "host/interfaces.lisp").read_text(), IFACES_AFTER)

    def test_a_cost_annotation_is_not_a_definition(self):
        # def-cost / def-operation-check name a book's function in a host file; the
        # declaration of that function must stay where the check can see it first.
        root = self.tree()
        (root / "host/b-host.lisp").write_text(
            B + "(def-cost fn-book-two :visits 0)\n(def-operation-check fn-book-two)\n")
        index = ir.Index(root)
        self.assertEqual([d[0] for d in index.defs["fn-book-two"]], ["books/book.lisp"])

    def test_it_reports_and_refuses_what_it_cannot_place(self):
        root = self.tree()
        code, out = self.run_tool(root)
        self.assertEqual(code, 1)
        self.assertIn("REFUSED no-definition: fn-generated", out)
        self.assertIn("REFUSED certified-book: fn-d-entry", out)
        self.assertIn("6 moved into 4 host file(s)", out)
        self.assertIn("book-defined 1", out)
        self.assertEqual((root / "host/interfaces.lisp").read_text(), IFACES, "a report writes nothing")

    def test_interface_emit_reads_the_declarations_where_they_now_are(self):
        root = self.tree()
        before = [(d["name"], d["class"]) for d in interface_emit.declarations(root)]
        self.run_tool(root, "--write")
        after = interface_emit.declarations(root)
        self.assertEqual(sorted(before), sorted((d["name"], d["class"]) for d in after))
        self.assertEqual({d["name"]: d["source"] for d in after}["fn-a-third"], "host/b-host.lisp")
        self.assertEqual({d["name"]: d["source"] for d in after}["fn-e-model"], "host/native/e-model-host.lisp")
        self.assertEqual({d["name"]: d["source"] for d in after}["fn-book-two"], "host/b-host.lisp",
                         "a book entry whose declaration names a host-defined keystone goes after it")

    def test_includes_only_repairs_an_unreferenced_standalone_root(self):
        root = self.tree()
        path = root / "host/standalone.lisp"
        path.write_text('(in-package "ACL2")\n(defun standalone (x) x)\n'
                        '(definterface standalone :class :program)\n')
        self.run_tool(root, "--includes-only", "--write")
        self.assertIn('(include-book "../books/definterface")', path.read_text())
        self.assertIn('(definterface fn-a-simple', (root / "host/interfaces.lisp").read_text())
        self.assertEqual({}, ir.include_edits(root))

    def test_dependency_transformation_checks_cycles_and_is_idempotent(self):
        root = self.tree()
        request = {"host/a-host.lisp": ["host/b-host.lisp"]}
        out = ir.dependency_edits(root, request)
        self.assertIn('(include-book "b-host")', out["host/a-host.lisp"])
        for rel, text in out.items():
            (root / rel).write_text(text)
        self.assertEqual({}, ir.dependency_edits(root, request))
        with self.assertRaisesRegex(ValueError, "include cycle"):
            ir.dependency_edits(root, {"host/b-host.lisp": ["host/a-host.lisp"]})
        with self.assertRaisesRegex(ValueError, "include cycle"):
            ir.dependency_edits(root, {"host/c-host.lisp": ["host/d-host.lisp"],
                                      "host/d-host.lisp": ["host/c-host.lisp"]})

    def test_a_second_run_moves_nothing(self):
        root = self.tree()
        self.run_tool(root, "--write")
        _code, out = self.run_tool(root, "--write")
        self.assertIn("0 moved", out)
        self.assertEqual((root / "host/interfaces.lisp").read_text(), IFACES_AFTER)


if __name__ == "__main__":
    unittest.main()

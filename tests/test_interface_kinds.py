"""tools/interface_kinds.py and `interface_emit.py --kinds': the guard kinds
books/definterface.lisp's fn-di-world-kinds requires, computed from source."""
from __future__ import annotations

import contextlib
import io
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import interface_emit, interface_kinds, ledger  # noqa: E402

KINDS_BOOK = """(in-package "ACL2")
(defconst *fn-entry-guard-kinds*
  '((fn-payload-handle-p . "a payload handle")
    (fn-cbor-octet-listp . "octets")
    (natp . "a natural")
    (integerp . "an integer")
    (stringp . "a string")
    (true-listp . "a NIL-terminated list")))
"""

BOOK = """(in-package "ACL2")
(defun fn-k-plain (octets n name)
  (declare (xargs :guard (and (stringp name) (natp n) (fn-cbor-octet-listp octets)
                              (consp octets) (< n 10) (natp (car octets)))))
  (list octets n name))
(defun fn-k-stobj (st n state)
  (declare (xargs :stobjs (st state) :guard (and (natp st) (natp state) (natp n))))
  (list st n state))
(defund fn-k-types (a b)
  (declare (type integer a) (type (satisfies fn-cbor-octet-listp) b))
  (list a b))
(defun fn-k-tie (n)
  (declare (xargs :guard (and (integerp n) (natp n))))
  n)
(encapsulate ()
  (local (defun fn-k-inner (h) (declare (xargs :guard (fn-payload-handle-p h))) h)))
(defun fn-k-none (x) x)
"""

INTERFACES = """(in-package "ACL2")
(definterface fn-k-plain :class :common-lisp-compliant
  :kinds ((octets fn-cbor-octet-listp) (n natp) (name stringp)))
(definterface fn-k-types :class :common-lisp-compliant :kinds ((a integerp)))
(definterface fn-k-none :class :ideal)
(definterface fn-k-elsewhere :class :program)
"""


def tree() -> Path:
    root = Path(tempfile.mkdtemp())
    (root / "books").mkdir()
    (root / "host").mkdir()
    (root / "books" / "payload-kinds.lisp").write_text(KINDS_BOOK)
    (root / "books" / "k.lisp").write_text(BOOK)
    (root / "host" / "interfaces.lisp").write_text(INTERFACES)
    return root


def form(text: str) -> list:
    return ledger.Reader(text).top_level()[0][0]


class KindsTests(unittest.TestCase):
    def setUp(self):
        self.root = tree()
        self.kinds = interface_kinds.entry_guard_kinds(self.root)
        self.defs = interface_kinds.definitions(self.root)

    def of(self, name):
        return interface_kinds.kinds_of(self.defs[name][1], self.kinds)

    def test_the_defconst_is_read(self):
        self.assertEqual(self.kinds, ["fn-payload-handle-p", "fn-cbor-octet-listp", "natp",
                                      "integerp", "stringp", "true-listp"])

    def test_single_formal_kind_conjuncts_in_formal_order(self):
        # (consp octets) is not a kind, (< n 10) has two arguments, and
        # (natp (car octets)) is not applied to a formal.
        self.assertEqual(self.of("fn-k-plain"),
                         [["octets", "fn-cbor-octet-listp"], ["n", "natp"], ["name", "stringp"]])

    def test_stobj_formals_carry_no_kind(self):
        self.assertEqual(self.of("fn-k-stobj"), [["n", "natp"]])

    def test_type_declarations_translate_to_recognizers(self):
        self.assertEqual(self.of("fn-k-types"),
                         [["a", "integerp"], ["b", "fn-cbor-octet-listp"]])

    def test_ties_keep_fn_di_sort_order(self):
        # fn-di-insert puts a check after every check at its own position, so
        # two kinds on one formal come out last conjunct first.
        self.assertEqual(self.of("fn-k-tie"), [["n", "natp"], ["n", "integerp"]])

    def test_definitions_inside_wrappers_are_found(self):
        self.assertEqual(self.of("fn-k-inner"), [["h", "fn-payload-handle-p"]])
        self.assertEqual(self.of("fn-k-none"), [])

    def test_a_wrong_declaration_is_a_disagreement_and_a_right_one_is_not(self):
        decls = interface_emit.declarations(self.root)
        problems = interface_kinds.disagreements(decls, self.defs, self.kinds)
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("fn-k-types declares :kinds ((a integerp)) but its guard "
                      "(books/k.lisp) gives ((a integerp) (b fn-cbor-octet-listp))", problems[0])

    def test_kinds_main_exit_codes(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(interface_emit.kinds_main([], self.root), 1)
            self.assertEqual(interface_emit.kinds_main(["fn-k-plain"], self.root), 0)
            self.assertEqual(interface_emit.kinds_main(["fn-k-elsewhere"], self.root), 1)
        text = out.getvalue()
        self.assertIn("4 declared, 3 defined in source; 1 disagreement(s)", text)
        self.assertIn("fn-k-plain (books/k.lisp) :kinds ((octets fn-cbor-octet-listp) "
                      "(n natp) (name stringp))", text)
        self.assertIn("fn-k-elsewhere: defined by no book or ACL2-mode host file", text)

    def test_a_fixed_declaration_has_no_disagreement(self):
        text = INTERFACES.replace(":kinds ((a integerp))",
                                  ":kinds ((a integerp) (b fn-cbor-octet-listp))")
        (self.root / "host" / "interfaces.lisp").write_text(text)
        decls = interface_emit.declarations(self.root)
        self.assertEqual(interface_kinds.disagreements(decls, self.defs, self.kinds), [])


if __name__ == "__main__":
    unittest.main()

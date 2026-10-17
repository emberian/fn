"""tools/interface_kinds.py: definterface's :class/:kinds from the source (item 68)."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tools import interface_kinds  # noqa: E402

KINDS = """(defconst *fn-entry-guard-kinds*
  '((fn-payload-handle-p . "h") (fn-cbor-octet-listp . "o") (natp . "n")
    (integerp . "i") (stringp . "s") (true-listp . "l")))
"""

BOOK = """(defun fn-k-a (x n state)
  (declare (xargs :guard (and (fn-cbor-octet-listp x) (natp n) (state-p state))
                  :stobjs state))
  (list x n state))
(defun fn-k-types (a b)
  (declare (type (unsigned-byte 8) a) (type string b))
  (declare (xargs :guard (natp a)))
  (list a b))
(defun fn-k-plain (x) x)
(defun fn-k-off (x)
  (declare (xargs :guard (natp x) :verify-guards nil))
  x)
(verify-guards fn-k-off)
(defun fn-k-later (x)
  (declare (xargs :guard (natp x) :verify-guards nil))
  x)
(defun fn-k-prog (x) (declare (xargs :mode :program)) x)
(defun fn-k-writer (x) (declare (xargs :guard (natp x) :verify-guards nil)) x)
(def-carried-writer fn-k-writer :profile fn-k-profile :via (fn-k-thm))
(defmacro octets-p (x) `(fn-cbor-octet-listp ,x))
(defun fn-k-macro (x) (declare (xargs :guard (octets-p x))) x)
(defun fn-k-if (x y) (declare (xargs :guard (if (stringp y) (natp x) 'nil))) (list x y))
(mutual-recursion
 (defun fn-k-even (x) (declare (xargs :verify-guards nil)) (if (zp x) t (fn-k-odd (1- x))))
 (defun fn-k-odd (x) (declare (xargs :verify-guards nil)) (if (zp x) nil (fn-k-even (1- x)))))
(verify-guards fn-k-even)
"""

EAGER = """(set-verify-guards-eagerness 2)
(defun fn-k-eager (x) x)
(set-verify-guards-eagerness 0)
(defun fn-k-lazy (x) (declare (xargs :guard t)) x)
(defun fn-k-lazy-t (x) (declare (xargs :guard t :verify-guards t)) x)
(program)
(defun fn-k-host (x) (declare (xargs :guard (natp x))) x)
(defun fn-k-host-logic (x) (declare (xargs :mode :logic :guard (natp x))) x)
(logic)
(defun fn-k-back (x) (declare (xargs :guard t :verify-guards t)) x)
"""


def source():
    return interface_kinds.read_source([("books/payload-kinds.lisp", KINDS),
                                        ("books/k.lisp", BOOK), ("books/e.lisp", EAGER)])


def decl(name, klass, kinds):
    return {"name": name, "class": klass, "kinds": kinds, "source": "host/interfaces.lisp",
            "line": 1}


class KindsTests(unittest.TestCase):
    def setUp(self):
        self.source = source()

    def kinds(self, name):
        return interface_kinds.kinds(self.source.definitions[name], self.source)

    def klass(self, name):
        return interface_kinds.symbol_class(self.source.definitions[name], self.source)

    def test_the_kinds_table_is_read_from_the_defconst(self):
        self.assertIn("fn-cbor-octet-listp", self.source.kinds)
        self.assertNotIn("state-p", self.source.kinds)

    def test_guard_kinds_in_position_order_stobj_excluded(self):
        self.assertEqual(self.kinds("fn-k-a"), [["x", "fn-cbor-octet-listp"], ["n", "natp"]])

    def test_type_declarations_come_first_and_ties_reverse(self):
        # conjuncts: (integerp a) range (stringp b) (natp a): a's two ties reversed
        self.assertEqual(self.kinds("fn-k-types"),
                         [["a", "natp"], ["a", "integerp"], ["b", "stringp"]])

    def test_if_nil_is_a_conjunction(self):
        self.assertEqual(self.kinds("fn-k-if"), [["x", "natp"], ["y", "stringp"]])

    def test_a_guard_macro_is_not_judged(self):
        with self.assertRaises(interface_kinds.CannotJudge):
            self.kinds("fn-k-macro")

    def test_classes(self):
        self.assertEqual(self.klass("fn-k-a"), "common-lisp-compliant")
        self.assertEqual(self.klass("fn-k-plain"), "ideal")
        self.assertEqual(self.klass("fn-k-off"), "common-lisp-compliant")  # verify-guards event
        self.assertEqual(self.klass("fn-k-later"), "ideal")
        # books/def-carried-writer.lisp verifies an :ideal writer's guards
        self.assertEqual(self.klass("fn-k-writer"), "common-lisp-compliant")
        self.assertEqual(self.klass("fn-k-prog"), "program")
        self.assertEqual(self.klass("fn-k-eager"), "common-lisp-compliant")
        self.assertEqual(self.klass("fn-k-lazy"), "ideal")  # eagerness 0
        self.assertEqual(self.klass("fn-k-lazy-t"), "common-lisp-compliant")
        self.assertEqual(self.klass("fn-k-host"), "program")  # (program) default
        self.assertEqual(self.klass("fn-k-host-logic"), "ideal")  # eagerness 0 still
        self.assertEqual(self.klass("fn-k-back"), "common-lisp-compliant")
        self.assertEqual(self.klass("fn-k-odd"), "common-lisp-compliant")  # its clique's event


class JudgeTests(unittest.TestCase):
    def test_agreement_is_silent_and_disagreements_are_worded(self):
        decls = [decl("fn-k-a", "common-lisp-compliant",
                      [["x", "fn-cbor-octet-listp"], ["n", "natp"]]),
                 decl("fn-k-plain", "common-lisp-compliant", []),
                 decl("fn-k-types", "common-lisp-compliant", [["b", "stringp"]]),
                 decl("fn-k-macro", "common-lisp-compliant", []),
                 decl("fn-no-such", "ideal", [])]
        problems, skipped = interface_kinds.judge(decls, source())
        self.assertEqual(skipped, 2)  # the macro guard, the missing definition
        self.assertEqual(len(problems), 2, problems)
        self.assertIn("fn-k-plain is :ideal (by its source, books/k.lisp:", problems[0])
        self.assertIn("declared :common-lisp-compliant", problems[0])
        self.assertIn("fn-k-types's guard kinds are ((a natp) (a integerp) (b stringp))",
                      problems[1])
        self.assertIn("declared ((b stringp))", problems[1])


if __name__ == "__main__":
    unittest.main()

"""tools/interface_emit.py: the definterface registry and its host-binding check."""
from __future__ import annotations

import tempfile
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import interface_emit  # noqa: E402

SOURCE = """(in-package "ACL2")
(include-book "../books/definterface")
(definterface fn-a :class :common-lisp-compliant :kinds ((octets fn-cbor-octet-listp))
  :keystones (fn-a-thm (fn-b-thm :via fn-b)) :root :extract)
(definterface fn-c :class :program :exempt ((frame "total scan")))
(definterface fn-d :class :common-lisp-compliant :direct "a stobj primitive")
(definterface create-fn-e :class :common-lisp-compliant :root :extract-extra)
"""


def tree(text: str) -> Path:
    root = Path(tempfile.mkdtemp())
    (root / "host").mkdir()
    (root / "host" / "interfaces.lisp").write_text(text)
    return root


def reading(**over) -> dict:
    base = {"dispatched": {"fn-c": {"host/native/io.lisp"}},
            "direct": {"fn-d": {"host/native/io.lisp"}},
            "defined": {"fn-a", "fn-c", "fn-d"}, "entries": 3}
    base.update(over)
    return base


class DeclarationTests(unittest.TestCase):
    def test_forms_parse(self):
        decls = interface_emit.declarations(tree(SOURCE))
        self.assertEqual([d["name"] for d in decls], ["fn-a", "fn-c", "fn-d", "create-fn-e"])
        a = decls[0]
        self.assertEqual(a["class"], "common-lisp-compliant")
        self.assertEqual(a["kinds"], [["octets", "fn-cbor-octet-listp"]])
        self.assertEqual(a["keystones"], [{"theorem": "fn-a-thm"},
                                          {"theorem": "fn-b-thm", "via": "fn-b"}])
        self.assertEqual(a["root"], "extract")

    def test_harness_tables(self):
        root = tree(SOURCE)
        self.assertEqual(interface_emit.entry_kind_exempt(root), {("fn-c", "frame"): "total scan"})
        self.assertEqual(interface_emit.entry_direct_allowed(root), {"fn-d": "a stobj primitive"})

    def test_roots_render_in_declaration_order(self):
        text = interface_emit.render_roots(interface_emit.declarations(tree(SOURCE)))
        self.assertIn('FN_EXTRACT_ROOTS_DECLARED="fn-a"\n', text)
        self.assertIn('FN_EXTRACT_EXTRA_DECLARED="create-fn-e"\n', text)

    def test_unknown_keyword_is_refused(self):
        with self.assertRaises(ValueError):
            interface_emit.declarations(tree('(definterface fn-a :class :program :guard t)\n'))


class HostBindingTests(unittest.TestCase):
    def problems(self, text=SOURCE, **over):
        decls = interface_emit.declarations(tree(text))
        return [p for p in interface_emit.findings(decls, reading(**over))
                if "is not what the declarations say" not in p]

    def test_bound(self):
        self.assertEqual(self.problems(), [])

    def test_stale_declaration(self):
        found = self.problems(dispatched={})
        self.assertTrue(any("fn-c is declared but the raw host never dispatches it" in p
                            for p in found), found)

    def test_stale_direct(self):
        found = self.problems(direct={})
        self.assertTrue(any("fn-d is declared :direct" in p for p in found), found)

    def test_undeclared_direct_application(self):
        found = self.problems(direct={"fn-d": {"x"}, "fn-z": {"host/native/io.lisp"}})
        self.assertTrue(any("applies fn-z directly" in p for p in found), found)

    def test_undefined_entry(self):
        found = self.problems(defined={"fn-c", "fn-d"})
        self.assertTrue(any("fn-a is defined by no book" in p for p in found), found)

    def test_undeclared_dispatched_entry(self):
        found = self.problems(dispatched={"fn-c": {"host/native/io.lisp"},
                                          "fn-z": {"host/native/owner.lisp"}})
        self.assertTrue(any("dispatches fn-z (host/native/owner.lisp) and no definterface"
                            in p for p in found), found)

    def test_duplicate(self):
        found = self.problems(SOURCE + "(definterface fn-c :class :program)\n")
        self.assertTrue(any("fn-c is declared twice" in p for p in found), found)


class GapTests(unittest.TestCase):
    def test_subsystem_prefix_then_file(self):
        self.assertEqual(interface_emit.subsystem("fn-owner-x", {"host/native/bp.lisp"}), "owner")
        self.assertEqual(interface_emit.subsystem("fn-q", {"host/native/bp-node.lisp"}), "bp")
        self.assertEqual(interface_emit.subsystem("fn-q", ()), "nntp/served")


if __name__ == "__main__":
    unittest.main()

"""tools/interface_emit.py: the definterface registry and its host-binding check."""
from __future__ import annotations

import tempfile
from pathlib import Path
import sys
import unittest
from unittest import mock

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

    def test_raw_scope_is_explicit_and_preserves_kind_checks(self):
        decls = interface_emit.declarations(tree(
            '(definterface fn-a :class :common-lisp-compliant :kinds ((n natp)) '
            ':raw-with (fn-a-proof))\n'
            '(definterface fn-b :class :common-lisp-compliant)\n'
            '(definterface fn-di-raw-with-problem :class :program '
            ':direct "Image-build declaration lint")\n'
            '(definterface fn-unrelated-helper :class :program :direct "other")\n'))
        rendered = interface_emit.render_raw_declarations(decls)
        self.assertIn('(definterface fn-a :class :common-lisp-compliant '
                      ':kinds ((n natp)) :raw-with (fn-a-proof))', rendered)
        self.assertNotIn('(definterface fn-b', rendered)
        self.assertIn('(definterface fn-di-raw-with-problem :class :program '
                      ':direct "Image-build declaration lint")', rendered)
        self.assertNotIn('(definterface fn-unrelated-helper', rendered)

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

    def test_raw_with_parses(self):
        decls = interface_emit.declarations(tree(
            '(definterface fn-a :class :common-lisp-compliant :raw-with (fn-a-open fn-a-statep))\n'))
        self.assertEqual(decls[0]["raw_with"], ["fn-a-open", "fn-a-statep"])
        self.assertEqual(interface_emit.declarations(tree(SOURCE))[0]["raw_with"], [])


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

    def raw_with_problems(self, declaration, book=""):
        # fn-r: a dispatched, defined entry; the book holds one non-local
        # theorem and one local one
        root = tree(SOURCE + declaration)
        (root / "books").mkdir()
        (root / "books" / "x.lisp").write_text(
            "(in-package \"ACL2\")\n(defthm fn-r-statep (implies (fn-r-relation s) "
            "(fn-r-okp s)))\n(local (defthm fn-r-local (equal x x)))\n" + book)
        decls = interface_emit.declarations(root)
        over = reading(dispatched={"fn-c": {"host/native/io.lisp"},
                                   "fn-r": {"host/native/owner.lisp"}},
                       defined={"fn-a", "fn-c", "fn-d", "fn-r"})
        return [p for p in interface_emit.findings(decls, over, root)
                if "is not what the declarations say" not in p]

    def test_raw_with_names_a_tree_theorem(self):
        self.assertEqual(self.raw_with_problems(
            "(definterface fn-r :class :common-lisp-compliant :raw-with (fn-r-statep))\n"), [])

    def test_raw_with_refuses_a_missing_or_local_theorem(self):
        found = self.raw_with_problems(
            "(definterface fn-r :class :common-lisp-compliant :raw-with (fn-r-statep fn-r-local))\n")
        self.assertTrue(any("fn-r :raw-with names fn-r-local, which no book defines" in p
                            for p in found), found)

    def test_raw_with_refuses_a_program_entry(self):
        found = self.raw_with_problems(
            "(definterface fn-r :class :program :raw-with (fn-r-statep))\n")
        self.assertTrue(any("fn-r is declared :raw-with but :class program" in p
                            for p in found), found)

    def test_registry_lists_the_raw_dispatched(self):
        root = tree("(definterface fn-a :class :common-lisp-compliant :raw-with (fn-a-thm))\n"
                    "(definterface fn-c :class :program)\n")
        import json
        doc = json.loads(interface_emit.render_registry(
            interface_emit.declarations(root), reading()))
        self.assertEqual(doc["raw_dispatched"], [{"name": "fn-a", "raw_with": ["fn-a-thm"]}])
        self.assertEqual(doc["coverage"]["raw_dispatched"], 1)
        self.assertEqual(doc["entries"][0]["raw_with"], ["fn-a-thm"])
        self.assertEqual(doc["entries"][1]["raw_with"], [])


class GapTests(unittest.TestCase):
    def test_subsystem_prefix_then_file(self):
        self.assertEqual(interface_emit.subsystem("fn-owner-x", {"host/native/bp.lisp"}), "owner")
        self.assertEqual(interface_emit.subsystem("fn-q", {"host/native/bp-node.lisp"}), "bp")
        self.assertEqual(interface_emit.subsystem("fn-q", ()), "nntp/served")


class LaptopRefusalTests(unittest.TestCase):
    """decision-keystones: `interface_emit --write` took minutes on the laptop."""

    def test_write_is_refused_off_a_farm_box_unless_overridden(self):
        from tools import acl2_slots
        with self.assertRaises(SystemExit) as refused:
            acl2_slots.refuse_on_laptop("tools/interface_emit.py --write", environ={},
                                        hostname="embers-laptop.local")
        self.assertIn("remote_check.sh auto", str(refused.exception))
        acl2_slots.refuse_on_laptop("x", environ={}, hostname="persvati")
        acl2_slots.refuse_on_laptop("x", environ={"FN_LAPTOP_OK": "1"},
                                    hostname="embers-laptop")
        from tools import interface_emit
        with mock.patch("socket.gethostname", return_value="embers-laptop"), \
                mock.patch.dict("os.environ", {"FN_LAPTOP_OK": ""}), \
                mock.patch.object(interface_emit, "declarations",
                                  side_effect=AssertionError("read the tree")):
            with self.assertRaises(SystemExit):
                interface_emit.main(["--write"])


if __name__ == "__main__":
    unittest.main()

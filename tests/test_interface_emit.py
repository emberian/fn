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

    def test_raw_with_carried_resolves_from_the_def_carried_row(self):
        book = ("(def-carried fn-r-carried :invariant fn-r-relation\n"
                "  :established ((fn-r-open fn-r-open-establishes))\n"
                "  :transitions ((fn-r fn-r-carries) (fn-s fn-s-carries))\n"
                "  :concludes ((fn-r-okp fn-r-statep)))\n"
                "(defthm fn-r-open-establishes (fn-r-relation (fn-r-open)))\n"
                "(defthm fn-r-carries (implies (fn-r-relation s) (fn-r-relation (fn-r s))))\n")
        self.assertEqual(self.raw_with_problems(
            "(definterface fn-r :class :common-lisp-compliant :raw-with (:carried fn-r-carried))\n",
            book), [])
        root = tree(SOURCE + "(definterface fn-r :class :common-lisp-compliant "
                    ":raw-with (:carried fn-r-carried))\n")
        (root / "books").mkdir()
        (root / "books" / "x.lisp").write_text("(in-package \"ACL2\")\n" + book)
        decl = interface_emit.declarations(root)[-1]
        self.assertEqual(decl["raw_with_carried"], "fn-r-carried")
        # only generated names: the declared theorems are hints, never resolved
        self.assertEqual(decl["raw_with"], ["fn-r-carried-fn-r-carries",
                                            "fn-r-carried-fn-r-okp-bridge"])
        rendered = interface_emit.render_raw_declarations([decl])
        self.assertIn(":raw-with (:carried fn-r-carried)", rendered)

    def test_raw_with_carried_refuses_a_missing_row_or_transition(self):
        found = self.raw_with_problems(
            "(definterface fn-r :class :common-lisp-compliant :raw-with (:carried fn-r-carried))\n")
        self.assertTrue(any("fn-r :raw-with (:carried fn-r-carried) resolves to no theorems" in p
                            for p in found), found)
        found = self.raw_with_problems(
            "(definterface fn-r :class :common-lisp-compliant :raw-with (:carried fn-r-carried))\n",
            "(def-carried fn-r-carried :invariant fn-r-relation "
            ":established ((fn-r-open fn-r-open-establishes)) :transitions ((fn-s fn-s-carries)))\n")
        self.assertTrue(any("resolves to no theorems" in p for p in found), found)

    def test_produced_open_is_never_reached_by_the_raw_host(self):
        # def-carried :produced: the open's premises hold only at its
        # producers' outputs, so the raw host may neither dispatch it nor
        # apply it directly (r25-F2)
        book = ("(def-carried fn-p-carried :invariant fn-p-relation\n"
                "  :established ((fn-p-open fn-p-open-establishes :hyps ((posp x))\n"
                "                 :produced ((fn-p-make fn-p-make-pos)) :witness (1 nil)))\n"
                "  :transitions ((fn-s fn-s-carries)))\n")
        root = tree(SOURCE)
        (root / "books").mkdir()
        (root / "books" / "x.lisp").write_text("(in-package \"ACL2\")\n" + book)
        self.assertEqual(interface_emit.carried_rows(root)["fn-p-carried"]["produced"],
                         ["fn-p-open"])
        decls = interface_emit.declarations(root)
        for kind, word in (("dispatched", "dispatches"), ("direct", "applies")):
            over = reading(**{kind: dict(reading()[kind], **{"fn-p-open": {"host/native/owner.lisp"}})})
            found = [p for p in interface_emit.findings(decls, over, root)
                     if "is not what the declarations say" not in p]
            self.assertTrue(any("the raw host {} fn-p-open".format(word) in p
                                and "fn-p-carried" in p for p in found), found)
        clean = [p for p in interface_emit.findings(decls, reading(), root)
                 if "is not what the declarations say" not in p]
        self.assertFalse(any("fn-p-open" in p for p in clean), clean)

    def test_raw_with_carried_refuses_malformed_forms(self):
        for form in ("(:carried)", "(:carried fn-r-carried extra)"):
            found = self.raw_with_problems(
                "(definterface fn-r :class :common-lisp-compliant :raw-with %s)\n" % form,
                "(def-carried fn-r-carried :invariant fn-r-relation "
                ":established ((fn-r-open fn-r-open-establishes)) "
                ":transitions ((fn-r fn-r-carries)))\n")
            self.assertTrue(any("resolves to no theorems" in p for p in found), (form, found))

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
        self.assertEqual(doc["raw_dispatched"], [{"name": "fn-a", "raw_with": ["fn-a-thm"], "raw_with_carried": None}])
        self.assertEqual(doc["coverage"]["raw_dispatched"], 1)
        self.assertEqual(doc["entries"][0]["raw_with"], ["fn-a-thm"])
        self.assertEqual(doc["entries"][1]["raw_with"], [])


class HostReadingTreeTests(unittest.TestCase):
    """Structural generation agrees without running theorem detectors."""

    def test_lazy_reading_matches_eager_and_tracks_source_changes(self):
        from tools import ledger, harness_check
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "books").mkdir()
            (root / "host/native").mkdir(parents=True)
            (root / "Makefile").write_text("ACL2_BOOKS = books/a\n")
            book = root / "books/a.lisp"
            book.write_text('(defun fn-a (x) x)\n(defthm fn-a-id (equal (fn-a x) x))\n')
            (root / "host/interfaces.lisp").write_text(
                '(definterface fn-a :class :program :root :extract)\n'
                '(definterface fn-b :class :program :direct "primitive")\n')
            (root / "host/build.lisp").write_text(
                '(defttag :raw)\n(progn! (set-raw-mode t) (load "host/native/io.lisp"))\n')
            host = root / "host/native/io.lisp"
            host.write_text("(defun fnn-use (x) (fnn-call 'fn-a x) (fn-b x))\n")
            with mock.patch.object(ledger, "ROOT", root), \
                    mock.patch.object(harness_check, "ROOT", root), \
                    mock.patch.object(ledger, "_TREE_CACHE", None), \
                    mock.patch.dict("os.environ", {"FN_LEDGER_TREE_CACHE": "0"}):
                genuine_load = ledger.load_tree
                snapshots = []
                for changed in (False, True):
                    if changed:
                        book.write_text('(defun fn-b (x) x)\n')
                        host.write_text("(defun fnn-use (x) (fnn-call 'fn-missing x) (fn-b x))\n")
                    ledger._TREE_CACHE = None
                    eager = genuine_load()
                    with mock.patch.object(ledger, "load_tree", return_value=eager):
                        expected = interface_emit.host_reading(root)
                    ledger._TREE_CACHE = None
                    with mock.patch.object(ledger.Tree, "_all_suspects",
                                           side_effect=AssertionError("unneeded analysis")), \
                            mock.patch.object(ledger, "load_tree", wraps=genuine_load) as loader:
                        actual = interface_emit.host_reading(root)
                        loader.assert_called_once_with(lazy=True)
                        self.assertIsNone(ledger._TREE_CACHE[1]._suspects)
                    self.assertEqual(actual, expected)
                    decls = interface_emit.declarations(root)
                    self.assertEqual(interface_emit.render_registry(decls, actual),
                                     interface_emit.render_registry(decls, expected))
                    self.assertEqual(interface_emit.findings(decls, actual, root),
                                     interface_emit.findings(decls, expected, root))
                    snapshots.append(actual)
                    # Full theorem analysis still runs when a caller asks for it.
                    lazy = ledger._TREE_CACHE[1]
                    with mock.patch.object(lazy, "_all_suspects", wraps=lazy._all_suspects) as analysis:
                        self.assertEqual(lazy.suspects, eager.suspects)
                        analysis.assert_called_once_with()
                self.assertNotEqual(snapshots[0], snapshots[1])
                self.assertIn("fn-missing", snapshots[1]["dispatched"])
                self.assertNotIn("fn-a", snapshots[1]["defined"])
                self.assertIn("fn-b", snapshots[1]["direct"])
                problems = interface_emit.findings(decls, snapshots[1], root)
                self.assertTrue(any("fn-a is defined by no book" in p for p in problems))
                self.assertTrue(any("dispatches fn-missing" in p for p in problems))


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

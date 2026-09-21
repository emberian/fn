"""Unit checks for the citation check (`tools/cite_check.py`).

Two halves.  The positive cases are the finding the tool exists for: the
`books/stx-transit.lisp` shape, a citation in a `books/` source of a file that
has never existed, which must come out PHANTOM and LOAD-BEARING; and the
`books/store-node-resolution-traces.lisp` shape, a citation of a file some
commit once held, which must come out DRIFT, because the repair for the two
is different -- a phantom has nothing to point at and a drift has a new path.

The negative cases are each a false positive a cruder sweep produced on this
tree, and each one is a rule in `benign` or `resolves`: an ACL2 community book
reached with `:dir :system`, a placeholder in a prose example, the Makefile's
extensionless spelling of a book, a `.cert` the run produces, a module
attribute, a hyphenated line wrap, a slash in running prose, and the fixture
data of the Python unit tests -- whose file this one is, so its own fake paths
below are covered by the same rule.
"""

import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "cite_check", Path(__file__).resolve().parents[1] / "tools" / "cite_check.py"
)
cite_check = importlib.util.module_from_spec(SPEC)
sys.modules["cite_check"] = cite_check
SPEC.loader.exec_module(cite_check)


class ScanTests(unittest.TestCase):
    """`scan` over a tree written into a temporary directory."""

    def scan(self, sources: dict[str, str], history: set[str] = frozenset()):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        root = Path(self.directory.name)
        for name, text in sources.items():
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            (root / name).write_text(text)
        original, cite_check.ROOT = cite_check.ROOT, root
        self.addCleanup(setattr, cite_check, "ROOT", original)
        return cite_check.scan(set(sources), set(history), list(sources))

    def only(self, sources, history=frozenset()):
        found = self.scan(sources, history)
        raised = [f for f in found if f.klass in cite_check.RAISED]
        self.assertEqual(len(raised), 1, [str(f) for f in found])
        return raised[0]

    def silent(self, sources, history=frozenset()):
        found = self.scan(sources, history)
        self.assertEqual([str(f) for f in found if f.klass in cite_check.RAISED], [])
        return found

    # -- the findings -----------------------------------------------------

    def test_a_book_citing_a_file_that_never_existed_is_a_load_bearing_phantom(self):
        finding = self.only({"books/lace.lisp":
                             '; `books/transit.lisp\' proves the gate.\n'})
        self.assertEqual((finding.klass, finding.tier),
                         ("phantom", "load-bearing"))
        self.assertEqual(finding.token, "books/transit.lisp")

    def test_a_test_book_is_load_bearing_too(self):
        finding = self.only({"tests/acl2/lace-tests.lisp":
                             '; `tests/acl2/gone-tests.lisp\' exhibits a run.\n'})
        self.assertEqual(finding.tier, "load-bearing")

    def test_a_citation_with_history_is_drift_not_phantom(self):
        finding = self.only({"books/assumptions.lisp": "; books/folded.lisp\n"},
                            history={"books/folded.lisp"})
        self.assertEqual(finding.klass, "drift")

    def test_history_of_the_book_root_counts_as_history_of_the_source(self):
        finding = self.only({"books/assumptions.lisp": '; `books/folded\'\n'},
                            history={"books/folded.lisp"})
        self.assertEqual(finding.klass, "drift")

    def test_a_spec_and_a_planning_file_are_separated_from_a_source(self):
        found = self.scan({"specs/design.md": "`books/later.lisp`\n",
                           "planning/lanes/HANDOFF.md": "`books/later.lisp`\n",
                           "books/real.lisp": "; books/later.lisp\n"})
        self.assertEqual({f.citer: f.tier for f in found},
                         {"specs/design.md": "spec",
                          "planning/lanes/HANDOFF.md": "planning",
                          "books/real.lisp": "load-bearing"})

    def test_the_forward_hint_is_set_by_the_line_not_the_tier(self):
        found = self.scan({"specs/design.md":
                           "The proposed `tools/run_x.py` will exist.\n"
                           "`tools/run_y.py` computes the charge.\n"})
        self.assertEqual({f.token: f.forward for f in found},
                         {"tools/run_x.py": True, "tools/run_y.py": False})

    def test_a_disclosed_phantom_is_annotated_and_not_raised(self):
        found = self.silent({"books/lace.lisp":
                             "; Until today this said `books/transit.lisp'\n"
                             "; names the composition.  IT HAS NEVER EXISTED,\n"
                             "; so the observation was assumed.\n"})
        self.assertEqual({f.klass for f in found}, {"annotated"})

    def test_a_disclosed_drift_names_where_the_file_went(self):
        found = self.silent({"books/assumptions.lisp":
                             "; books/folded.lisp -- that book was folded into\n"
                             "; books/kept.lisp by 8209f27.\n",
                             "books/kept.lisp": '(in-package "ACL2")\n'},
                            history={"books/folded.lisp"})
        self.assertEqual({f.klass for f in found}, {"annotated"})

    def test_disclosure_does_not_reach_an_unrelated_citation(self):
        finding = self.only({"books/lace.lisp":
                             "; `books/gone.lisp' proves it.\n"
                             + "; filler\n" * 9
                             + "; `books/other.lisp' has never existed.\n"})
        self.assertEqual((finding.token, finding.klass),
                         ("books/gone.lisp", "phantom"))

    # -- the false positives ----------------------------------------------

    def test_a_system_include_book_is_not_a_repository_path(self):
        found = self.silent({"books/real.lisp":
                             '(include-book "tools/flag" :dir :system)\n'})
        self.assertEqual([f.klass for f in found], ["system"])

    def test_our_books_directory_is_flat_so_a_nested_books_path_is_acl2s(self):
        found = self.silent({"books/real.lisp":
                             "; books/arithmetic/top.lisp states nothing.\n"})
        self.assertEqual([f.klass for f in found], ["system"])

    def test_a_placeholder_in_a_prose_example_is_not_a_citation(self):
        found = self.silent({"planning/lanes/LANEDUMP.md":
                             '(ld "books/X.lisp")\n'
                             "every `tests/acl2/*-teeth-tests.lisp`\n"
                             "`books/<root>.lisp`\n"})
        self.assertEqual({f.klass for f in found}, {"placeholder"})

    def test_an_extensionless_book_root_resolves_against_the_lisp_file(self):
        self.silent({"Makefile": "ACL2_BOOKS = books/wire\n",
                     "books/wire.lisp": "(in-package \"ACL2\")\n"})

    def test_a_produced_file_resolves_against_the_source_that_produces_it(self):
        self.silent({"planning/lanes/HANDOFF.md": "`books/wire.cert` was kept\n",
                     "books/wire.lisp": "(in-package \"ACL2\")\n"})

    def test_a_module_attribute_resolves_against_the_module(self):
        self.silent({"planning/lanes/HANDOFF.md": "`tools/scheduler.plan_from`\n",
                     "tools/scheduler.py": "def plan_from(): pass\n"})

    def test_a_hyphenated_line_wrap_is_not_a_citation(self):
        found = self.silent({"planning/lanes/HANDOFF.md":
                             "the octet rules. `books/anchor-\ninvariants.lisp`\n"})
        self.assertEqual([f.klass for f in found], ["wrapped"])

    def test_an_undelimited_slash_in_running_prose_is_not_a_citation(self):
        found = self.silent({"specs/container.md":
                             "D08 is the fix and is host/grammar work.\n"})
        self.assertEqual([f.klass for f in found], ["prose"])

    def test_a_directory_citation_keeps_its_own_name(self):
        # A trailing slash once ate the basename and every cited directory
        # read as a one-character placeholder, which hid a load-bearing one.
        finding = self.only({"tests/acl2/bundle-tests.lisp":
                             "; `tests/vectors/golden/' holds the octets.\n"})
        self.assertEqual((finding.token, finding.tier),
                         ("tests/vectors/golden/", "load-bearing"))

    def test_a_delimited_extensionless_citation_is_still_read(self):
        finding = self.only({"specs/design.md": "certifies `books/nntp-probe`\n"})
        self.assertEqual(finding.token, "books/nntp-probe")

    def test_unit_test_fixture_data_is_classed_apart_from_its_comments(self):
        found = self.scan({"tests/test_certify_runner.py":
                           'ORDER = ["books/leaf-a", "books/base"]\n'
                           "# books/gone.lisp was folded away\n"})
        self.assertEqual({f.token: f.klass for f in found},
                         {"books/leaf-a": "fixture", "books/base": "fixture",
                          "books/gone.lisp": "phantom"})

    def test_an_evidence_record_names_what_was_certified_then(self):
        found = self.silent({"tests/evidence/2026-09-18-store.json":
                             '{"books/folded.lisp": "deadbeef"}\n'},
                            history={"books/folded.lisp"})
        self.assertEqual([(f.klass, f.tier) for f in found],
                         [("record", "record")])


class StrictTests(unittest.TestCase):
    """`--strict` is the gate a tree with no load-bearing finding can adopt."""

    def test_the_real_tree_reports_and_does_not_fail(self):
        self.assertEqual(cite_check.main(["--summary"]), 0)


if __name__ == "__main__":
    unittest.main()

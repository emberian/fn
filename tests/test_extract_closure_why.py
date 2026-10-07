"""tools/extract/closure_why.py and host_tokens.file_tokens on synthetic data."""
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools" / "extract"))

import closure_why  # noqa: E402
import core_build  # noqa: E402
import host_tokens  # noqa: E402

EDGES = """#root\traw:ACL2::FN-A
#root\traw:ACL2::FN-B
raw:ACL2::FN-A\traw:ACL2::FN-C star1:ACL2::FN-A
star1:ACL2::FN-A\traw:ACL2::THROW-RAW-EV-FNCALL
raw:ACL2::FN-C\traw:ACL2::BINARY-APPEND
raw:ACL2::FN-B\traw:ACL2::FN-C
raw:ACL2::THROW-RAW-EV-FNCALL\traw:ACL2::EV-FNCALL-MSG
raw:ACL2::EV-FNCALL-MSG\traw:ACL2::EV-W
raw:ACL2::EV-W\t
raw:ACL2::BINARY-APPEND\t
star1:ACL2::FN-B\t
"""


class ClosureWhy(unittest.TestCase):
    def analyse(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "edges.tsv").write_text(EDGES)
            roots, graph = closure_why.read_edges(Path(d) / "edges.tsv")
        return closure_why.analyse(roots, graph, set(closure_why.EVALUATOR), None)

    def test_the_boundary_edge_and_its_path_are_named(self):
        r = self.analyse()
        self.assertEqual(r["targets_present"], ["raw:ACL2::EV-W"])
        self.assertEqual([(b["caller"], b["callee"]) for b in r["boundary"]],
                         [("star1:ACL2::FN-A", "raw:ACL2::THROW-RAW-EV-FNCALL")])
        self.assertEqual(r["boundary"][0]["path"],
                         ["raw:ACL2::THROW-RAW-EV-FNCALL", "raw:ACL2::EV-FNCALL-MSG", "raw:ACL2::EV-W"])

    def test_only_roots_that_reach_a_target_are_listed(self):
        r = self.analyse()
        self.assertEqual([row["root"] for row in r["roots"]], ["raw:ACL2::FN-A", "star1:ACL2::FN-A"])

    def test_cutting_the_boundary_drops_what_only_it_reaches(self):
        r = self.analyse()
        self.assertEqual(r["reachable"] - r["reachable_without_boundary"], 3)


class HostTokens(unittest.TestCase):
    def test_a_variable_named_like_an_acl2_function_is_not_a_root(self):
        toks = host_tokens.file_tokens(
            "(defun fnn-x (ev ordinal) (fnn-call 'fn-his-row-begin ev)"
            " (flet ((fail (fmt &rest a) (format nil fmt))) (arity 'f w))"
            " (let ((always 1)) always) (ld-fn x) '(fn-a b) (<= 0 n *default-step-limit*))")
        self.assertNotIn("EV", toks)
        self.assertNotIn("FMT", toks)
        self.assertNotIn("ALWAYS", toks)
        for applied in ("ARITY", "LD-FN", "FNN-CALL", "F"):
            self.assertIn(applied, toks)
        for own in ("FN-HIS-ROW-BEGIN", "FN-A", "FNN-X", "*DEFAULT-STEP-LIMIT*"):
            self.assertIn(own, toks)

    def test_an_unreadable_file_keeps_every_word(self):
        toks = host_tokens.file_tokens("(defun fnn-x (ev) (car ev)")
        self.assertIn("EV", toks)


class ImageOnlyHost(unittest.TestCase):
    """The product leaves out what only an ACL2 image can run (core_build.IMAGE_ONLY_*)."""

    def test_each_image_only_load_is_a_real_load_of_the_image_build(self):
        block = core_build.raw_block(ROOT)
        for rel in core_build.IMAGE_ONLY_LOADS:
            self.assertEqual(block.count('(load "%s")' % rel), 1, rel)

    def test_the_product_loads_none_of_them_and_sets_no_acl2_banner(self):
        for build in ("host/native/build.lisp", "host/native/build-dtn.lisp"):
            files = core_build.host_files(ROOT, build)
            self.assertFalse(set(files) & set(core_build.IMAGE_ONLY_LOADS), build)
            body = core_build.product_block(ROOT, build)
            for form in core_build.IMAGE_ONLY_FORMS:
                self.assertNotIn(form, body)


class Check(unittest.TestCase):
    def run_check(self, edges):
        import contextlib, io
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "edges.tsv").write_text(edges)
            err = io.StringIO()
            with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
                rc = closure_why.main([d, "--check"])
        return rc, err.getvalue()

    def test_a_reachable_evaluator_is_refused_with_its_path(self):
        rc, err = self.run_check(EDGES)
        self.assertEqual(rc, 1)
        self.assertIn("raw:ACL2::EV-W", err)

    def test_an_unreachable_evaluator_unit_passes(self):
        cut = EDGES.replace("star1:ACL2::FN-A\traw:ACL2::THROW-RAW-EV-FNCALL", "star1:ACL2::FN-A\t")
        self.assertEqual(self.run_check(cut)[0], 0)


class BannedPrefix(unittest.TestCase):
    """RP-1: no unit of the developer-only book (FN-DEVAL-...) is in the closure."""
    def run_check(self, edges):
        return Check.run_check(self, edges)

    def with_deval(self, caller):
        cut = EDGES.replace("star1:ACL2::FN-A\traw:ACL2::THROW-RAW-EV-FNCALL", "star1:ACL2::FN-A\t")
        return cut.replace("raw:ACL2::FN-C\traw:ACL2::BINARY-APPEND",
                           "raw:ACL2::FN-C\traw:ACL2::BINARY-APPEND " + caller) \
            + "raw:ACL2::FN-DEVAL-ADMIT\traw:ACL2::BINARY-APPEND\n" \
            + "star1:ACL2::FN-DEVAL-ADMIT\t\n"

    def test_the_prefix_names_the_units_of_the_developer_book_only(self):
        graph = {"raw:ACL2::FN-DEVAL-ADMIT": [], "star1:ACL2::FN-DEVAL-ADMIT": [],
                 "raw:ACL2::FN-DEVAL": [], "raw:ACL2::FN-DEVALUE": [], "raw:ACL2::FNN-DEV-ADMIT": [],
                 "raw:ACL2::FN-OLOG-DEVAL-LINE": [], "table:ACL2::FN-DEVAL-X": []}
        self.assertEqual(closure_why.banned_by_prefix(graph),
                         ["raw:ACL2::FN-DEVAL-ADMIT", "star1:ACL2::FN-DEVAL-ADMIT",
                          "table:ACL2::FN-DEVAL-X"])
        self.assertEqual(closure_why.BANNED_PREFIXES, ("FN-DEVAL-",))

    def test_a_reachable_developer_unit_is_refused_with_its_path(self):
        rc, err = self.run_check(self.with_deval("raw:ACL2::FN-DEVAL-ADMIT"))
        self.assertEqual(rc, 1)
        self.assertIn("raw:ACL2::FN-DEVAL-ADMIT", err)

    def test_the_same_graph_without_the_edge_passes(self):
        # the unit is in the graph, no root reaches it: not in the served program
        self.assertEqual(self.run_check(self.with_deval(""))[0], 0)

    def test_mutation_without_the_prefix_rule_the_reachable_unit_passes(self):
        # labelled mutation: the rule applied by exact unit ids only (the evaluator list) lets it by
        saved = closure_why.BANNED_PREFIXES
        try:
            closure_why.BANNED_PREFIXES = ("NO-SUCH-PREFIX-",)
            self.assertEqual(self.run_check(self.with_deval("raw:ACL2::FN-DEVAL-ADMIT"))[0], 0)
        finally:
            closure_why.BANNED_PREFIXES = saved


# A table-reading unit, and a snapshot as core-export.lisp prints it (row keys of every printed shape).
TABLE_EDGES = EDGES.replace("raw:ACL2::FN-C\traw:ACL2::BINARY-APPEND",
                            "raw:ACL2::FN-C\traw:ACL2::BINARY-APPEND table:ACL2::ACL2-DEFAULTS-TABLE table:FN-X::T2")
SNAPSHOT = """(IN-PACKAGE "ACL2")
(XL-SET-WORLD-SNAPSHOT '((FN-A (GUARD . T))
 (FN-CORE-TABLE-DIGESTS (TABLE-ALIST (FN-INTERFACES (FN-A 1 2) (|odd )key| 3))
   (FN-RAW-DISPATCH-VERDICTS (\"a )string\" 4) (#\\) 5))
   (ACL2-DEFAULTS-TABLE (:DEFUN-MODE 6))
   (FN-X::T2)))
 (ACL2-DEFAULTS-TABLE (TABLE-ALIST (:DEFUN-MODE . :LOGIC)))))
""".replace('\\"', '"')


class CheckTables(unittest.TestCase):
    """X3's one discovery: the snapshot carries exactly the tables the emitted forms and the install path read."""

    def run_check(self, edges, snapshot):
        import contextlib, io
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "edges.tsv").write_text(edges)
            (Path(d) / "core-world.lisp").write_text(snapshot, encoding="latin-1")
            err = io.StringIO()
            with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
                rc = closure_why.main([d, "--check-tables"])
        return rc, err.getvalue()

    def test_snapshot_names_are_read_past_every_row_shape(self):
        self.assertEqual(closure_why.snapshot_tables(SNAPSHOT),
                         ["ACL2::FN-INTERFACES", "ACL2::FN-RAW-DISPATCH-VERDICTS",
                          "ACL2::ACL2-DEFAULTS-TABLE", "FN-X::T2"])

    def test_agreeing_tables_pass(self):
        self.assertEqual(self.run_check(TABLE_EDGES, SNAPSHOT), (0, ""))

    def test_a_table_read_but_not_carried_is_refused_by_name(self):
        rc, err = self.run_check(TABLE_EDGES, SNAPSHOT.replace("   (FN-X::T2)", ""))
        self.assertEqual(rc, 1)
        self.assertIn("table FN-X::T2 is read by an emitted form but the snapshot does not carry it", err)

    def test_a_dropped_install_table_is_refused_by_name(self):
        rc, err = self.run_check(TABLE_EDGES, SNAPSHOT.replace("(FN-INTERFACES (FN-A 1 2) (|odd )key| 3))", ""))
        self.assertEqual(rc, 1)
        self.assertIn("table ACL2::FN-INTERFACES is read", err)

    def test_a_table_carried_but_read_by_nothing_is_refused_by_name(self):
        rc, err = self.run_check(TABLE_EDGES.replace(" table:FN-X::T2", ""), SNAPSHOT)
        self.assertEqual(rc, 1)
        self.assertIn("table FN-X::T2 is carried by the snapshot but no emitted form", err)

    def test_a_table_unit_in_defs_is_refused_by_name(self):
        rc, err = self.run_check(TABLE_EDGES + "table:ACL2::ACL2-DEFAULTS-TABLE\t\n", SNAPSHOT)
        self.assertEqual(rc, 1)
        self.assertIn("table:ACL2::ACL2-DEFAULTS-TABLE is a defs.lisp unit", err)

    def test_two_manifests_are_refused(self):
        with self.assertRaises(ValueError):
            closure_why.snapshot_tables(SNAPSHOT + "(FN-CORE-TABLE-DIGESTS (TABLE-ALIST))")


if __name__ == "__main__":
    unittest.main()

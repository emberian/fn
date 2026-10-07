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


if __name__ == "__main__":
    unittest.main()

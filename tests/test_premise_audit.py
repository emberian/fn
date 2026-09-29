"""tools/premise_audit.py: the reader's decisions on small forms, and the
classification on a stub graph (no tree read: the whole-tree run is the
box's)."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "tools"))

import premise_audit  # noqa: E402
import reach_check  # noqa: E402


class Forms(unittest.TestCase):
    def test_conjuncts_unfold_and(self):
        tree = reach_check.read_sexp("(and (p x) (and (q y) (r z)))")
        heads = sorted(t[0] for t in premise_audit.conjuncts(tree))
        self.assertEqual(heads, ["p", "q", "r"])

    def test_predicate_application_forms(self):
        app = premise_audit.predicate_application
        self.assertEqual(app(reach_check.read_sexp("(fn-inv s)")), ("fn-inv", "s"))
        self.assertEqual(app(reach_check.read_sexp("(equal (fn-inv s) t)")), ("fn-inv", "s"))
        self.assertEqual(app(reach_check.read_sexp("(equal t (fn-inv s))")), ("fn-inv", "s"))
        self.assertIsNone(app(reach_check.read_sexp("(not (fn-inv s))")))
        self.assertIsNone(app(reach_check.read_sexp("(equal (f s) (g s))")))
        self.assertIsNone(app("s"))


class StubGraph:
    """The three theorems the docstring names: a preservation, an
    establishment by the open (hosted), and a consumer that assumes R."""

    def __init__(self, hosted_open=True):
        self.book_defs = {"fn-inv": 1, "fn-step": 1, "fn-open": 1, "fn-serve": 1,
                          "fn-other": 1, "fn-model-open": 1}
        self.books = []
        self.stobj_names = {"state"}
        self.reachable = {"fn-step", "fn-serve"} | ({"fn-open"} if hosted_open else set())


class Classification(unittest.TestCase):
    forms = {
        "fn-inv-preserved": ("books/a.lisp", "(defthm fn-inv-preserved (implies (fn-inv s) (fn-inv (fn-step s))))"),
        "fn-inv-of-open": ("books/a.lisp", "(defthm fn-inv-of-open (fn-inv (fn-open x)))"),
        "fn-serve-ok": ("books/b.lisp", "(defthm fn-serve-ok (implies (fn-inv s) (equal (fn-serve s) :ok)))"),
        "fn-other-model": ("books/b.lisp", "(defthm fn-other-model (implies (fn-other s) (equal (fn-serve s) :ok)))"),
        "fn-other-of-model-open": ("books/b.lisp", "(defthm fn-other-of-model-open (fn-other (fn-model-open x)))"),
    }

    def audit(self, hosted_open=True):
        graph = StubGraph(hosted_open)
        original = (reach_check.theorem_forms, reach_check.record_definitions,
                    reach_check.Subject.hosted)
        reach_check.theorem_forms = lambda paths: dict(self.forms)
        reach_check.record_definitions = lambda paths: {}
        reach_check.Subject.hosted = lambda self, graph: bool(set(self.functions) & graph.reachable)
        try:
            return premise_audit.Audit(graph)
        finally:
            (reach_check.theorem_forms, reach_check.record_definitions,
             reach_check.Subject.hosted) = original

    def test_statement_opens_binders(self):
        hyps, conclusion = premise_audit.statement(
            "(defthm fn-inv-at-install (let* ((oc (fn-install r)) (o (fn-owner oc)))"
            " (implies (and (not (equal oc :fault)) (fn-idlep o)) (fn-inv o s))))")
        self.assertEqual(conclusion, ["fn-inv", ["fn-owner", ["fn-install", "r"]], "s"])
        self.assertEqual(hyps, [["and", ["not", ["equal", ["fn-install", "r"], ":fault"]],
                                 ["fn-idlep", ["fn-owner", ["fn-install", "r"]]]]])
        hyps, conclusion = premise_audit.statement(
            "(defthm two (mv-let (a b) (fn-split x) (implies (fn-okp a) (fn-inv b))))")
        self.assertEqual(hyps, [["fn-okp", ["mv-nth", "0", ["fn-split", "x"]]]])
        self.assertEqual(conclusion, ["fn-inv", ["mv-nth", "1", ["fn-split", "x"]]])
        self.assertEqual(premise_audit.statement("(defthm plain (implies (p x) (q x)))"),
                         ([["p", "x"]], ["q", "x"]))

    def test_hosted_establishment_clears_the_premise(self):
        audit = self.audit(hosted_open=True)
        premises = audit.premises()
        self.assertEqual(premises["fn-inv"]["class"], premise_audit.HOSTED)
        self.assertEqual(premises["fn-inv"]["establishments"], ["fn-inv-of-open"])
        self.assertEqual(premises["fn-inv"]["preservations"], ["fn-inv-preserved"])
        self.assertNotIn("fn-inv", audit.findings())

    def test_preserved_only_when_the_open_is_not_hosted(self):
        audit = self.audit(hosted_open=False)
        self.assertEqual(audit.premises()["fn-inv"]["class"], premise_audit.OFF_HOST)
        self.assertIn("fn-inv", audit.findings())

    def test_model_establishment_is_off_the_host_path(self):
        audit = self.audit()
        row = audit.premises()["fn-other"]
        self.assertEqual(row["class"], premise_audit.OFF_HOST)
        self.assertEqual(row["unhosted_establishments"], ["fn-other-of-model-open"])
        self.assertEqual(row["theorems"], [("fn-other-model", "books/b.lisp")])

    def test_summary_counts(self):
        audit = self.audit(hosted_open=False)
        line = premise_audit.summary_line(audit.findings(), audit.premises(), {"accepted": {}})
        # Three theorems assume a finding's premise at a hosted entry: the
        # preservation `(implies (fn-inv s) (fn-inv (fn-step s)))' assumes
        # fn-inv at the hosted step too, as it should (the step is entered
        # with the premise the open never established).
        self.assertIn("2 premises at hosted entries, 2 unestablished (3 theorems)", line)
        self.assertIn("2 established off the host path", line)


if __name__ == "__main__":
    unittest.main()

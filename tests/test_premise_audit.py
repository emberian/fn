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


class LocalLemmas(unittest.TestCase):
    """A theorem proved inside (local ...) is a book-internal step: its
    hypotheses are no host premise (bpfj-candidate-sound, 2026-10-08)."""

    def test_local_theorems_are_named(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            book = pathlib.Path(d) / "b.lisp"
            book.write_text('(in-package "ACL2")\n'
                            '(local (defthm bpfj-candidate-sound (implies (fn-c x) (fn-ok (fn-c x)))))\n'
                            '(encapsulate () (local\n  (defthmd Inner-Step (implies (fn-inv s) (fn-ok s)))))\n'
                            '(defthm exported (implies (fn-inv s) (fn-ok s)))\n'
                            '; (local (defthm in-a-comment t))\n')
            got = premise_audit.local_theorems([book])
        self.assertIn("bpfj-candidate-sound", got)
        self.assertIn("inner-step", got)
        self.assertNotIn("exported", got)
        self.assertNotIn("in-a-comment", got)


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


def _defs(**forms):
    return {name: ("books/g.lisp", reach_check.read_sexp(text)) for name, text in forms.items()}


COMPLIANT = {"class": "common-lisp-compliant", "raw_with": [], "raw_guarded": None,
             "applied_directly_in": []}


class GuardEstablished(unittest.TestCase):
    """PREMISE-CHECKER-GUARD-ESTABLISHED: a premise in the declared guard of
    a subject that only checked native entries reach is held by the guard;
    every other way in keeps it a finding."""

    definitions = _defs(
        **{"fn-serve": "(defun fn-serve (cfg s) (declare (xargs :guard (and (fn-cfgp cfg) (fn-inv s)))) (list cfg s))",
           "fn-serve-program": "(defun fn-serve-program (s) (declare (xargs :mode :program :guard (fn-inv s))) s)",
           "fn-serve-unverified": "(defun fn-serve-unverified (s) (declare (xargs :guard (fn-inv s) :verify-guards nil)) s)",
           "fn-wrap": "(defun fn-wrap (s) (declare (xargs :guard (fn-inv s))) (fn-serve nil s))"})

    def model(self, entries, mentions, edges=None, program_books=()):
        edges = edges if edges is not None else {"fn-wrap": {"fn-serve"}}
        return premise_audit.GuardModel(edges, entries, set(mentions), self.definitions,
                                        set(program_books))

    def conclusion(self, text="(equal (fn-serve cfg s) :ok)"):
        return reach_check.read_sexp(text)

    def test_checked_entry_guard_holds_the_premise(self):
        m = self.model({"fn-wrap": COMPLIANT}, ["fn-wrap"])
        self.assertEqual(m.establishes("fn-inv", "s", self.conclusion(), ["fn-serve"]), "fn-serve")
        self.assertEqual(m.establishes("fn-cfgp", "cfg", self.conclusion(), ["fn-serve"]), "fn-serve")

    def test_the_premise_must_be_at_the_guarded_formal(self):
        m = self.model({"fn-wrap": COMPLIANT}, ["fn-wrap"])
        # fn-inv is the guard of the SECOND formal; here s is the first argument
        self.assertIsNone(m.establishes("fn-inv", "s", self.conclusion("(equal (fn-serve s cfg) :ok)"),
                                        ["fn-serve"]))
        self.assertIsNone(m.establishes("fn-other", "s", self.conclusion(), ["fn-serve"]))

    def test_program_wrapper_entry_establishes_nothing(self):
        m = self.model({"fn-wrap": {**COMPLIANT, "class": "program"}}, ["fn-wrap"])
        self.assertIsNone(m.establishes("fn-inv", "s", self.conclusion(), ["fn-serve"]))

    def test_ideal_entry_establishes_nothing(self):
        m = self.model({"fn-wrap": {**COMPLIANT, "class": "ideal"}}, ["fn-wrap"])
        self.assertIsNone(m.establishes("fn-inv", "s", self.conclusion(), ["fn-serve"]))

    def test_raw_with_and_raw_guarded_entries_establish_nothing(self):
        for row in ({**COMPLIANT, "raw_with": ["fn-inv-preserved"]},
                    {**COMPLIANT, "raw_guarded": [0, "nil", ["fn-inv"]]},
                    {**COMPLIANT, "applied_directly_in": ["host/native/owner.lisp"]}):
            m = self.model({"fn-wrap": row}, ["fn-wrap"])
            self.assertIsNone(m.establishes("fn-inv", "s", self.conclusion(), ["fn-serve"]), row)

    def test_an_unchecked_path_beside_the_checked_one_keeps_the_finding(self):
        # the native code also names fn-serve itself (not an entry: a raw call)
        m = self.model({"fn-wrap": COMPLIANT}, ["fn-wrap", "fn-serve"])
        self.assertIsNone(m.establishes("fn-inv", "s", self.conclusion(), ["fn-serve"]))

    def test_program_and_unverified_subjects_are_never_credited(self):
        entries = {"fn-serve-program": COMPLIANT, "fn-serve-unverified": COMPLIANT}
        m = self.model(entries, list(entries), edges={})
        for s in entries:
            self.assertIsNone(m.establishes("fn-inv", "s", self.conclusion(f"(equal ({s} s) s)"), [s]), s)
        m = self.model({"fn-wrap": COMPLIANT}, ["fn-wrap"], program_books=["books/g.lisp"])
        self.assertIsNone(m.establishes("fn-inv", "s", self.conclusion(), ["fn-serve"]))

    def test_audit_reports_the_class_not_a_finding(self):
        class Graph(StubGraph):
            def __init__(self):
                super().__init__()
                self.book_defs = {**self.book_defs, "fn-cfgp": 1}
        forms = {"fn-serve-ok": ("books/b.lisp",
                                 "(defthm fn-serve-ok (implies (fn-inv s) (equal (fn-serve cfg s) :ok)))")}
        guard = self.model({"fn-wrap": COMPLIANT}, ["fn-wrap"])
        original = (reach_check.theorem_forms, reach_check.record_definitions,
                    reach_check.Subject.hosted)
        reach_check.theorem_forms = lambda paths: dict(forms)
        reach_check.record_definitions = lambda paths: {}
        reach_check.Subject.hosted = lambda self, graph: True
        try:
            with_guard = premise_audit.Audit(Graph(), guard)
            without = premise_audit.Audit(Graph())
        finally:
            (reach_check.theorem_forms, reach_check.record_definitions,
             reach_check.Subject.hosted) = original
        # red before: without the model fn-inv is never concluded, a finding
        self.assertIn("fn-inv", without.findings())
        # green after: held by fn-serve's checked guard, its own class
        row = with_guard.premises()["fn-inv"]
        self.assertEqual(row["class"], premise_audit.GUARD)
        self.assertEqual(row["guard_established"], [("fn-serve-ok", "fn-serve")])
        self.assertNotIn("fn-inv", with_guard.findings())


if __name__ == "__main__":
    unittest.main()

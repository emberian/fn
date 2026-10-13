"""tools/premise_audit.py: the reader's decisions on small forms, and the
classification on a stub graph (no tree read: the whole-tree run is the
box's)."""
import pathlib
import sys
import unittest
import contextlib
import io
import json
import tempfile
from unittest import mock

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
        self.assertEqual(app(reach_check.read_sexp("(fn-inv s)")), ("fn-inv", ["s"]))
        self.assertEqual(app(reach_check.read_sexp("(equal (fn-inv s) t)")), ("fn-inv", ["s"]))
        self.assertEqual(app(reach_check.read_sexp("(equal t (fn-inv s))")), ("fn-inv", ["s"]))
        self.assertEqual(app(reach_check.read_sexp("(fn-get 0 x)")), ("fn-get", ["0", "x"]))
        self.assertIsNone(app(reach_check.read_sexp("(not (fn-inv s))")))
        self.assertIsNone(app(reach_check.read_sexp("(equal (f s) (g s))")))
        self.assertIsNone(app("s"))

    def test_a_constant_argument_is_no_variable(self):
        # A17, lane/vertical-lease: numerals, keywords, characters, t and nil
        # in front of the subject were read as "the bare variable".
        var = premise_audit.variable_argument
        read = reach_check.read_sexp
        self.assertIsNone(var(read("(r 0 (fn-slots s))")[1:], set()))
        self.assertEqual(var(read("(r 0 x)")[1:], set()), "x")
        self.assertEqual(var(read("(r :hand hd id s)")[1:], set()), "hd")
        self.assertIsNone(var(read("(r #x10 -1 1/2 t nil #\\a)")[1:], set()))
        self.assertIsNone(var(read("(r *fn-max*)")[1:], {"*fn-max*"}))


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
                          "fn-other": 1, "fn-model-open": 1, "fn-slot": 1, "fn-pick": 1}
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
        # Index-first predicates (A17): assumed of a term at a hosted entry,
        # established by the hosted open in the second position.
        "fn-slot-serve": ("books/c.lisp", "(defthm fn-slot-serve (implies (fn-slot 0 (fn-step s)) (equal (fn-serve s) :ok)))"),
        "fn-slot-of-open": ("books/c.lisp", "(defthm fn-slot-of-open (fn-slot 0 (fn-open x)))"),
        "fn-pick-serve": ("books/c.lisp", "(defthm fn-pick-serve (implies (fn-pick 0 s) (equal (fn-serve s) :ok)))"),
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

    def test_index_first_premise_of_a_term_is_not_bare(self):
        audit = self.audit()
        rows = audit.assumed["fn-slot"]
        self.assertEqual([(t, bare) for t, _, _, bare, _ in rows], [("fn-slot-serve", False)])
        self.assertNotIn("fn-slot", audit.premises())
        self.assertIn("fn-slot", audit.premises(all_arguments=True))

    def test_index_first_establishment_reads_every_argument(self):
        self.assertEqual(self.audit(hosted_open=True).classify("fn-slot"), premise_audit.HOSTED)
        self.assertEqual(self.audit(hosted_open=False).classify("fn-slot"), premise_audit.OFF_HOST)

    def test_index_first_premise_of_a_variable_stays_a_finding(self):
        audit = self.audit()
        self.assertEqual([bare for _, _, _, bare, _ in audit.assumed["fn-pick"]], [True])
        self.assertIn("fn-pick", audit.findings())

    def test_summary_counts(self):
        audit = self.audit(hosted_open=False)
        line = premise_audit.summary_line(audit.findings(), audit.premises(), {"accepted": {}})
        # Three theorems assume a finding's premise at a hosted entry: the
        # preservation `(implies (fn-inv s) (fn-inv (fn-step s)))' assumes
        # fn-inv at the hosted step too, as it should (the step is entered
        # with the premise the open never established).  fn-pick (a bare
        # variable behind an index) is the third, never concluded; fn-slot
        # is of a term, so it is not counted.
        self.assertIn("3 premises at hosted entries, 3 unestablished (4 theorems)", line)
        self.assertIn("1 never concluded", line)
        self.assertIn("2 established off the host path", line)


class EstablishmentFixture(unittest.TestCase):
    predicate = "fn-ovr-plan-cursor"
    entry = "fn-ovr-plan-lease-quantum"
    theorem = "fn-ovr-plan-lease-quantum-taken-is-over"
    form = """(defthm fn-ovr-plan-lease-quantum-taken-is-over
  (implies (posp (mv-nth 0 (fn-ovr-plan-lease-quantum plan w h id inc s fn-arena fn-cat)))
           (and (fn-ovr-plan-cursor plan)
                (fn-ovw-cursorp (fn-ovr-plan-cursor plan)))))"""

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.path = pathlib.Path(directory.name) / "premise-establishments.json"
        with contextlib.redirect_stdout(io.StringIO()):
            premise_audit.initialize_establishments(self.path)

    def audit(self, form=None, reachable=True, hosted_heads=(), stobj_names=(),
              definitions=(), predicate=None, local=(), missing=False):
        predicate = predicate or self.predicate
        graph = StubGraph()
        graph.book_defs.update(dict.fromkeys(
            [predicate, self.entry, "fn-ovw-cursorp", *definitions], 1))
        if reachable:
            graph.reachable.add(self.entry)
        graph.reachable.update(hosted_heads)
        graph.stobj_names.update(stobj_names)
        forms = {
            self.theorem: ("books/fixture.lisp", form or self.form),
            "fn-over-serve": ("books/fixture.lisp",
                              f"(defthm fn-over-serve (implies ({predicate} plan)"
                              " (equal (fn-serve plan) :ok)))"),
        }
        if missing:
            forms.pop(self.theorem)
        with mock.patch.object(reach_check, "theorem_forms", return_value=forms), \
                mock.patch.object(reach_check, "record_definitions", return_value={}), \
                mock.patch.object(premise_audit, "local_theorems", return_value=set(local)), \
                mock.patch.object(reach_check.Subject, "hosted",
                                  lambda self, graph: bool(set(self.functions) & graph.reachable)):
            return premise_audit.Audit(graph, establishments_path=self.path)

    def command(self, audit, args):
        output = io.StringIO()
        def baseline(path=None):
            findings = audit.term_findings() if path == premise_audit.TERM_BASELINE else audit.findings()
            return {"accepted": dict.fromkeys(findings, "fixture")}
        with mock.patch.object(premise_audit, "ESTABLISHMENTS", self.path), \
                mock.patch.object(reach_check, "Graph", return_value=audit.graph), \
                mock.patch.object(premise_audit, "native_guard_model", return_value=None), \
                mock.patch.object(premise_audit, "Audit", return_value=audit), \
                mock.patch.object(premise_audit, "load_baseline", side_effect=baseline), \
                contextlib.redirect_stdout(output):
            status = premise_audit.main(args)
        return status, output.getvalue()

    def register(self, audit, predicate=None, call=None, theorem=None):
        return self.command(audit, ["--register-establishment", predicate or self.predicate,
                                    theorem or self.theorem, call or self.entry])

    def assert_hosted(self, audit):
        self.assertEqual(audit.classify(self.predicate), premise_audit.HOSTED)
        self.assertEqual(audit.premises()[self.predicate]["class"], premise_audit.HOSTED)
        self.assertNotIn(self.predicate, audit.findings())
        self.assertEqual(audit.concluded[self.predicate], [
            (self.theorem, "books/fixture.lisp", [self.entry], True)])

    def assert_off_host(self, audit, heads=(), predicate=None):
        predicate = predicate or self.predicate
        self.assertEqual(audit.classify(predicate), premise_audit.OFF_HOST)
        self.assertIn(predicate, audit.findings())
        self.assertEqual(audit.concluded[predicate], [
            (self.theorem, "books/fixture.lisp", list(heads), False)])

    def assert_refused(self, audit, condition, predicate=None, call=None):
        before = self.path.read_bytes() if self.path.exists() else None
        with mock.patch.object(premise_audit, "_write_establishments",
                               wraps=premise_audit._write_establishments) as writer:
            status, output = self.register(audit, predicate, call)
            writer.assert_not_called()
        self.assertEqual(status, 1)
        self.assertIn(condition, output)
        self.assertIn(self.theorem, output)
        self.assertEqual(self.path.read_bytes() if self.path.exists() else None, before)
        self.assertNotEqual(audit.classify(predicate or self.predicate), premise_audit.HOSTED)

    def shape(self, hypothesis, argument, predicate=None):
        return (f"(defthm {self.theorem} (implies {hypothesis}"
                f" ({predicate or self.predicate} {argument})))")


class RegisteredEstablishments(EstablishmentFixture):
    def test_exact_over_requires_a_registered_row(self):
        self.assert_off_host(self.audit())
        status, output = self.register(self.audit())
        self.assertEqual(status, 0, output)
        expected = [{"premise": self.predicate, "theorem": self.theorem, "call": self.entry}]
        self.assertEqual(json.loads(self.path.read_text()), expected)
        self.assertEqual(self.path.read_text(), json.dumps(expected, indent=2, sort_keys=True) + "\n")
        registered = self.audit()
        self.assert_hosted(registered)
        status, output = self.command(registered, ["--explain", self.predicate])
        self.assertEqual(status, 0)
        self.assertIn(f"established by registered row {self.theorem} via {self.entry}", output)

    def test_log_prefix_term_is_refused_without_writing(self):
        predicate = "fn-lgp-relp"
        heads = ["fn-lgrc-attempt", "fn-lgrc-final"]
        form = self.shape("(not (fn-bsc-lookup s stg stage))",
                          "(fn-lgrc-final (fn-lgrc-attempt s j k) s)", predicate)
        audit = self.audit(form, definitions=[*heads, "fn-bsc-lookup"],
                           hosted_heads=["fn-bsc-lookup"], predicate=predicate)
        self.assert_off_host(audit, heads, predicate)
        self.assert_refused(audit, "single bare variable", predicate, "fn-bsc-lookup")

    def test_recognizer_root_is_refused_without_writing(self):
        predicate = "fn-his-cursors-apart"
        form = self.shape("(fn-his-cellsp cells)", "cells", predicate)
        audit = self.audit(form, definitions=["fn-his-cellsp"],
                           hosted_heads=["fn-his-cellsp"], predicate=predicate)
        self.assert_refused(audit, "primitive conjunct root", predicate, "fn-his-cellsp")

    def test_call_below_a_book_function_is_refused_without_writing(self):
        predicate = "fn-ptx-wfp"
        form = self.shape("(<= (fn-rtc-size (fn-rtc-get i m)) 1)", "m", predicate)
        audit = self.audit(form, definitions=["fn-rtc-size", "fn-rtc-get"],
                           hosted_heads=["fn-rtc-size", "fn-rtc-get"], predicate=predicate)
        self.assert_refused(audit, "nested book calls excluded", predicate, "fn-rtc-get")

    def test_different_variable_is_refused_without_writing(self):
        audit = self.audit(self.form.replace(f"({self.entry} plan", f"({self.entry} other"))
        self.assert_refused(audit, "matching direct bare variable")

    def test_concluded_term_containing_variable_is_refused_without_writing(self):
        audit = self.audit(self.form.replace("(fn-ovr-plan-cursor plan)",
                                             "(fn-ovr-plan-cursor (nth 0 plan))"))
        self.assert_refused(audit, "single bare variable")

    def test_unreachable_call_is_refused_without_writing(self):
        self.assert_refused(self.audit(reachable=False), "not host-reachable")

    def test_stobj_call_is_refused_without_writing(self):
        self.assert_refused(self.audit(stobj_names=[self.entry]), "stobj name")

    def test_same_predicate_call_is_refused_without_writing(self):
        audit = self.audit(self.form.replace(self.entry + " plan", self.predicate + " plan"),
                           hosted_heads=[self.predicate])
        self.assert_refused(audit, "concluded predicate R", call=self.predicate)

    def test_local_theorem_is_refused_without_writing(self):
        self.assert_refused(self.audit(local=[self.theorem]), "theorem is local")

    def test_missing_theorem_is_refused_without_writing(self):
        self.path = self.path.with_name("absent-register.json")
        self.assert_refused(self.audit(missing=True), "theorem is missing")

    def test_constants_terms_and_quoted_calls_are_refused(self):
        for value in ("t", "nil", ":plan", "0", "fn-ovw-cursorp", "'plan", "(nth 0 plan)"):
            with self.subTest(concluded=value):
                self.assert_refused(self.audit(self.form.replace(" plan", f" {value}")),
                                    "single bare variable")
        for hypothesis in (f"'({self.entry} plan)", f"(posp ({self.entry} 'plan))"):
            with self.subTest(hypothesis=hypothesis):
                self.assert_refused(self.audit(self.shape(hypothesis, "plan")),
                                    "matching direct bare variable")

    def test_stale_row_is_refused_and_strict_fails_without_writing(self):
        self.assertEqual(self.register(self.audit())[0], 0)
        before = self.path.read_bytes()
        stale = self.audit(self.form.replace(f"({self.entry} plan", f"({self.entry} other"))
        self.assert_off_host(stale)
        self.assertEqual(len(stale.refused_establishments), 1)
        status, output = self.command(stale, ["--strict", "--summary"])
        self.assertEqual(status, 1)
        self.assertIn(f"refused registered row {self.predicate} {self.theorem} via {self.entry}", output)
        self.assertIn("matching direct bare variable", output)
        self.assertNotIn("NEW unestablished", output)  # the refused row alone makes strict red
        self.assertEqual(self.path.read_bytes(), before)
        missing = self.audit(missing=True)
        self.assertIn("theorem is missing", missing.refused_establishments[0])
        self.assertNotEqual(missing.classify(self.predicate), premise_audit.HOSTED)
        for kwargs, condition in (({"reachable": False}, "not host-reachable"),
                                  ({"local": [self.theorem]}, "theorem is local"),
                                  ({"stobj_names": [self.entry]}, "stobj name")):
            with self.subTest(current_tree=kwargs):
                invalid = self.audit(**kwargs)
                self.assert_off_host(invalid)
                self.assertIn(condition, invalid.refused_establishments[0])
                self.assertEqual(self.path.read_bytes(), before)

    def test_unregister_removes_row_and_absent_unregister_refuses(self):
        self.assertEqual(self.register(self.audit())[0], 0)
        status, output = self.command(self.audit(), ["--unregister-establishment", self.predicate, self.theorem])
        self.assertEqual(status, 0, output)
        self.assertEqual(self.path.read_text(), "[]\n")
        self.assert_off_host(self.audit())
        before = self.path.read_bytes()
        status, output = self.command(self.audit(), ["--unregister-establishment", self.predicate, self.theorem])
        self.assertEqual(status, 1)
        self.assertIn("no such registered row", output)
        self.assertEqual(self.path.read_bytes(), before)

    def test_rows_are_sorted_and_duplicate_register_does_not_write(self):
        audit = self.audit()
        audit.theorems["a-first"] = ("books/fixture.lisp", self.form.replace(self.theorem, "a-first"))
        self.assertEqual(self.register(audit)[0], 0)
        self.assertEqual(self.register(audit, theorem="a-first")[0], 0)
        rows = json.loads(self.path.read_text())
        self.assertEqual([row["theorem"] for row in rows], ["a-first", self.theorem])
        before = self.path.read_bytes()
        status, output = self.register(audit)
        self.assertEqual(status, 1)
        self.assertIn("already registered", output)
        self.assertEqual(self.path.read_bytes(), before)

    def test_register_operation_cannot_bypass_strict_audit(self):
        before = self.path.read_bytes()
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
            self.command(self.audit(), ["--strict", "--register-establishment",
                                        self.predicate, self.theorem, self.entry])
        self.assertEqual(error.exception.code, 2)
        self.assertEqual(self.path.read_bytes(), before)

    def test_shape_two_is_used_to_check_register_rows(self):
        form = (f"(defthm {self.theorem} (if (posp ({self.entry} plan))"
                f" ({self.predicate} plan) t))")
        audit = self.audit(form)
        self.assert_off_host(audit)
        self.assertEqual(self.register(audit)[0], 0)
        self.assert_hosted(self.audit(form))

    def test_preservation_cannot_be_registered_as_establishment(self):
        form = (f"(defthm {self.theorem} (implies ({self.predicate} plan)"
                f" (if (posp ({self.entry} plan)) ({self.predicate} plan) t)))")
        audit = self.audit(form)
        self.assertEqual(audit.classify(self.predicate), premise_audit.PRESERVED)
        self.assert_refused(audit, "preservation, not establishment")


class ConditionalConclusions(EstablishmentFixture):
    predicate = "fn-owner-retain-statep"
    entry = "fn-owner-install-extended"
    theorem = "fn-owner-install-extended-establishes-when-recovering"
    form = """(defthm fn-owner-install-extended-establishes-when-recovering
  (implies (or (equal oc :fault) (fn-lgoc-invariantp oc))
           (if (equal (mv-nth 1 (fn-owner-install-extended oc extended key fn-arena fn-cat fn-hist state)) :recovering)
               (fn-owner-retain-statep (mv-nth 5 (fn-owner-install-extended oc extended key fn-arena fn-cat fn-hist state)))
             t)))"""

    def test_exact_carried_ok_shape_is_hosted_without_a_row(self):
        self.assertEqual(self.path.read_text(), "[]\n")
        audit = self.audit()
        self.assert_hosted(audit)
        hyps, conclusion = premise_audit.statement(self.form)
        branches = premise_audit.conclusion_branches(hyps, conclusion)
        self.assertEqual(len(branches), 1)
        effective, result = branches[0]
        self.assertEqual(effective, hyps + [conclusion[1]])
        flat = reach_check.flatten(["defthm", self.theorem, ["implies", ["and", *effective], result]])
        equivalent = self.audit(flat)
        self.assertEqual(audit.concluded, equivalent.concluded)
        self.assertEqual(audit.assumed, equivalent.assumed)
        self.assertEqual(audit.preserving, equivalent.preserving)

    def test_non_true_else_is_not_an_establishment(self):
        audit = self.audit(self.form.replace("             t)))", "             nil)))"))
        self.assertEqual(audit.classify(self.predicate), premise_audit.NEVER)
        self.assertIn(self.predicate, audit.findings())

    def test_if_branch_carries_its_condition_as_a_preservation_hypothesis(self):
        form = (f"(defthm {self.theorem} (if ({self.predicate} s)"
                f" ({self.predicate} ({self.entry} s)) t))")
        audit = self.audit(form)
        self.assertEqual(audit.classify(self.predicate), premise_audit.PRESERVED)
        self.assertEqual(audit.preserving[self.predicate], [self.theorem])
        self.assertEqual(audit.concluded.get(self.predicate, []), [])

    def test_original_hypothesis_still_makes_if_conclusion_a_preservation(self):
        form = (f"(defthm {self.theorem} (implies ({self.predicate} s)"
                f" (if (posp ({self.entry} s)) ({self.predicate} ({self.entry} s)) t)))")
        audit = self.audit(form)
        self.assertEqual(audit.classify(self.predicate), premise_audit.PRESERVED)
        self.assertEqual(audit.preserving[self.predicate], [self.theorem])

    def test_conditional_hypothesis_does_not_contaminate_an_and_sibling(self):
        form = (f"(defthm {self.theorem} (and"
                f" (if ({self.predicate} s) ({self.predicate} ({self.entry} s)) t)"
                f" ({self.predicate} ({self.entry} other))))")
        audit = self.audit(form)
        self.assert_hosted(audit)
        self.assertEqual(audit.preserving[self.predicate], [self.theorem])


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


class LowerStale(unittest.TestCase):
    """--lower-stale drops exactly the entries --strict calls stale, keeps the
    rest (accepted text included) and adds no finding, NEW ones included."""

    def test_only_stale_entries_leave(self):
        import json
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            path = pathlib.Path(d) / "premise-baseline.json"
            baseline = {"note": "n", "accepted": {"fn-kept": "why kept", "fn-gone": "why gone"}}
            path.write_text(json.dumps(baseline))
            findings = {"fn-kept": {"class": "never concluded"},
                        "fn-new": {"class": "never concluded"}}
            original = premise_audit.BASELINE
            premise_audit.BASELINE = path
            try:
                removed = premise_audit.lower_stale(findings, baseline)
            finally:
                premise_audit.BASELINE = original
            self.assertEqual(removed, ["fn-gone"])
            written = json.loads(path.read_text())
            self.assertEqual(written, {"note": "n", "accepted": {"fn-kept": "why kept"}})

    def test_nothing_stale_writes_nothing(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            path = pathlib.Path(d) / "premise-baseline.json"
            original = premise_audit.BASELINE
            premise_audit.BASELINE = path
            try:
                removed = premise_audit.lower_stale({"fn-a": {}}, {"accepted": {"fn-a": "x"}})
            finally:
                premise_audit.BASELINE = original
            self.assertEqual(removed, [])
            self.assertFalse(path.exists())


class TermPremises(unittest.TestCase):
    """The Fungus case (10-11): fn-lgo-rows-history-within assumed of
    (nthcdr k rows) by L2-4, L2-5 and L2H-2 at a hosted entry and never
    concluded was invisible to --strict, which counted bare variables only."""
    forms = {
        # The case as stated (books/store-log-open-scan.lisp:941): ALLOW is a
        # variable argument, so with every argument read it is a bare finding.
        "l2-4": ("books/store-log-open-scan.lisp",
                 "(defthm l2-4 (implies (fn-lgo-rows-history-within (nthcdr k rows) allow)"
                 " (equal (fn-serve rows) :ok)))"),
        # The same shape with no variable argument: a term finding only.
        "l2-term": ("books/store-log-open-scan.lisp",
                    "(defthm l2-term (implies (fn-lgo-rows-within (nthcdr k rows))"
                    " (equal (fn-serve rows) :ok)))"),
        "fn-inv-serve": ("books/a.lisp", "(defthm fn-inv-serve (implies (fn-inv s) (equal (fn-serve s) :ok)))"),
    }

    def audit(self, extra=None):
        graph = StubGraph()
        graph.book_defs = dict(graph.book_defs, **{"fn-lgo-rows-history-within": 1,
                                                   "fn-lgo-rows-within": 1, "nthcdr": 1})
        forms = dict(self.forms, **(extra or {}))
        original = (reach_check.theorem_forms, reach_check.record_definitions,
                    reach_check.Subject.hosted)
        reach_check.theorem_forms = lambda paths: dict(forms)
        reach_check.record_definitions = lambda paths: {}
        reach_check.Subject.hosted = lambda self, graph: bool(set(self.functions) & graph.reachable)
        try:
            return premise_audit.Audit(graph)
        finally:
            (reach_check.theorem_forms, reach_check.record_definitions,
             reach_check.Subject.hosted) = original

    def test_the_stated_case_is_now_a_bare_finding(self):
        findings = self.audit().findings()
        self.assertEqual(findings["fn-lgo-rows-history-within"]["theorems"],
                         [("l2-4", "books/store-log-open-scan.lisp")])

    def test_a_term_premise_is_a_term_finding_not_a_bare_one(self):
        audit = self.audit()
        self.assertNotIn("fn-lgo-rows-within", audit.findings())
        terms = audit.term_findings()
        self.assertEqual(list(terms), ["fn-lgo-rows-within"])
        self.assertEqual(terms["fn-lgo-rows-within"]["class"], premise_audit.NEVER)

    def test_strict_refuses_a_new_term_premise_and_a_stale_term_entry(self):
        audit = self.audit()
        findings, terms = audit.findings(), audit.term_findings()
        accepted = dict.fromkeys(findings, "x")
        lines, rc = premise_audit.strict_verdict(findings, accepted, terms, {})
        self.assertEqual(rc, 1)
        self.assertIn("NEW unestablished premise of a term fn-lgo-rows-within", lines[0])
        lines, rc = premise_audit.strict_verdict(findings, accepted, terms, {"fn-lgo-rows-within": "x"})
        self.assertEqual((lines, rc), ([], 0))
        # established at the host: the entry is stale, and strict says so
        opened = self.audit({"l-open": ("books/store-log-open-scan.lisp",
                                        "(defthm l-open (fn-lgo-rows-within (fn-open x)))")})
        self.assertEqual(opened.term_findings(), {})
        lines, rc = premise_audit.strict_verdict(opened.findings(), accepted, opened.term_findings(),
                                                 {"fn-lgo-rows-within": "x"})
        self.assertEqual(rc, 1)
        self.assertIn("term baseline entry fn-lgo-rows-within is no longer a finding", lines[0])

    def test_term_baseline_captures_once_then_only_shrinks(self):
        import json
        import tempfile
        terms = self.audit().term_findings()
        with tempfile.TemporaryDirectory() as d:
            path = pathlib.Path(d) / "premise-term-baseline.json"
            original = premise_audit.TERM_BASELINE
            premise_audit.TERM_BASELINE = path
            try:
                self.assertEqual(premise_audit.write_term_baseline(terms), 0)   # initial capture
                self.assertEqual(list(json.loads(path.read_text())["accepted"]),
                                 ["fn-lgo-rows-within"])
                grown = dict(terms, **{"fn-other-term": {"class": premise_audit.NEVER}})
                self.assertEqual(premise_audit.write_term_baseline(grown), 1)   # refused: it only shrinks
                removed = premise_audit.lower_stale({}, json.loads(path.read_text()), path)
                self.assertEqual(removed, ["fn-lgo-rows-within"])
                self.assertEqual(json.loads(path.read_text())["accepted"], {})
            finally:
                premise_audit.TERM_BASELINE = original


if __name__ == "__main__":
    unittest.main()

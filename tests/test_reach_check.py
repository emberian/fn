"""tools/reach_check.py: the orphan it reports must be a real orphan.

A gate that cries wolf gets switched off.  These tests pin the two things
that would make this one lie: a function the host demonstrably calls must
never be reported unreachable, and a function named nowhere outside the
books must never be reported hosted.
"""
import io
import json
from contextlib import redirect_stdout
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import reach_check                                            # noqa: E402


class GraphTests(unittest.TestCase):
    """The call graph, against functions whose status is not in doubt."""

    @classmethod
    def setUpClass(cls):
        cls.graph = reach_check.Graph()

    def test_the_served_read_path_is_reachable(self):
        """host/owner-host.lisp fn-owner-chunk calls fn-own-read, which runs
        fn-served-step, which dispatches to fn-peer-command."""
        for name in ("fn-own-read", "fn-served-step", "fn-peer-command",
                     "fn-peer-decide-offer"):
            self.assertIn(name, self.graph.reachable,
                          f"{name} is on the served path and must be reachable")

    def test_a_function_named_nowhere_outside_books_is_not_reachable(self):
        """The control. fn-transfer-* has no adapter on this tree; if this
        starts failing, either transfer got hosted (good, rebaseline) or the
        graph has started reaching through something it should not."""
        named = subprocess.run(
            ["grep", "-rl", "fn-transfer-add-chunk", "host/", "tools/"],
            cwd=ROOT, capture_output=True, text=True).stdout.split()
        self.assertEqual(named, [], "the premise of this test has changed")
        self.assertNotIn("fn-transfer-add-chunk", self.graph.reachable)

    def test_an_attached_implementation_is_reached_through_its_constraint(self):
        """host/store-host.lisp names files through fn-store-txn-name ->
        fn-sbud-txn-name -> the constrained fn-bs-txn-name, which
        books/byte-store-txn-name.lisp `defattach`es to fn-bs-txn-name-impl."""
        self.assertIn("fn-bs-txn-name-impl", self.graph.reachable)

    def test_a_defstobj_creator_is_reached_through_the_abstract_creator(self):
        """books/payload-arena-paged.lisp `(defstobj fn-arena$p ...)' is the
        foundation of `fn-arena-paged', whose :creator runs `:exec
        create-fn-arena$p'; the paged arena is reached through the live
        extent arena's seal (host/bp-ingress-host.lisp -> fn-arena-seal-list
        -> ... -> fn-arena-paged-seal-list), so its creator ran too: a
        theorem concluding of `(create-fn-arena$p)' is concluded of a
        reached function (the premise audit's establishment by the
        creator)."""
        self.assertIn("create-fn-arena$p", self.graph.book_defs)
        self.assertNotIn("create-fn-arena$p", self.graph.stobj_names)
        self.assertIn("create-fn-arena$p", self.graph.reachable)
        self.assertIn("create-fn-arena-paged", self.graph.host_chain("create-fn-arena$p"))

    def test_only_loaded_hosts_seed_book_symbols(self):
        self.assertGreater(self.graph.seeds["host"], 0)
        self.assertEqual(set(self.graph.seeds), {"host"})

    def test_a_record_recognizer_reaches_its_field_conjuncts(self):
        """PKT-394: fn-sco-finalize-from checks fn-node-statep, whose
        fn-defrecord :fields call fn-statep and
        fn-node-articles-have-archive-bindingsp; fn-statep's own :fields call
        fn-articles-freshp, whose :exec is fn-fr-freshp.  Without the macro's
        expansion none of them is a definition and the path is invisible."""
        self.assertIn("fn-node-statep", self.graph.book_defs)
        self.assertIn("fn-statep", self.graph.edges["fn-node-statep"])
        self.assertIn("fn-node-articles-have-archive-bindingsp",
                      self.graph.edges["fn-node-statep"])
        for name in ("fn-node-statep", "fn-node-articles-have-archive-bindingsp",
                     "fn-nab-articles-boundp", "fn-articles-freshp", "fn-fr-freshp"):
            self.assertIn(name, self.graph.reachable)
        # The proof-only relation stays unreached: no executed function calls it.
        self.assertIn("fn-fr-disjointp", self.graph.book_defs)
        self.assertNotIn("fn-fr-disjointp", self.graph.reachable)

    def test_record_expansion_reads_the_keywords(self):
        with tempfile.TemporaryDirectory() as tmp:
            book = Path(tmp) / "r.lisp"
            book.write_text(
                '(fn-defrecord fn-q\n'
                '  :constructor (fn-q-make a b)\n'
                '  :fields ((fn-q-a natp) ; a comment (unbalanced\n'
                '           (fn-q-b (fn-q-good-b "(" (fn-q-b x))))\n'
                '  :extra ((fn-q-whole x)))\n'
                '(fn-defrecord fn-r :constructor (fn-r-make a) :fields ((fn-r-a t))\n'
                '  :recognizer fn-r-okp :recognizer-formals (ctx))\n'
                '(fn-defrecord fn-s :constructor (fn-s-make a) :fields ((fn-s-a t))\n'
                '  :recognizer nil)\n', encoding="utf-8")
            saved = reach_check.ROOT
            reach_check.ROOT = Path(tmp)
            try:
                defs = reach_check.record_definitions([book])
            finally:
                reach_check.ROOT = saved
        self.assertEqual(sorted(defs), ["fn-qp", "fn-r-okp"])
        body = reach_check.Graph.symbols(defs["fn-qp"][1])
        self.assertTrue({"natp", "fn-q-good-b", "fn-q-whole"} <= body)
        self.assertIn("ctx", reach_check.Graph.symbols(defs["fn-r-okp"][1]))
        # accessors and the constructor are plumbing, not definitions here
        self.assertNotIn("fn-q-a", defs)
        self.assertNotIn("fn-q-make", defs)


class SubjectRuleTests(unittest.TestCase):
    """The subject is the function the host calls (AGENTS.md; keystone audit
    2026-09-27).  Each test is one of the ways an event used to pass on the
    strength of something that is not its subject."""

    @classmethod
    def setUpClass(cls):
        cls.graph = reach_check.Graph()
        cls.theorems = reach_check.theorem_forms(cls.graph.books)

    def subject(self, name):
        return reach_check.Subject(self.graph, name, self.theorems[name][1])

    def test_a_dollar_symbol_is_one_symbol(self):
        """`(defun fn-arena$lcorr ...)' used to define `fn-arena', so every
        theorem naming the stobj was hosted by the stobj's name."""
        self.assertEqual(reach_check.Graph.symbols("(fn-octets$corr a b)"),
                         {"fn-octets$corr", "a", "b"})
        self.assertIn("fn-arena$lcorr", self.graph.book_defs)
        self.assertNotIn("fn-arena", self.graph.book_defs)

    def test_stobj_names_are_never_the_subject(self):
        for name in ("fn-arena", "fn-cat", "state"):
            self.assertIn(name, self.graph.stobj_names)
        s = self.subject("fn-sca-load-history-establishes-relation")
        self.assertNotIn("fn-arena", s.functions)
        self.assertIn("fn-sca-load-history", s.functions)
        self.assertFalse(s.hosted(self.graph),
                         "the host loads with fn-sca-load-held-rows (G5-1)")

    def test_a_hypothesis_recognizer_does_not_host(self):
        """G3-1: the LZ codec passed on `(fn-cbor-octet-listp x)'.  The LZ
        codec is host-reached since compression-extents, so the witness is
        now the byte store's write, whose theorem has the same hypothesis."""
        s = self.subject("fn-bs-write-preserves-statep")
        self.assertNotIn("fn-cbor-octet-listp", s.functions)
        self.assertFalse(s.hosted(self.graph))

    def test_hints_do_not_host(self):
        form = ("(defthm t1 (equal (fn-bs-write s ino off octets outcome) c) "
                ":hints ((\"Goal\" :use ((:instance fn-own-read-preserves-relation)) "
                ":in-theory (enable fn-own-read))))")
        s = reach_check.Subject(self.graph, "t1", form)
        self.assertEqual(s.functions, ["fn-bs-write"])
        self.assertFalse(s.hosted(self.graph))

    def test_a_hosted_function_over_a_models_state_is_the_model(self):
        """G1-1: fn-ocv-reader-view is hosted, but here it reads the count
        machine's views."""
        self.assertIn("fn-ocv-reader-view", self.graph.reachable)
        s = self.subject("fn-ocvm-reader-view-is-the-completed-prefix")
        self.assertIn("fn-ocv-reader-view", s.functions)
        self.assertFalse(s.hosted(self.graph))

    def test_a_hosted_step_is_hosted(self):
        self.assertTrue(self.subject("fn-own-read-preserves-relation").hosted(self.graph))

    def test_an_absstobj_export_reaches_the_attached_implementation(self):
        """(attach-stobj fn-arena fn-arena-paged): the host's fn-arena-get
        runs fn-arena$p-get, so the paged correspondence is hosted and the
        retired byte-array one is not."""
        self.assertIn("fn-arena-get", self.graph.reachable)
        self.assertIn("fn-arena-paged-get", self.graph.reachable)
        self.assertIn("fn-arena$p-get", self.graph.reachable)
        paged = reach_check.Subject(self.graph, "fn-arena-paged-get{correspondence}", None)
        self.assertEqual(paged.functions, ["fn-arena-paged-get"])
        self.assertTrue(paged.hosted(self.graph))
        retired = reach_check.Subject(self.graph, "fn-arena-bytes-seal-list{correspondence}", None)
        self.assertFalse(retired.hosted(self.graph))

    def test_a_named_equality_ties_a_model_to_the_hosted_function(self):
        bridges = reach_check.equality_bridges(self.graph, self.theorems)
        self.assertIn(("fn-lgc-t-prepare", "fn-lgc-t-prepare-refines"),
                      bridges["fn-lgt-prepare"])
        self.assertIn(("fn-nov-lines-for-numbers", "fn-nov-indexed-lines-equal-archive-lines"),
                      bridges["fn-nov-lines-for-numbers-indexed"])

    def test_an_unfolding_or_commutation_is_not_an_equality_to_a_function(self):
        graph = self.graph
        cases = [
            ("fn-bs-fence-dir", "fn-bs-make",
             "(defthm x (equal (fn-bs-fence-dir d bs) (fn-bs-make (fn-bs-dirs bs) d i p n)))"),
            ("fn-rcl-reclaim-state", "fn-accept-prepare",
             "(defthm y (equal (fn-rcl-reclaim-state n (fn-accept-prepare a b c d e s) g) "
             "(fn-accept-prepare a b c d e (fn-rcl-reclaim-state n s g))))"),
            ("fn-bpnpf-read", "fn-bpnpf-default",
             "(defthm z (equal (fn-bpnpf-read x y) (fn-bpnpf-default)))"),
        ]
        for unhosted, other, form in cases:
            bridges = reach_check.equality_bridges(graph, {"t": ("f", form)})
            self.assertNotIn(other, [o for o, _ in bridges.get(unhosted, [])], form)


class CorrespondenceBridgeTests(unittest.TestCase):
    """Export attribution needs a named proof link and an executable call."""

    def setUp(self):
        self.event = "clear{correspondence}"
        self.link = "clear-keyed{correspondence}"
        self.theorems = {
            self.event: ("books/catalog.lisp", """(defthm clear{correspondence}
              (implies (corr c a) (corr (clear-c c) (clear-a a))))"""),
            self.link: ("books/catalog.lisp", """(defthm clear-keyed{correspondence}
              (implies (and (corr c a) (keyp key))
                (corr (keyed-c key c) (keyed-a key a)))
              :hints (("Goal" :use ((:instance clear{correspondence})))) )"""),
        }
        exports = {"clear": ("clear-a", "clear-c"),
                   "clear-keyed": ("keyed-a", "keyed-c"),
                   "clear-lookalike": ("look-a", "look-c")}
        self.graph = SimpleNamespace(
            books=[], book_defs=dict.fromkeys(exports),
            export_of=dict.fromkeys(exports, "catalog"),
            stobjs={"catalog": {"file": "books/catalog.lisp", "exports": exports}},
            stobj_names={"catalog"}, reachable={"clear-keyed", "clear-lookalike"},
            edges={"keyed-c": {"clear-c"}}, unreadable={}, unloaded_hosts=[], seeds={},
            host_chain=lambda name: ["host/owner.lisp", name])
        self.rows = [{"id": "PRF-201", "events": [self.event]}]

    def audit(self):
        with patch.object(reach_check, "theorem_forms", return_value=self.theorems), \
                patch.object(reach_check, "load_rows", return_value=self.rows):
            return reach_check.audit(self.graph)

    def test_linked_export_hosts_event_and_names_evidence_without_hosting_code(self):
        self.assertEqual(self.audit(), ([], 1, []))
        self.assertEqual(self.graph.correspondence_bridged,
                         [("PRF-201", self.event, "clear-keyed", self.link)])
        self.assertNotIn("clear", self.graph.reachable)

    def test_unlinked_lookalike_is_not_a_join(self):
        del self.theorems[self.link]
        findings, hosted, unresolved = self.audit()
        self.assertEqual((hosted, unresolved), (0, []))
        self.assertEqual([f.event for f in findings], [self.event])

    def test_citation_alone_or_call_alone_does_not_join(self):
        self.graph.edges = {}
        self.assertEqual(self.audit()[1], 0)
        self.graph.edges = {"keyed-c": {"clear-c"}}
        book, form = self.theorems[self.link]
        for hint in (':in-theory (enable clear{correspondence})',
                     ':use ((:instance clear{correspondence} (c other)))',
                     ':use ((:functional-instance clear{correspondence}))',
                     ':use (:functional-instance clear{correspondence})'):
            with self.subTest(hint=hint):
                self.theorems[self.link] = (book, form.replace(
                    ':use ((:instance clear{correspondence}))', hint))
                self.assertEqual(self.audit()[1], 0)

    def test_unreached_link_or_wrong_statement_does_not_join(self):
        self.graph.reachable = {"clear-lookalike"}
        self.assertEqual(self.audit()[1], 0)
        self.graph.reachable.add("clear-keyed")
        book, form = self.theorems[self.link]
        for old, new in (("(corr (keyed-c", "(other-corr (keyed-c"),
                         ("(keyed-c key c)", "(look-c key c)"),
                         ("(keyed-a key a)", "(look-a key a)")):
            with self.subTest(new=new):
                self.theorems[self.link] = (book, form.replace(old, new))
                self.assertEqual(self.audit()[1], 0)

    def test_other_stobj_and_preservation_are_not_attributed(self):
        self.graph.stobjs["other"] = self.graph.stobjs["catalog"]
        self.graph.export_of["clear-keyed"] = "other"
        self.assertEqual(self.audit()[1], 0)
        self.graph.export_of["clear-keyed"] = "catalog"
        self.rows[0]["events"] = ["clear{preserved}"]
        self.assertEqual(self.audit()[1], 0)

    def test_existing_named_export_equation_still_hosts(self):
        self.theorems = {"clear-equation": ("books/catalog.lisp",
                          "(defthm clear-equation (equal (clear a) (clear-keyed key a)))")}
        self.assertEqual(self.audit(), ([], 1, []))
        self.assertEqual(self.graph.bridged,
                         [("PRF-201", self.event, "clear", "clear-keyed", "clear-equation")])

    def test_listing_and_explanation_name_correspondence(self):
        for flags in (("--strict",), ("--explain", self.event)):
            output = io.StringIO()
            with patch.object(reach_check, "Graph", return_value=self.graph), \
                    patch.object(reach_check, "theorem_forms", return_value=self.theorems), \
                    patch.object(reach_check, "load_rows", return_value=self.rows), \
                    patch.object(reach_check, "load_baseline", return_value={"accepted": {}}), \
                    redirect_stdout(output):
                self.assertEqual(reach_check.main(flags), 0)
            self.assertIn("hosted through the named correspondence " + self.link,
                          output.getvalue())
            self.assertIn("clear-keyed (reached) uses " + self.event, output.getvalue())


class ResultProjectionBridgeTests(unittest.TestCase):
    """A complete named output abstraction, not an arbitrary composition."""

    PROJECTION = """(defun result (answer)
      (declare (xargs :guard t))
      (let ((joined (if (and (consp answer) (consp (cdr answer)))
                        (cadr answer) nil)))
        (list (if (consp answer) (car answer) nil)
              (if (consp joined) (car joined) nil))))"""
    BRIDGE = """(defthm receiver-refines
      (implies (receiver-only records)
        (equal (result (concrete store records arena))
               (model store records arena))))"""

    def graph(self, projection=None):
        return SimpleNamespace(book_defs={
            "result": ("books/bridge.lisp", projection or self.PROJECTION),
            "concrete": ("books/bridge.lisp", "(defun concrete (s r a) nil)"),
            "model": ("books/model.lisp", "(defun model (s r a) nil)"),
            "receiver-only": ("books/bridge.lisp", "(defun receiver-only (r) t)"),
        }, reachable={"concrete"})

    def test_full_result_projection_ties_only_model_to_concrete(self):
        graph = self.graph()
        for form in (self.BRIDGE,
                     "(defthm reversed (equal (model store records arena) "
                     "(result (concrete store records arena))))"):
            bridges = reach_check.equality_bridges(graph, {"bridge": ("b", form)})
            self.assertIn(("concrete", "bridge"), bridges["model"])
            self.assertNotIn(("model", "bridge"), bridges.get("concrete", []))
        self.assertEqual(graph.reachable, {"concrete"}, "a bridge does not host model code")

    def test_audit_records_named_bridge_without_mutating_reachability(self):
        graph = self.graph()
        graph.books = []
        graph.stobj_names, graph.export_of = set(), {}
        graph.unfold = lambda term: None
        model_form = "(defthm model-property (equal (car (model store records arena)) :ok))"
        theorems = {"receiver-refines": ("b", self.BRIDGE),
                    "model-property": ("m", model_form)}
        rows = [{"id": "PRF-1", "events": ["model-property"]}]
        with patch.object(reach_check, "theorem_forms", return_value=theorems), \
                patch.object(reach_check, "load_rows", return_value=rows):
            findings, hosted, unresolved = reach_check.audit(graph)
        self.assertEqual((findings, hosted, unresolved), ([], 1, []))
        self.assertEqual(graph.bridged, [("PRF-1", "model-property", "model",
                                         "concrete", "receiver-refines")])
        self.assertEqual(graph.reachable, {"concrete"})

        # With only an equality over changed input, the model stays orphaned.
        theorems["receiver-refines"] = ("b", self.BRIDGE.replace(
            "(model store records arena)", "(model other records arena)"))
        with patch.object(reach_check, "theorem_forms", return_value=theorems), \
                patch.object(reach_check, "load_rows", return_value=rows):
            findings, hosted, unresolved = reach_check.audit(graph)
        self.assertEqual(hosted, 0)
        self.assertEqual(len(findings), 1)
        self.assertEqual(graph.bridged, [])

    def test_identity_and_plain_field_selection_are_projections(self):
        for body in ("answer", "(car answer)", "(cons (car answer) (cdr answer))",
                     "(let* ((state (cadr answer)) (receiver (car state))) "
                     "(list (car answer) receiver))"):
            graph = self.graph(f"(defun result (answer) {body})")
            self.assertTrue(reach_check.structural_result_projection(graph, "result"), body)

    def test_nonprojections_cannot_host_the_model(self):
        bodies = (
            "nil", "(list nil nil)", "(car (cons nil answer))",
            "(let ((x (cons nil answer))) (car x))",
            "(+ 1 (car answer))", "(model answer)",
            "(if (equal (car answer) :ok) (cdr answer) nil)",
            "(if (consp answer) nil (car answer))",
            "(if (and (consp answer) (not (consp answer))) (car answer) nil)",
            "(list :ok (cdr answer))", "(quote (answer))",
        )
        for body in bodies:
            graph = self.graph(f"(defun result (answer) {body})")
            bridges = reach_check.equality_bridges(graph, {"bridge": ("b", self.BRIDGE)})
            self.assertNotIn(("concrete", "bridge"), bridges.get("model", []), body)
        for definition in ("(defmacro result (answer) `(car ,answer))",
                           "(defun result (answer other) (car answer))"):
            self.assertFalse(reach_check.structural_result_projection(
                self.graph(definition), "result"), definition)

    def test_changed_or_computed_inputs_and_unrelated_equalities_do_not_bridge(self):
        cases = (
            "(equal (result (concrete store records arena)) (model store other arena))",
            "(equal (result (concrete store records arena)) (model records store arena))",
            "(equal (result (concrete (model store records arena))) (model store records arena))",
            "(equal (result (concrete (cdr store) records arena)) (model (cdr store) records arena))",
            "(equal (result (concrete store records arena)) (model store records (concrete arena)))",
            "(equal (result (model store records arena)) (model store records arena))",
            "(equal (result (concrete store records arena)) (concrete store records arena))",
            "(equal (result (concrete)) (model))",
            "(equal (list (concrete store records arena)) (model store records arena))",
        )
        graph = self.graph()
        for conclusion in cases:
            bridges = reach_check.equality_bridges(graph, {"bridge": ("b", f"(defthm x {conclusion})")})
            self.assertNotIn(("concrete", "bridge"), bridges.get("model", []), conclusion)


class SharedGraphTests(unittest.TestCase):
    """reach_check reads definitions with tools/callgraph.py (the ledger's
    reader), so a comment or a docstring is never an edge."""

    @classmethod
    def setUpClass(cls):
        cls.graph = reach_check.Graph()

    def test_a_comment_is_not_a_call(self):
        """fn-feed-apply-record's comment names fn-feed-drivenp; before
        2026-09-28 that comment hosted PRF-335's prefix lemma."""
        self.assertIn("fn-feed-apply-record", self.graph.reachable)
        self.assertNotIn("fn-feed-drivenp", self.graph.edges["fn-feed-apply-record"])

    def test_a_macro_body_is_followed(self):
        """The generated dispatcher macro reaches the session arm via its term builder."""
        self.assertIn("fn-nntp-command-dispatch", self.graph.edges["fn-nntp-command"])
        # 6aa65979f moved the handwritten macro body into the table's
        # generator.  Both edges matter: merely finding the session arm
        # reachable would also pass if some unrelated host path reached it.
        self.assertIn("fn-proto-command-dispatch-term",
                      self.graph.edges["fn-nntp-command-dispatch"])
        self.assertIn("fn-nntp-session-command",
                      self.graph.edges["fn-proto-command-dispatch-term"])

    def test_the_host_chain_starts_at_a_host_line(self):
        chain = self.graph.host_chain("fn-nntp-session-command")
        self.assertTrue(chain)
        self.assertTrue(chain[0].startswith(("host/", "stobj ")), chain)
        self.assertEqual(chain[-1], "fn-nntp-session-command")
        self.assertEqual(self.graph.host_chain("fn-nntp-run-session"), [])


class DeclaredSubjectTests(unittest.TestCase):
    """A row's generated `keystone_subjects' (tools/keystone_emit.py, lane
    defkeystone) is the subject; the conclusion is not read."""

    @classmethod
    def setUpClass(cls):
        cls.graph = reach_check.Graph()

    def audit_rows(self, rows):
        saved = reach_check.load_rows
        reach_check.load_rows = lambda: rows
        try:
            return reach_check.audit(self.graph)
        finally:
            reach_check.load_rows = saved

    def test_a_declared_hosted_subject_hosts_whatever_the_conclusion_says(self):
        # The conclusion is about the unhosted trace model; the declared
        # subject is the hosted step, and it is what is checked.
        findings, hosted, unresolved = self.audit_rows([{
            "id": "PRF-T1", "events": ["fn-nntp-finite-trace-preserves-consistent-session"],
            "keystone_subjects": {"fn-nntp-finite-trace-preserves-consistent-session":
                                  "fn-nntp-session-command"}}])
        self.assertEqual((findings, hosted, unresolved), ([], 1, []))

    def test_a_declared_unhosted_subject_is_an_orphan(self):
        # fn-own-read-preserves-relation is hosted by inference; declaring the
        # model run its subject makes it an orphan naming that subject.
        findings, hosted, unresolved = self.audit_rows([{
            "id": "PRF-T2", "events": ["fn-own-read-preserves-relation"],
            "keystone_subjects": {"fn-own-read-preserves-relation": "fn-nntp-run-session"}}])
        self.assertEqual(hosted, 0)
        self.assertEqual([f.subjects for f in findings], [["fn-nntp-run-session"]])
        self.assertIn("declared subject", findings[0].render())

    def test_a_declared_subject_that_is_not_a_definition_is_unresolved(self):
        findings, hosted, unresolved = self.audit_rows([{
            "id": "PRF-T3", "events": ["fn-own-read-preserves-relation"],
            "keystone_subjects": {"fn-own-read-preserves-relation": "fn-no-such-function"}}])
        self.assertEqual((findings, hosted), ([], 0))
        self.assertEqual(unresolved[0][0], "PRF-T3")

    def test_a_row_without_the_map_is_inferred_as_before(self):
        findings, hosted, _ = self.audit_rows([{
            "id": "PRF-T4", "events": ["fn-own-read-preserves-relation"]}])
        self.assertEqual((findings, hosted), ([], 1))


class RatchetTests(unittest.TestCase):
    """The baseline may shrink and may not grow silently."""

    def run_check(self, *flags):
        return subprocess.run(
            [sys.executable, "tools/reach_check.py", *flags],
            cwd=ROOT, capture_output=True, text=True)

    def test_the_tree_is_at_its_baseline(self):
        done = self.run_check("--summary", "--strict")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("0 of them unbaselined", done.stdout)

    def test_an_unbaselined_orphan_fails_and_is_named(self):
        registry = ROOT / "planning" / "proofs.json"
        original = registry.read_text()
        planted = "fn-transfer-add-chunk-preserves-statep"
        try:
            loaded = json.loads(original)
            rows = loaded["proofs"] if isinstance(loaded, dict) else loaded
            rows[0]["events"] = list(rows[0].get("events", [])) + [planted]
            registry.write_text(json.dumps(loaded, indent=2) + "\n")
            done = self.run_check("--summary", "--strict")
            self.assertEqual(done.returncode, 1, done.stdout)
            self.assertIn("NEW unreachable subject", done.stdout)
            self.assertIn(planted, done.stdout)
        finally:
            registry.write_text(original)
        self.assertEqual(registry.read_text(), original)

    def test_every_baselined_orphan_carries_a_reason(self):
        baseline = json.loads(
            (ROOT / "planning" / "reach-baseline.json").read_text())
        self.assertTrue(baseline["accepted"])
        for key, reason in baseline["accepted"].items():
            self.assertGreater(len(reason), 40,
                               f"{key} is accepted without saying why")
        self.assertEqual(reach_check.unexplained(baseline["accepted"]), [])

    def test_a_placeholder_reason_is_untriaged(self):
        self.assertEqual(
            reach_check.unexplained({"PRF-1:x": "no host line reaches this subject and "
                                     + reach_check.PLACEHOLDER,
                                     "PRF-1:y": "SPEC: the model the hosted z refines",
                                     "PRF-1:w": "a reason with no disposition word"}),
            ["PRF-1:w", "PRF-1:x"])


class BinderStatementTests(unittest.TestCase):
    """A subject under a let*/mv-let (obstructions-2 item 13; the blind spot
    premise_audit fixed on lane/closure-theorems 4c08b2a63).  No tree read."""

    FORM = ("(defthm t2 (let* ((o (fn-open s))) (implies (fn-h o) (fn-r o))) "
            ":hints ((\"Goal\" :in-theory (enable fn-h))))")

    def test_the_binder_is_opened_and_the_hypothesis_is_assumed(self):
        hyps, conclusion = reach_check.split_statement(self.FORM)
        self.assertEqual(hyps, [["fn-h", ["fn-open", "s"]]])
        self.assertEqual(conclusion, ["fn-r", ["fn-open", "s"]])
        _, kept = reach_check.split_statement(self.FORM, keep_binders=True)
        self.assertEqual(kept, ["let*", [["o", ["fn-open", "s"]]], ["fn-r", "o"]])
        mv = "(defthm t3 (mv-let (a b) (fn-two x) (equal (fn-r b) a)))"
        self.assertEqual(reach_check.split_statement(mv)[1],
                         ["equal", ["fn-r", ["mv-nth", "1", ["fn-two", "x"]]],
                          ["mv-nth", "0", ["fn-two", "x"]]])

    def test_a_let_bound_subject_is_read_as_its_conclusion(self):
        graph = SimpleNamespace(book_defs={"fn-open": 1, "fn-h": 1, "fn-r": 1},
                                stobj_names=set(), export_of={},
                                reachable={"fn-r", "fn-open"})
        s = reach_check.Subject(graph, "t2", self.FORM)
        # fn-h is the hypothesis predicate, never the subject.
        self.assertEqual(s.functions, ["fn-open", "fn-r"])
        self.assertTrue(s.hosted(graph))
        # Over a bound model state (fn-open unreached) the hosted fn-r is a
        # statement about the model: the binders stay for that judgement.
        graph.reachable = {"fn-r"}
        self.assertFalse(reach_check.Subject(graph, "t2", self.FORM).hosted(graph))


class AbbreviationTests(unittest.TestCase):
    """PKT-376: an event stated over a proof-only abbreviation is about what
    the abbreviation names; a real (branching) model stays a model."""

    DEFS = {
        "fn-live": ("(defun fn-live (x) (declare (xargs :guard t :verify-guards nil))"
                    " (fn-store (fn-owner (fn-run x))))"),
        "fn-exec": "(defun fn-exec (x) (fn-store (fn-owner (fn-run x))))",
        "fn-seq": ("(defun-nx fn-seq (x) (let ((y (fn-owner x))) (fn-store y)))"),
        "fn-model": "(defun fn-model (x) (if (consp x) (fn-store x) nil))",
        "fn-livem": "(defmacro fn-livem (x) `(fn-store (fn-run ,x)))",
        "fn-store": "(defun fn-store (o) (car o))",
        "fn-owner": "(defun fn-owner (o) (cdr o))",
        "fn-check": "(defun fn-check (s) (consp s))",
        "fn-run": "(defun fn-run (x) (if (consp x) (fn-run (cdr x)) x))",
        "fn-indexedp": "(defun fn-indexedp (s) (if (consp s) (fn-indexedp (cdr s)) t))",
    }

    def graph(self):
        graph = reach_check.Graph.__new__(reach_check.Graph)
        graph.book_defs = {n: ("books/x.lisp", f) for n, f in self.DEFS.items()}
        graph.stobj_names, graph.export_of = {"state"}, {}
        graph.reachable = {"fn-store", "fn-owner", "fn-check"}
        return graph

    def hosted(self, form):
        graph = self.graph()
        return reach_check.Subject(graph, "t", form).hosted(graph)

    def test_an_event_over_an_abbreviation_is_about_what_it_names(self):
        self.assertTrue(self.hosted("(defthm t (fn-indexedp (fn-live x)))"))
        self.assertTrue(self.hosted("(defthm t (fn-indexedp (fn-livem x)))"))

    def test_a_branching_definition_is_not_an_abbreviation(self):
        graph = self.graph()
        self.assertIsNone(graph.abbreviation("fn-model"))
        self.assertIsNone(graph.abbreviation("fn-run"), "recursive")
        self.assertIsNone(graph.abbreviation("fn-store"), "reached: a function, not a proof abbreviation")
        self.assertIsNone(graph.abbreviation("fn-exec"), "executable: the host could call it")
        self.assertIsNone(graph.abbreviation("fn-seq"), "a binder sequences work (fn-sca-load-history)")
        self.assertIsNotNone(graph.abbreviation("fn-live"))
        self.assertFalse(self.hosted("(defthm t (fn-indexedp (fn-model x)))"))

    def test_a_bound_abbreviation_is_a_model_only_when_what_it_names_is(self):
        self.assertTrue(self.hosted("(defthm t (let ((o (fn-live x))) (fn-check o)))"))
        self.assertFalse(self.hosted("(defthm t (let ((o (fn-model x))) (fn-check o)))"))


class LoadedHostTests(unittest.TestCase):
    """PKT-412: a host file no image build loads is not a host line."""

    def test_only_what_a_build_loads_is_a_host_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host/native/build.lisp").write_text(
                '(ld "host/a-host.lisp" :ld-error-action :error)\n'
                '; (ld "host/commented-host.lisp")\n'
                '(progn! (set-raw-mode t) (load "host/native/io.lisp"))\n')
            (root / "host/a-host.lisp").write_text('(ld "b-host.lisp")\n(defun a () 1)\n')
            (root / "host/b-host.lisp").write_text("(defun b () 2)\n")
            (root / "host/commented-host.lisp").write_text("(defun c () 3)\n")
            (root / "host/unloaded-host.lisp").write_text("(defun u () 4)\n")
            (root / "host/native/io.lisp").write_text(
                '(load (merge-pathnames "digest.lisp" *load-truename*))\n')
            (root / "host/native/digest.lisp").write_text("(defun d () 5)\n")
            self.assertEqual(reach_check.loaded_host_files(("host/native/build.lisp",), root),
                             {"host/native/build.lisp", "host/a-host.lisp", "host/b-host.lisp",
                              "host/native/io.lisp", "host/native/digest.lisp"})

    def test_a_build_run_from_its_own_directory_resolves_there(self):
        # The extraction world (tools/extract/world-host.lisp) runs from
        # tools/extract and names `../../host/...' (Q7k).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host").mkdir()
            (root / "tools/extract").mkdir(parents=True)
            (root / "tools/extract/world-host.lisp").write_text(
                '(ld "../../host/port-host.lisp" :ld-error-action :error)\n')
            (root / "host/port-host.lisp").write_text("(defun p () 1)\n")
            self.assertEqual(
                reach_check.loaded_host_files({"tools/extract/world-host.lisp": "tools/extract"}, root),
                {"tools/extract/world-host.lisp", "host/port-host.lisp"})
            self.assertEqual(
                reach_check.loaded_host_files(("tools/extract/world-host.lisp",), root),
                {"tools/extract/world-host.lisp"})

    def test_a_book_symbol_mentioned_only_by_python_is_an_orphan(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "tools").mkdir()
            (root / "host/native").mkdir(parents=True)
            (root / "host/native/build.lisp").write_text(
                '(ld "host/live.lisp")\n')
            (root / "host/live.lisp").write_text(
                '(defun host-live (x) (fn-live x))\n')
            (root / "books/x.lisp").write_text(
                '(defun fn-live (x) x)\n'
                '(defun fn-python-only (x) (cons x x))\n'
                '(defthm python-only-property (consp (fn-python-only x)))\n')
            (root / "tools/x.py").write_text('SYMBOL = "fn-python-only"\n')
            rows = [{"id": "PRF-T1", "events": ["python-only-property"]}]
            loaded = reach_check.loaded_host_files(root=root)
            with patch.object(reach_check, "ROOT", root), \
                    patch.object(reach_check, "loaded_host_files", return_value=loaded), \
                    patch.object(reach_check, "load_rows", return_value=rows):
                graph = reach_check.Graph()
                self.assertIn("fn-live", graph.reachable)
                self.assertIn("fn-python-only", graph.book_defs)
                self.assertNotIn("fn-python-only", graph.reachable)
                findings, hosted, unresolved = reach_check.audit(graph)
            self.assertEqual((hosted, unresolved), (0, []))
            self.assertEqual([f.key() for f in findings],
                             ["PRF-T1:python-only-property"])
            self.assertEqual(findings[0].subjects, ["fn-python-only"])

    def test_the_extraction_worlds_ports_are_host_lines(self):
        graph = reach_check.Graph()
        self.assertIn("host/store-open-host.lisp", graph.loaded_hosts)
        self.assertIn("host/owner-host.lisp", graph.loaded_hosts)
        self.assertNotIn("host/native/build-store-test.lisp", graph.loaded_hosts)

if __name__ == "__main__":
    unittest.main()

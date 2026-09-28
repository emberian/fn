"""tools/reach_check.py: the orphan it reports must be a real orphan.

A gate that cries wolf gets switched off.  These tests pin the two things
that would make this one lie: a function the host demonstrably calls must
never be reported unreachable, and a function named nowhere outside the
books must never be reported hosted.
"""
import json
import subprocess
import sys
import tempfile
import unittest
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

    def test_the_bridges_count_as_host_lines(self):
        """tools/run_owner.py drives the owner by building ACL2 forms as
        text. A symbol named only there is still called by the host."""
        self.assertGreater(self.graph.seeds["bridge"], 0)


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

    def test_this_checker_is_not_a_bridge(self):
        self.assertNotIn(Path(reach_check.__file__).resolve(),
                         [p.resolve() for p in self.graph.bridges])


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
        codec is hosted now (compressed extents), so the witness is the
        NNTP trace model: its hypothesis `fn-nntp-session-consistentp' is
        hosted, its subject `fn-nntp-run-session' is not."""
        self.assertIn("fn-nntp-session-consistentp", self.graph.reachable)
        self.assertNotIn("fn-nntp-run-session", self.graph.reachable)
        s = self.subject("fn-nntp-finite-trace-preserves-consistent-session")
        self.assertNotIn("fn-nntp-session-consistentp", s.functions)
        self.assertIn("fn-nntp-run-session", s.functions)
        self.assertFalse(s.hosted(self.graph))

    def test_hints_do_not_host(self):
        form = ("(defthm t1 (equal (fn-nntp-run-session s evs) c) "
                ":hints ((\"Goal\" :use ((:instance fn-own-read-preserves-relation)) "
                ":in-theory (enable fn-own-read))))")
        s = reach_check.Subject(self.graph, "t1", form)
        self.assertEqual(s.functions, ["fn-nntp-run-session"])
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
        """fn-nntp-command's arms are named only by the dispatcher macro."""
        self.assertIn("fn-nntp-command-dispatch", self.graph.edges["fn-nntp-command"])
        self.assertIn("fn-nntp-session-command", self.graph.edges["fn-nntp-command-dispatch"])

    def test_the_host_chain_starts_at_a_host_line(self):
        chain = self.graph.host_chain("fn-nntp-session-command")
        self.assertTrue(chain)
        self.assertTrue(chain[0].startswith(("host/", "tools/", "stobj ")), chain)
        self.assertEqual(chain[-1], "fn-nntp-session-command")
        self.assertEqual(self.graph.host_chain("fn-nntp-run-session"), [])


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


if __name__ == "__main__":
    unittest.main()

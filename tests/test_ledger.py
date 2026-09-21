"""Unit checks for the generated ledger: the reader and the suspect detector.

Every fixture below is a small inline book.  The point of the negative cases is
that the detector must not flag an ordinary induction, and the point of the
positive cases is that it must flag the exact shapes the 2026-09-18 review
named.  A detector that flagged everything would be as useless as one that
flagged nothing.
"""

import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location(
    "ledger", Path(__file__).resolve().parents[1] / "tools" / "ledger.py"
)
ledger = importlib.util.module_from_spec(SPEC)
# Register before executing: the module defines dataclasses, and `dataclass`
# resolves annotations through sys.modules.
sys.modules["ledger"] = ledger
SPEC.loader.exec_module(ledger)


def tree_from(sources: dict[str, str], roots: list[str] | None = None) -> ledger.Tree:
    """A Tree over inline sources, with no filesystem and no ACL2.

    A source under `books/` or `tests/acl2/` is read as a book; anything else
    is read as a host file, which is the same rule `ledger.host_paths` applies
    to the repository.
    """
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        books, hosts = {}, {}
        for relative, text in sources.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            if relative.startswith(("books/", "tests/acl2/")):
                books[relative] = ledger.analyze_book(path, relative)
            else:
                hosts[relative] = ledger.analyze_host(path, relative)
    return ledger.Tree(books, roots if roots is not None else
                       [relative[:-5] for relative in sources
                        if relative.startswith(("books/", "tests/acl2/"))],
                       hosts)


class ReaderTests(unittest.TestCase):
    def test_comments_strings_and_block_comments_are_not_code(self):
        forms = ledger.read_forms('''
            ; (defthm commented-out nil)
            #| (defthm blocked nil) #| nested |# still-blocked |#
            (defconst *help* "(defthm in-a-string nil)")
            (defthm real (equal x x))
        ''')
        self.assertEqual([ledger.head(form) for form in forms],
                         ["defconst", "defthm"])
        self.assertIsInstance(forms[0][2], str)
        self.assertNotIsInstance(forms[0][2], ledger.Sym)

    def test_symbols_and_string_literals_stay_distinct(self):
        forms = ledger.read_forms('(f "abc" abc)')
        self.assertIsInstance(forms[0][1], str)
        self.assertNotIsInstance(forms[0][1], ledger.Sym)
        self.assertIsInstance(forms[0][2], ledger.Sym)
        self.assertFalse(ledger.same(forms[0][1], forms[0][2]))

    def test_quote_character_and_dotted_forms_read(self):
        forms = ledger.read_forms("(a '(1 . 2) #\\Space `(x ,y) 3/4 -2.5)")
        self.assertEqual(ledger.head(forms[0][1]), "quote")
        self.assertEqual(str(forms[0][2]), "#\\Space")
        self.assertEqual(ledger.head(forms[0][3]), "quasiquote")
        self.assertEqual(forms[0][5], -2.5)

    def test_bar_escaped_symbol_keeps_its_spelling(self):
        forms = ledger.read_forms("(|Weird Symbol| plain)")
        self.assertEqual(str(forms[0][0]), "weird symbol")

    def test_unbalanced_source_is_an_error_not_a_guess(self):
        with self.assertRaises(ledger.ReadError):
            ledger.read_forms("(defthm x (equal 1 1)")
        with self.assertRaises(ledger.ReadError):
            ledger.read_forms("(a) )")


class EventTests(unittest.TestCase):
    BOOK = '''(in-package "ACL2")
        (include-book "other")
        (include-book "std/testing/must-fail" :dir :system)
        (defun f (x) (declare (xargs :guard t :verify-guards nil)) (cons x x))
        (verify-guards f)
        (defun g (x) (declare (xargs :guard t)) x)
        (defun h (x) x)
        (defun k (x) (declare (xargs :guard t :verify-guards nil)) x)
        (defthm f-is-a-cons (consp (f x)))
        (local (defthm helper (equal (g x) x)))
        (assert-event (equal (f 1) '(1 . 1)))
        (local (must-fail (defthm never (equal (f 1) 2))))
    '''

    def setUp(self):
        self.tree = tree_from({"books/a.lisp": self.BOOK})
        self.book = self.tree.books["books/a.lisp"]

    def test_events_are_counted_per_book(self):
        self.assertEqual(sorted(t.name for t in self.book.theorems),
                         ["f-is-a-cons", "helper"])
        self.assertEqual(sorted(f.name for f in self.book.functions),
                         ["f", "g", "h", "k"])
        self.assertEqual(self.book.assert_events, 1)
        self.assertEqual(self.book.must_fails, 1)
        self.assertEqual(self.book.includes, ["other"])
        self.assertEqual(self.book.system_includes, ["std/testing/must-fail"])

    def test_a_theorem_inside_must_fail_is_not_a_theorem(self):
        self.assertNotIn("never", self.tree.theorems)

    def test_guard_status_distinguishes_four_states(self):
        states = {f.name: f.guard_status for f in self.book.functions}
        self.assertEqual(states, {"f": "verified", "g": "default-guarded",
                                  "h": "default-unguarded", "k": "declared-off"})

    def test_a_local_witness_is_not_a_definition(self):
        tree = tree_from({"books/a.lisp": '''(in-package "ACL2")
            (encapsulate (((c *) => *))
              (local (defun c (x) x))
              (defthm c-is-identity (equal (c x) x)))
        '''})
        self.assertEqual(tree.books["books/a.lisp"].encapsulates, 1)
        self.assertNotIn("c", tree.functions)
        self.assertEqual(tree.suspects, {})


class SuspectTests(unittest.TestCase):
    def flags(self, source: str) -> dict[str, list[str]]:
        return tree_from({"books/a.lisp": '(in-package "ACL2")\n' + source}).suspects

    # -- must be flagged ------------------------------------------------

    def test_closed_theory_corollary_is_flagged(self):
        flagged = self.flags('''
            (defun step (s) (cons s s))
            (defun inv (s) (consp s))
            (defthm step-preserves-state (inv (step s)))
            (defthm state-has-consp (implies (inv s) (consp s)))
            (defthm derived (consp (step s))
              :hints (("Goal" :in-theory '(step-preserves-state state-has-consp))))
        ''')
        self.assertIn("derived", flagged)
        self.assertTrue(any("closed-theory-corollary" in r for r in flagged["derived"]))

    def test_instance_corollary_is_flagged(self):
        flagged = self.flags('''
            (defun step (s) (cons s s))
            (defun inv (s) (consp s))
            (defthm base (implies (inv s) (consp s)))
            (defthm derived (implies (inv s) (consp s))
              :hints (("Goal" :use ((:instance base (s s))))))
        ''')
        self.assertTrue(any("instance-corollary" in r for r in flagged["derived"]))

    def test_reflexive_conclusion_is_flagged_through_one_unfolding(self):
        flagged = self.flags('''
            (defun build (xs) (cons xs xs))
            (defun completep (index xs) (subsetp (build xs) index))
            (defthm build-complete (completep (build xs) xs))
        ''')
        self.assertTrue(any("reflexive-conclusion" in r
                            for r in flagged["build-complete"]))

    def test_definition_restated_under_its_own_hypotheses_is_flagged(self):
        flagged = self.flags('''
            (defun idp (x) (stringp x))
            (defun id-equalp (a b) (and (idp a) (idp b) (equal a b)))
            (defthm id-equalp-is-exact
              (implies (and (idp a) (idp b))
                       (equal (id-equalp a b) (equal a b))))
        ''')
        self.assertTrue(any("definition-restated" in r
                            for r in flagged["id-equalp-is-exact"]))

    def test_branch_of_definition_is_flagged_through_a_let(self):
        flagged = self.flags('''
            (defun matchesp (pin e) (equal (cdr pin) e))
            (defun release (s id e)
              (let ((pin (assoc id s)))
                (if (matchesp pin e) (remove1-equal pin s) s)))
            (defthm wrong-evidence-does-not-release
              (implies (not (matchesp (assoc id s) e))
                       (equal (release s id e) s)))
        ''')
        self.assertTrue(any("branch-of-definition" in r
                            for r in flagged["wrong-evidence-does-not-release"]))

    def test_preserves_name_with_no_subject_call_is_flagged(self):
        flagged = self.flags('''
            (defun rotate (s) (cons s s))
            (defun inv (s) (consp s))
            (defthm rotate-preserves-inv (implies (inv s) (inv (cons s s))))
        ''')
        self.assertTrue(any("preserves-no-subject-call" in r
                            for r in flagged["rotate-preserves-inv"]))

    # -- must not be flagged --------------------------------------------

    def test_an_ordinary_induction_is_not_flagged(self):
        flagged = self.flags('''
            (defun listp2 (xs) (if (consp xs) (listp2 (cdr xs)) (null xs)))
            (defun app (xs ys) (if (consp xs) (cons (car xs) (app (cdr xs) ys)) ys))
            (defthm app-preserves-listp2
              (implies (and (listp2 xs) (listp2 ys)) (listp2 (app xs ys)))
              :hints (("Goal" :induct (app xs ys))))
        ''')
        self.assertEqual(flagged, {})

    def test_a_branch_hypothesis_with_real_content_is_not_flagged(self):
        """The hypothesis is the branch test, but the conclusion is a fact
        about the result, not the branch's value restated."""
        flagged = self.flags('''
            (defun okp (s b) (and (consp s) (consp b)))
            (defun ingest (s b) (if (okp s b) (cons b s) s))
            (defthm admitted-ingest-member
              (implies (okp s b) (member-equal b (ingest s b))))
        ''')
        self.assertEqual(flagged, {})

    def test_an_instance_that_discharges_a_hypothesis_is_not_flagged(self):
        flagged = self.flags('''
            (defun step (s) (cons s s))
            (defun inv (s) (consp s))
            (defthm base (implies (inv s) (consp s)))
            (defthm derived (implies (inv s) (consp (step s)))
              :hints (("Goal" :use ((:instance base (s (step s)))))))
        ''')
        # `base' itself restates the recognizer body and is rightly flagged;
        # `derived' discharges base's hypothesis at a new state and is not.
        self.assertNotIn("derived", flagged)

    def test_constant_propagation_trivia_is_not_a_vacuous_theorem(self):
        """`(equal t t)` appearing because a call site passes a literal is a
        finding about the call site, not a vacuous theorem."""
        flagged = self.flags('''
            (defun acceptablep (r authorized) (and (consp r) (equal authorized t)))
            (defthm accepted-record-is-a-cons
              (implies (acceptablep r t) (consp r)))
        ''')
        self.assertEqual(flagged, {})


class RegistryTests(unittest.TestCase):
    SOURCES = {
        "books/a.lisp": '''(in-package "ACL2")
            (defun f (x) (declare (xargs :guard t :verify-guards nil)) (cons x x))
            (verify-guards f)
            (defun unguarded (x) x)
            (defthm f-is-a-cons (consp (f x)))
            (defthm f-subset-self (subsetp (f x) (f x)))
        ''',
        "books/orphan.lisp": '''(in-package "ACL2")
            (defthm orphan-fact (equal (cons 1 2) (cons 1 2)))
        ''',
    }

    def setUp(self):
        self.tree = tree_from(self.SOURCES, roots=["books/a"])

    def curated(self, events):
        return {"schema_version": 1, "targets": [{"id": "PRF-001", "events": events}]}

    def validate(self, events):
        registry = {"proofs": [{"id": "PRF-001", "title": "t", "events": []}]}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "proofs.json"
            path.write_text(json.dumps(registry))
            with mock.patch.object(ledger, "PROOFS", path):
                return ledger.validate_events(self.tree, self.curated(events))

    def test_a_good_citation_passes_and_regenerates(self):
        problems, regenerated = self.validate([{"name": "f-is-a-cons", "kind": "theorem"}])
        self.assertEqual(problems, [])
        self.assertEqual(regenerated["PRF-001"], ["f-is-a-cons"])

    def test_an_unknown_theorem_name_fails(self):
        problems, _ = self.validate([{"name": "no-such-theorem", "kind": "theorem"}])
        self.assertTrue(any("no such theorem" in p for p in problems))

    def test_a_suspect_theorem_may_not_be_cited(self):
        problems, _ = self.validate([{"name": "f-subset-self", "kind": "theorem"}])
        self.assertTrue(any("SUSPECT" in p for p in problems))

    def test_a_theorem_outside_the_root_closure_fails(self):
        problems, _ = self.validate([{"name": "orphan-fact", "kind": "theorem"}])
        self.assertTrue(any("certification root" in p for p in problems))

    def test_a_cited_function_must_have_verified_guards(self):
        problems, _ = self.validate([{"name": "f", "kind": "guarded-function"}])
        self.assertEqual(problems, [])
        problems, _ = self.validate([{"name": "unguarded", "kind": "guarded-function"}])
        self.assertTrue(any("guard status" in p for p in problems))


class RepositoryLedgerTests(unittest.TestCase):
    """The real tree: the shipped ledger must be current and the cited events
    must pass the same checks the fixtures above describe."""

    def test_the_checked_in_ledger_is_current(self):
        self.assertEqual(ledger.check_problems(), [])

    def test_every_named_assumption_has_an_encapsulate(self):
        failures = (ledger.ROOT / "specs/failures.md").read_text()
        named = set(re.findall(r"(?m)^\| (A-[A-Z-]+) \|", failures))
        book = (ledger.ROOT / "books/assumptions.lisp").read_text()
        # A-CRYPTO lives in the crypto seam, not here; see the book header.
        for assumption in sorted(named - {"A-CRYPTO"}):
            self.assertIn(assumption, book, f"{assumption} has no encapsulate")


if __name__ == "__main__":
    unittest.main()


class ExportHygieneLintTests(unittest.TestCase):
    """What a book leaves enabled, judged by shape only."""

    ACCESSOR = '''(in-package "ACL2")
(defun fn-ag-car (x) (if (consp x) (car x) nil))
(defthm fn-ag-car-is-car (equal (fn-ag-car x) (car x)))
'''

    def findings(self, source: str) -> list[dict]:
        return ledger.export_hygiene(tree_from({"books/b.lisp": source}))

    def test_an_enabled_equality_between_two_different_accessors_is_flagged(self):
        found = self.findings(self.ACCESSOR)
        self.assertEqual([entry["theorem"] for entry in found], ["fn-ag-car-is-car"])
        self.assertIn("accessor-equality", found[0]["reason"])

    def test_a_preservation_lemma_in_one_vocabulary_is_not_flagged(self):
        # The same accessor on both sides keeps the goal in accessor form:
        # this is the shape the discipline asks for, not a finding.
        self.assertEqual(self.findings('''(in-package "ACL2")
(defun fn-articles (s) (car s))
(defthm fn-prepare-does-not-publish
  (implies (fn-statep s)
           (equal (fn-articles (fn-prepare s)) (fn-articles s))))
'''), [])

    def test_rule_classes_nil_local_and_defthmd_all_exempt(self):
        header = '(in-package "ACL2")\n(defun fn-ag-car (x) (if (consp x) (car x) nil))\n'
        claim = "(equal (fn-ag-car x) (car x))"
        for variant in (
                f"(defthm fn-ag-car-is-car {claim} :rule-classes nil)",
                f"(local (defthm fn-ag-car-is-car {claim}))",
                f"(defthmd fn-ag-car-is-car {claim})"):
            self.assertEqual(self.findings(header + variant + "\n"), [], variant)

    def test_a_closing_in_theory_disable_exempts_the_rule(self):
        for closing in ("(in-theory (disable fn-ag-car-is-car))",
                        "(in-theory (disable (:rewrite fn-ag-car-is-car)))",
                        "(in-theory (e/d (fn-ag-car) (fn-ag-car-is-car)))"):
            self.assertEqual(self.findings(self.ACCESSOR + closing), [], closing)
        # A `local' disable does not change what the book exports.
        self.assertEqual(len(self.findings(
            self.ACCESSOR + "(local (in-theory (disable fn-ag-car-is-car)))")), 1)

    def test_a_theory_name_withdrawn_at_the_end_of_the_book_exempts_its_rules(self):
        # The shape three deputies use: name the helpers once, withdraw the
        # name.  Reading only the disable would count every helper as exported.
        withdrawn = self.ACCESSOR + """(deftheory fn-ag-vocabulary
  '(fn-ag-car-is-car))
(in-theory (disable fn-ag-vocabulary))
"""
        self.assertEqual(self.findings(withdrawn), [])
        # Defining the theory and never disabling it withdraws nothing.
        defined_only = self.ACCESSOR + """(deftheory fn-ag-vocabulary
  '(fn-ag-car-is-car))
"""
        self.assertEqual([entry["theorem"] for entry in self.findings(defined_only)],
                         ["fn-ag-car-is-car"])

    def test_rune_forms_and_theory_algebra_resolve_too(self):
        for closing in (
                "(deftheory v '((:rewrite fn-ag-car-is-car)))\n"
                "(in-theory (disable v))",
                "(deftheory v '((:d fn-ag-car) (:e fn-ag-car) fn-ag-car-is-car))\n"
                "(in-theory (disable v))",
                "(deftheory inner '(fn-ag-car-is-car))\n"
                "(deftheory outer (union-theories (theory 'inner) '(fn-ag-car)))\n"
                "(in-theory (disable outer))",
                "(deftheory v '(fn-ag-car-is-car))\n"
                "(in-theory (set-difference-theories (current-theory :here) "
                "(theory 'v)))",
                "(deftheory v '(fn-ag-car-is-car))\n"
                "(in-theory (e/d (fn-ag-car) (v)))"):
            self.assertEqual(self.findings(self.ACCESSOR + closing + "\n"), [],
                             closing)

    def test_a_theory_that_does_not_name_the_rule_still_leaves_it_enabled(self):
        closing = ("(deftheory v '(fn-ag-cdr-is-cdr))\n"
                   "(in-theory (disable v))\n")
        self.assertEqual([entry["theorem"] for entry in
                          self.findings(self.ACCESSOR + closing)],
                         ["fn-ag-car-is-car"])

    def test_len_backchaining_conclusions_are_flagged(self):
        found = self.findings('''(in-package "ACL2")
(defthm consp-from-len (implies (< 0 (len x)) (consp x)))
(defthm len-from-len (implies (equal (len x) 3) (equal (len (cdr x)) 2)))
(defthm unrelated (implies (consp x) (equal (car (cons a x)) a)))
''')
        self.assertEqual([entry["theorem"] for entry in found],
                         ["consp-from-len", "len-from-len"])
        self.assertTrue(all("len-backchaining" in entry["reason"] for entry in found))


class EnabledProjectionLintTests(unittest.TestCase):
    """An accessor shipped enabled while other books reason over it."""

    # The shape the tree actually uses: `mbe` around a walk into one formal.
    OWNER = '''(in-package "ACL2")
(defun fn-ep-result-effects (x)
  (mbe :logic (cadr x) :exec (cadr x)))
'''
    USER = '''(in-package "ACL2")
(include-book "owner")
(defthm fn-ep-effects-well-formed
  (implies (fn-ep-resultp r) (fn-ep-effectsp (fn-ep-result-effects r))))
'''

    def findings(self, owner: str, **rest: str) -> list[dict]:
        books = {"books/owner.lisp": owner}
        books.update({name: text for name, text in rest.items()})
        return ledger.enabled_projection(tree_from(books))

    def test_an_enabled_projection_another_book_reasons_over_is_flagged(self):
        found = self.findings(self.OWNER, **{"books/user.lisp": self.USER})
        self.assertEqual([entry["function"] for entry in found],
                         ["fn-ep-result-effects"])
        self.assertEqual(found[0]["stated_in"], ["books/user.lisp"])
        self.assertIn("enabled-projection", found[0]["reason"])
        self.assertIn("1 book states", found[0]["reason"])

    def test_a_projection_its_own_book_withdraws_is_not_flagged(self):
        withdrawn = self.OWNER + """(deftheory fn-ep-vocabulary
  '(fn-ep-result-effects))
(in-theory (disable fn-ep-vocabulary))
"""
        self.assertEqual(
            self.findings(withdrawn, **{"books/user.lisp": self.USER}), [])
        # And by name, without the theory.
        self.assertEqual(
            self.findings(self.OWNER + "(in-theory (disable fn-ep-result-effects))",
                          **{"books/user.lisp": self.USER}), [])

    def test_a_projection_nothing_else_states_a_theorem_over_is_not_flagged(self):
        """An accessor no other book reasons over costs nobody anything."""
        self.assertEqual(self.findings(self.OWNER), [])
        # Its own book's theorems do not count: the book chooses its own
        # vocabulary and pays its own bill.
        self.assertEqual(self.findings(
            self.OWNER + "(defthm fn-ep-here (equal (fn-ep-result-effects x) (cadr x)))"),
            [])

    def test_a_function_that_computes_is_not_a_projection(self):
        """The lint is about names whose whole content is WHERE a value is."""
        for body in ("(+ 1 (car x))", "(fn-ep-helper (car x))",
                     "(if (consp x) (car x) nil)", "(append (car x) (cdr x))"):
            owner = '(in-package "ACL2")\n(defun fn-ep-result-effects (x) {})\n'.format(body)
            self.assertEqual(
                self.findings(owner, **{"books/user.lisp": self.USER}), [], body)

    def test_a_projection_of_more_than_one_argument_is_not_flagged(self):
        owner = ('(in-package "ACL2")\n'
                 '(defun fn-ep-result-effects (x y) (cadr (cons x y)))\n')
        self.assertEqual(
            self.findings(owner, **{"books/user.lisp": self.USER}), [])

    def test_the_warning_and_the_ledger_carry_the_finding(self):
        tree = tree_from({"books/owner.lisp": self.OWNER,
                          "books/user.lisp": self.USER})
        warnings = [line for line in ledger.lint_warnings(tree)
                    if line.startswith("enabled projection:")]
        self.assertEqual(len(warnings), 1)
        self.assertTrue(warnings[0].startswith(
            "enabled projection: books/owner.lisp:2: fn-ep-result-effects:"),
            warnings[0])
        self.assertIn("books/user.lisp", warnings[0])
        data = ledger.build_ledger(tree)
        self.assertEqual(data["totals"]["enabled_projection_warnings"], 1)
        self.assertIn("Enabled-projection warnings | 1",
                      ledger.ledger_markdown(data))


class TeethFormLintTests(unittest.TestCase):
    """A must-fail earns its name by naming a value."""

    def findings(self, source: str) -> list[dict]:
        return ledger.teeth_form(tree_from({"tests/acl2/t.lisp": source}))

    def test_a_bare_general_claim_is_flagged(self):
        found = self.findings('''(in-package "ACL2")
(must-fail (thm (implies (and (fn-inputsp fs n) (fn-coverp fs)) (fn-agreep fs))))
''')
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0]["check"], "thm")
        self.assertIn("bare-general-claim", found[0]["reason"])

    def test_a_must_fail_naming_a_value_is_not_flagged(self):
        for witness in ("(must-fail (thm (equal (fn-check :indeterminate) :success)))",
                        "(must-fail (thm (equal (fn-len '(1 2)) 3)))",
                        "(must-fail (defthm d (equal (fn-parse *fn-sample*) nil)))",
                        '(must-fail (thm (equal (fn-parse "abc") nil)))'):
            self.assertEqual(self.findings('(in-package "ACL2")\n' + witness), [],
                             witness)

    def test_a_keyword_option_is_not_a_witness(self):
        found = self.findings('''(in-package "ACL2")
(must-fail (defthm general (implies (fn-p x) (fn-q x)) :rule-classes nil)
           :with-output-off nil)
''')
        self.assertEqual([entry["check"] for entry in found], ["general"])

    def test_a_must_fail_around_something_other_than_a_theorem_is_not_judged(self):
        self.assertEqual(self.findings('''(in-package "ACL2")
(must-fail (defun f (x) (car x)))
'''), [])


class IncludeHygieneLintTests(unittest.TestCase):
    """A non-local include of a book that withdraws nothing re-exports it all.

    The measured case: `books/bp-ingress.lisp` took a non-local include of
    `article-properties` for one guard hint, which enabled every rule of that
    book in the ingress proof and turned six minutes into an 1800 s timeout.
    """

    OPEN = '(in-package "ACL2")\n(defthm fn-open-shape (equal (fn-ag-car x) (car x)))\n'
    CLOSED = ('(in-package "ACL2")\n'
              '(defthm fn-closed-shape (equal (fn-cl-car x) (car x)))\n'
              '(in-theory (disable fn-closed-shape))\n')

    def findings(self, includer: str) -> list[dict]:
        return ledger.include_hygiene(tree_from({
            "books/open.lisp": self.OPEN,
            "books/closed.lisp": self.CLOSED,
            "books/includer.lisp": includer,
        }))

    def test_a_non_local_include_of_a_book_with_no_export_theory_is_flagged(self):
        found = self.findings('(in-package "ACL2")\n(include-book "open")\n')
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0]["book"], "books/includer.lisp")
        self.assertEqual(found[0]["included"], "books/open.lisp")
        self.assertEqual(found[0]["line"], 2)
        self.assertIn("re-export", found[0]["reason"])

    def test_the_same_include_made_local_is_clean(self):
        self.assertEqual(
            self.findings('(in-package "ACL2")\n(local (include-book "open"))\n'), [])

    def test_including_a_book_that_withdraws_on_exit_is_clean(self):
        self.assertEqual(
            self.findings('(in-package "ACL2")\n(include-book "closed")\n'), [])

    def test_a_system_book_and_an_unresolvable_path_are_not_judged(self):
        self.assertEqual(self.findings('(in-package "ACL2")\n'
                                       '(include-book "std/lists/top" :dir :system)\n'
                                       '(include-book "no-such-book")\n'), [])

    def test_a_relative_include_resolves_to_the_book_it_names(self):
        found = ledger.include_hygiene(tree_from({
            "books/open.lisp": self.OPEN,
            "tests/acl2/t.lisp": '(in-package "ACL2")\n'
                                 '(include-book "../../books/open")\n',
        }))
        self.assertEqual([entry["included"] for entry in found], ["books/open.lisp"])


class HostNamesLintTests(unittest.TestCase):
    """The fourth lint, over the files no certification reads.

    `host/*.lisp` is `ld`ed by a bridge at start-up, so an undefined name in
    it is found by the bridge dying: `host/checkpoint-host.lisp` named
    `*fn-store-groups*` after the compiled group table deleted it, and every
    `Acl2Store` constructor failed with a Translate error.
    """

    BOOK = ('(in-package "ACL2")\n'
            '(defconst *fn-store-capacity* 8)\n'
            '(defun fn-store-decode (x) x)\n')

    def findings(self, host: str) -> list[dict]:
        return ledger.host_names(tree_from({
            "books/store.lisp": self.BOOK,
            "host/h.lisp": host,
        }))

    def test_a_deleted_defconst_is_flagged(self):
        found = self.findings('(in-package "ACL2")\n'
                              '(include-book "../books/store")\n'
                              '(defun fn-host-capacity () *fn-store-groups*)\n')
        self.assertEqual([entry["name"] for entry in found], ["*fn-store-groups*"])
        self.assertEqual(found[0]["host"], "host/h.lisp")
        self.assertEqual(found[0]["line"], 3)
        self.assertIsNone(found[0]["source"])
        self.assertIn("undefined", found[0]["reason"])

    def test_a_name_from_an_included_book_is_clean(self):
        self.assertEqual(self.findings(
            '(in-package "ACL2")\n'
            '(include-book "../books/store")\n'
            '(defun fn-host-decode (x) (fn-store-decode x))\n'
            '(defun fn-host-capacity () *fn-store-capacity*)\n'), [])

    def test_an_acl2_builtin_from_the_allowlist_is_clean(self):
        self.assertIn("f-put-global", ledger.acl2_builtins())
        self.assertEqual(self.findings(
            '(in-package "ACL2")\n'
            "(defun fn-host-note (state) (f-put-global 'fn-host-note 1 state))\n"), [])

    def test_a_name_defined_in_a_host_file_this_one_does_not_load_is_named(self):
        found = ledger.host_names(tree_from({
            "host/a.lisp": '(in-package "ACL2")\n(defun fn-a () 1)\n',
            "host/b.lisp": '(in-package "ACL2")\n(defun fn-b () (fn-a))\n',
        }))
        self.assertEqual([(e["host"], e["name"], e["source"]) for e in found],
                         [("host/b.lisp", "fn-a", "host/a.lisp")])

    def test_an_ld_of_the_defining_host_file_is_clean(self):
        self.assertEqual(ledger.host_names(tree_from({
            "host/a.lisp": '(in-package "ACL2")\n(defun fn-a () 1)\n',
            "host/b.lisp": ('(in-package "ACL2")\n(ld "host/a.lisp")\n'
                            "(defun fn-b () (fn-a))\n"),
        })), [])

    def test_explicit_raw_load_sees_the_common_lisp_vocabulary(self):
        tree = tree_from({
            "host/native/build.lisp": (
                '(in-package "ACL2")\n'
                '(defttag :native-test)\n'
                '(progn! (set-raw-mode t) (load "host/native/raw.lisp"))\n'),
            "host/native/raw.lisp": (
                '(in-package "ACL2")\n'
                '(defun fnn-raw-tail (x) (fifth x))\n'),
        })
        self.assertEqual(ledger.raw_host_paths(tree), {"host/native/raw.lisp"})
        self.assertEqual(ledger.host_names(tree), [])

    def test_raw_typo_and_missing_fnn_helper_are_not_whitelisted(self):
        found = ledger.host_names(tree_from({
            "host/native/build.lisp": (
                '(in-package "ACL2")\n'
                '(defttag :native-test)\n'
                '(progn! (set-raw-mode t) (load "host/native/raw.lisp"))\n'),
            "host/native/raw.lisp": (
                '(in-package "ACL2")\n'
                '(defun fnn-raw-bad (x) (fivth x))\n'
                '(defun fnn-raw-missing () (fnn-not-present))\n'),
        }))
        self.assertEqual([(entry["name"], entry["source"]) for entry in found],
                         [("fivth", None), ("fnn-not-present", None)])
        self.assertTrue(all("raw Common Lisp load" in entry["reason"]
                            for entry in found))

    def test_acl2_wrapper_does_not_inherit_raw_visibility_or_helpers(self):
        found = ledger.host_names(tree_from({
            "host/native/build.lisp": (
                '(in-package "ACL2")\n'
                '(defttag :native-test)\n'
                '(progn! (set-raw-mode t) (load "host/native/raw.lisp"))\n'),
            "host/native/raw.lisp": (
                '(in-package "ACL2")\n'
                '(defun fnn-raw-helper () t)\n'),
            "host/wrapper.lisp": (
                '(in-package "ACL2")\n'
                '(defun fn-wrapper (x) (list (fifth x) (fnn-raw-helper)))\n'),
        }))
        self.assertEqual([(entry["host"], entry["name"], entry["source"])
                          for entry in found],
                         [("host/wrapper.lisp", "fifth", None),
                          ("host/wrapper.lisp", "fnn-raw-helper",
                           "host/native/raw.lisp")])

    def test_raw_mode_without_an_active_trust_tag_is_not_a_raw_surface(self):
        tree = tree_from({
            "host/native/build.lisp": (
                '(in-package "ACL2")\n'
                '(progn! (set-raw-mode t) (load "host/native/unloaded.lisp"))\n'),
            "host/native/unloaded.lisp": (
                '(in-package "ACL2")\n'
                '(defun fnn-unloaded (x) (fifth x))\n'),
        })
        self.assertEqual(ledger.raw_host_paths(tree), set())
        found = ledger.host_names(tree)
        self.assertEqual([(entry["host"], entry["name"]) for entry in found],
                         [("host/native/unloaded.lisp", "fifth")])

    def test_a_macro_argument_is_syntax_and_a_cond_test_is_not_a_call(self):
        self.assertEqual(ledger.host_names(tree_from({
            "host/a.lisp": ('(in-package "ACL2")\n'
                            "(defmacro fn-with (vars form) (list 'quote vars form))\n"
                            "(defun fn-b (x) (fn-with (path) x))\n"
                            "(defun fn-c (x) (let ((ctx x)) (cond (ctx :yes) (t :no))))\n"),
        })), [])


class LintReportingTests(unittest.TestCase):
    def test_warnings_carry_the_book_line_and_name(self):
        tree = tree_from({
            "books/b.lisp": ExportHygieneLintTests.ACCESSOR,
            "tests/acl2/t.lisp": '(in-package "ACL2")\n(must-fail (thm (fn-p x)))\n',
        })
        warnings = ledger.lint_warnings(tree)
        self.assertEqual(len(warnings), 2)
        self.assertTrue(warnings[0].startswith("export hygiene: books/b.lisp:3:"))
        self.assertTrue(warnings[1].startswith("teeth form: tests/acl2/t.lisp:2:"))

    def test_the_generated_ledger_carries_both_counts(self):
        ledger_data = ledger.build_ledger(tree_from({
            "books/b.lisp": ExportHygieneLintTests.ACCESSOR}))
        self.assertEqual(ledger_data["totals"]["export_hygiene_warnings"], 1)
        self.assertEqual(ledger_data["totals"]["teeth_form_warnings"], 0)
        self.assertEqual(ledger_data["lints"]["export_hygiene"][0]["theorem"],
                         "fn-ag-car-is-car")
        self.assertEqual(ledger_data["totals"]["include_hygiene_warnings"], 0)
        self.assertIn("Export-hygiene warnings | 1",
                      ledger.ledger_markdown(ledger_data))

    def test_a_host_warning_carries_the_file_line_and_name(self):
        tree = tree_from({
            "host/h.lisp": '(in-package "ACL2")\n(defun fn-h () *fn-gone*)\n',
        })
        warnings = ledger.lint_warnings(tree)
        self.assertEqual(len(warnings), 1)
        self.assertTrue(warnings[0].startswith(
            "host names: host/h.lisp:2: *fn-gone*:"), warnings[0])
        ledger_data = ledger.build_ledger(tree)
        self.assertEqual(ledger_data["totals"]["host_names_warnings"], 1)
        self.assertIn("Host-names warnings | 1", ledger.ledger_markdown(ledger_data))

    def test_an_include_warning_carries_the_includer_line_and_target(self):
        tree = tree_from({
            "books/open.lisp": IncludeHygieneLintTests.OPEN,
            "books/includer.lisp": '(in-package "ACL2")\n(include-book "open")\n',
        })
        warnings = ledger.lint_warnings(tree)
        self.assertEqual(len(warnings), 1)
        self.assertTrue(warnings[0].startswith(
            "include hygiene: books/includer.lisp:2: books/open.lisp:"), warnings[0])
        ledger_data = ledger.build_ledger(tree)
        self.assertEqual(ledger_data["totals"]["include_hygiene_warnings"], 1)
        self.assertIn("Include-hygiene warnings | 1",
                      ledger.ledger_markdown(ledger_data))


class DefrecordExpansionTests(unittest.TestCase):
    """`fn-defrecord` is a macro, so the reader must expand it to see the book.

    Without this the ledger reads a migrated book as forty names shorter than
    it is: `host_names` then calls every accessor the host bridges use
    undefined, `include_hygiene` warns about every includer because the
    recognizers never reach `disabled_rules`, and the guard and theorem counts
    fall.  These pin the Python side of the mirror; the Lisp side is proved by
    `tests/acl2/defrecord-tests.lisp`.
    """

    UNTAGGED = ('(in-package "ACL2")\n'
                '(fn-defrecord fn-x-point\n'
                '  :constructor (fn-x-point a b c)\n'
                '  :fields ((fn-x-point-a natp)\n'
                '           (fn-x-point-b natp)\n'
                '           (fn-x-point-c stringp)))\n')
    TAGGED = ('(in-package "ACL2")\n'
              '(fn-defrecord fn-x-mark\n'
              '  :tag :fn-x-mark\n'
              '  :constructor (fn-x-mark origin weight)\n'
              '  :fields ((fn-x-mark-origin fn-x-pointp)\n'
              '           (fn-x-mark-weight posp))\n'
              '  :extra ((<= (fn-x-mark-weight x) 1000)))\n')
    NO_RECOGNIZER = ('(in-package "ACL2")\n'
                     '(fn-defrecord fn-x-result\n'
                     '  :constructor (fn-x-result ok value)\n'
                     '  :recognizer nil\n'
                     '  :fields ((fn-x-result-ok t) (fn-x-result-value t)))\n')

    def book(self, source: str) -> ledger.Book:
        return tree_from({"books/x.lisp": source}).books["books/x.lisp"]

    def test_every_generated_name_is_defined(self):
        book = self.book(self.UNTAGGED)
        for name in ("fn-x-point-shapep", "fn-x-point", "fn-x-point-a",
                     "fn-x-point-b", "fn-x-point-c", "fn-x-pointp",
                     "fn-x-point-shapep-of-fn-x-point",
                     "fn-x-point-a-of-fn-x-point", "fn-x-point-injective",
                     "fn-x-point-of-accessors",
                     "fn-x-point-shapep-forward-shape",
                     "fn-x-point-accessors-forward-consp",
                     "fn-x-pointp-forward-shape"):
            self.assertIn(name, book.definitions, name)

    def test_generated_functions_are_marked_generated(self):
        book = self.book(self.UNTAGGED)
        self.assertTrue(book.functions)
        self.assertTrue(all(function.generated for function in book.functions))

    def test_accessor_guards_are_verified_by_event(self):
        statuses = {function.name: function.guard_status
                    for function in self.book(self.UNTAGGED).functions}
        self.assertEqual(statuses["fn-x-point-a"], "verified")
        self.assertEqual(statuses["fn-x-point-shapep"], "default-guarded")

    def test_internals_are_withdrawn(self):
        book = self.book(self.UNTAGGED)
        self.assertEqual(
            book.disabled_rules,
            {"fn-x-point-shapep", "fn-x-point", "fn-x-point-a",
             "fn-x-point-b", "fn-x-point-c"})

    def test_tag_shifts_the_fields_by_one(self):
        book = self.book(self.TAGGED)
        bodies = {function.name: function.body for function in book.functions}
        # origin at index 1, weight at index 2: (car (cdr x)), (car (cdr (cdr x))).
        self.assertEqual(ledger.head(bodies["fn-x-mark-origin"]), "mbe")
        logic = ledger.keyword_plist(bodies["fn-x-mark-origin"][1:])[":logic"]
        self.assertEqual(logic, [ledger.Sym("car"),
                                 [ledger.Sym("cdr"), ledger.Sym("x")]])
        self.assertEqual(bodies["fn-x-mark"],
                         [ledger.Sym("list"), ledger.Sym(":fn-x-mark"),
                          ledger.Sym("origin"), ledger.Sym("weight")])

    def test_recognizer_carries_field_types_and_extra(self):
        body = {f.name: f.body for f in self.book(self.TAGGED).functions}["fn-x-markp"]
        self.assertIn([ledger.Sym("fn-x-pointp"),
                       [ledger.Sym("fn-x-mark-origin"), ledger.Sym("x")]], body)
        self.assertIn([ledger.Sym("<="),
                       [ledger.Sym("fn-x-mark-weight"), ledger.Sym("x")], 1000], body)

    CONTEXT = ('(in-package "ACL2")\n'
               '(fn-defrecord fn-x-pin\n'
               '  :constructor (fn-x-pin subject weight)\n'
               '  :fields ((fn-x-pin-subject stringp)\n'
               '           (fn-x-pin-weight (<= (fn-x-pin-weight x) budget)))\n'
               '  :recognizer-formals (budget)\n'
               '  :recognizer-guard (posp budget)\n'
               '  :recognizer-verify-guards nil)\n')

    def test_recognizer_formals_come_before_the_record_variable(self):
        book = self.book(self.CONTEXT)
        formals = {f.name: f.formals for f in book.functions}
        self.assertEqual(formals["fn-x-pinp"], ["budget", "x"])
        # The accessors keep the one formal the record pattern gives them.
        self.assertEqual(formals["fn-x-pin-subject"], ["x"])
        theorem = next(t for t in book.theorems
                       if t.name == "fn-x-pinp-forward-shape")
        self.assertEqual(theorem.statement[1],
                         [ledger.Sym("fn-x-pinp"), ledger.Sym("budget"),
                          ledger.Sym("x")])

    def test_recognizer_guard_and_deferred_verification(self):
        book = self.book(self.CONTEXT)
        statuses = {f.name: f.guard_status for f in book.functions}
        # Deferred: the book verifies it, so the reader must not count it here.
        self.assertNotEqual(statuses["fn-x-pinp"], "verified")
        # The accessors are untouched by either option.
        self.assertEqual(statuses["fn-x-pin-subject"], "verified")

    def test_recognizer_nil_suppresses_it(self):
        book = self.book(self.NO_RECOGNIZER)
        self.assertNotIn("fn-x-resultp", book.definitions)
        self.assertNotIn("fn-x-resultp-forward-shape", book.definitions)
        self.assertIn("fn-x-result-ok", book.definitions)

    def test_constructor_of_accessors_is_under_the_shape(self):
        # The dual of the accessor-of-constructor family, what every
        # decode-of-encode needs.  Under the shape predicate, so that a
        # record with `:recognizer nil` has it too and no recognizer formal
        # becomes a free variable in the hypothesis.
        theorem = next(t for t in self.book(self.UNTAGGED).theorems
                       if t.name == "fn-x-point-of-accessors")
        self.assertEqual(
            theorem.statement,
            [ledger.Sym("implies"),
             [ledger.Sym("fn-x-point-shapep"), ledger.Sym("x")],
             [ledger.Sym("equal"),
              [ledger.Sym("fn-x-point"),
               [ledger.Sym("fn-x-point-a"), ledger.Sym("x")],
               [ledger.Sym("fn-x-point-b"), ledger.Sym("x")],
               [ledger.Sym("fn-x-point-c"), ledger.Sym("x")]],
              ledger.Sym("x")]])
        names = [t.name for t in self.book(self.NO_RECOGNIZER).theorems]
        self.assertIn("fn-x-result-of-accessors", names)

    def test_recognizer_forward_chains_the_shape_predicate(self):
        # What makes the rule above fire with the recognizer CLOSED.
        theorem = next(t for t in self.book(self.TAGGED).theorems
                       if t.name == "fn-x-markp-forward-shape")
        self.assertEqual(theorem.statement[2][1],
                         [ledger.Sym("fn-x-mark-shapep"), ledger.Sym("x")])

    def test_injectivity_is_not_reflexive(self):
        # A synthesis that used the same call on both sides would make the
        # suspect detector report every record as a reflexive conclusion.
        theorem = next(t for t in self.book(self.UNTAGGED).theorems
                       if t.name == "fn-x-point-injective")
        self.assertNotEqual(theorem.statement[1], theorem.statement[2])
        self.assertEqual(ledger.keyword_plist(theorem.rest)[":rule-classes"],
                         ledger.Sym("nil"))

    def test_export_names_recognizers_and_withdraws_them(self):
        book = self.book(
            '(in-package "ACL2")\n'
            '(fn-defrecord-export fn-x-vocabulary\n'
            '  :records (fn-x-point fn-x-mark)\n'
            '  :also (fn-x-step))\n')
        self.assertEqual(book.disabled_rules,
                         {"fn-x-pointp", "fn-x-markp", "fn-x-step"})


class HandWrittenRecordLintTests(unittest.TestCase):
    """The fifth lint: a record written out event by event, not generated."""

    HAND = ('(in-package "ACL2")\n'
            '(defun fn-h-shapep (x) (declare (xargs :guard t))\n'
            '  (and (true-listp x) (equal (len x) 3)))\n'
            '(defun fn-h-a (x) (declare (xargs :guard t))\n'
            '  (mbe :logic (car x) :exec (fn-ag-car x)))\n'
            '(defun fn-h-b (x) (declare (xargs :guard t))\n'
            '  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))\n'
            '(defun fn-h-c (x) (declare (xargs :guard t))\n'
            '  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))\n')
    NTH_STYLE = ('(in-package "ACL2")\n'
                 '(defun fn-n-shapep (x) (declare (xargs :guard t))\n'
                 '  (and (true-listp x) (equal (len x) 3)))\n'
                 '(defun fn-n-a (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))\n'
                 '(defun fn-n-b (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))\n'
                 '(defun fn-n-c (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))\n')

    def findings(self, source: str) -> list[dict]:
        return ledger.hand_written_record(tree_from({"books/h.lisp": source}))

    def test_mbe_accessors_are_a_finding(self):
        found = self.findings(self.HAND)
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0]["accessors"], 3)
        self.assertIn("fn-defrecord", found[0]["reason"])

    def test_nth_style_accessors_are_a_finding_too(self):
        # Two flavours are in the tree: the `mbe` chain and `(fn-bp-nth 1 x)`.
        self.assertEqual(len(self.findings(self.NTH_STYLE)), 1)

    def test_two_accessors_are_not_a_finding(self):
        source = "\n".join(self.HAND.splitlines()[:-2]) + "\n"
        self.assertEqual(self.findings(source), [])

    def test_a_shape_predicate_alone_is_not_a_finding(self):
        self.assertEqual(self.findings(
            '(in-package "ACL2")\n'
            '(defun fn-h-shapep (x) (declare (xargs :guard t)) (true-listp x))\n'), [])

    def test_accessors_over_a_different_variable_do_not_count(self):
        source = self.HAND.replace("(x)", "(y)").replace(
            "(defun fn-h-shapep (y)", "(defun fn-h-shapep (x)").replace(
            "(and (true-listp y) (equal (len y) 3))",
            "(and (true-listp x) (equal (len x) 3))")
        self.assertEqual(self.findings(source), [])

    def test_a_generated_record_is_not_a_finding(self):
        self.assertEqual(self.findings(
            '(in-package "ACL2")\n'
            '(fn-defrecord fn-g\n'
            '  :constructor (fn-g a b c)\n'
            '  :fields ((fn-g-a natp) (fn-g-b natp) (fn-g-c natp)))\n'), [])

    def test_a_macro_only_book_exports_no_rule(self):
        book = tree_from({"books/m.lisp":
                          '(in-package "ACL2")\n'
                          '(defun fn-m-plumbing (x)\n'
                          '  (declare (xargs :mode :program)) x)\n'
                          '(defmacro fn-m (x) (fn-m-plumbing x))\n'}).books["books/m.lisp"]
        self.assertTrue(ledger.exports_no_rule(book))

    def test_an_include_shim_does_not_count_as_rule_free(self):
        book = tree_from({"books/s.lisp":
                          '(in-package "ACL2")\n'
                          '(include-book "m")\n'
                          '(defun fn-s (x) (declare (xargs :mode :program)) x)\n'
                          }).books["books/s.lisp"]
        self.assertFalse(ledger.exports_no_rule(book))

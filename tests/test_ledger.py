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
    """A Tree over inline books, with no filesystem and no ACL2."""
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        books = {}
        for relative, text in sources.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            books[relative] = ledger.analyze_book(path, relative)
    return ledger.Tree(books, roots if roots is not None else
                       [relative[:-5] for relative in sources])


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

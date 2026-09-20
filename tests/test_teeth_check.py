"""`tools/teeth_check.py`: the reading of a witness, and the driver it writes.

The three defects this tool exists to find were all found by hand on
2026-09-20, so each of them is a case here: a claim whose two sides are both
empty (the S4-1 hostile batch), a hypothesis that is `NIL` (a vacuous
implication), and a recogniser no test ever makes true (the `owner-tests`
connection list).  The ACL2 side is pinned by one real log fragment rather
than by a string this file imagines ACL2 prints.
"""

from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import teeth_check  # noqa: E402
from teeth_check import Assertion, Claim  # noqa: E402


def read(source: str, book: str = "tests/acl2/x-tests.lisp"):
    """`read_book` over a literal book, without touching the filesystem."""
    path = ROOT / book
    original = teeth_check.Path.read_text
    try:
        return teeth_check.read_book(_Fake(path, source))
    finally:
        del original


class _Fake:
    """A path that reads as the given text and still knows where it is."""

    def __init__(self, path: Path, source: str) -> None:
        self._path, self._source = path, source
        self.name, self.parent, self.stem = path.name, path.parent, path.stem

    def read_text(self, encoding: str = "utf-8") -> str:
        return self._source

    def relative_to(self, other: Path) -> Path:
        return self._path.relative_to(other)


class Rendering(unittest.TestCase):
    def test_a_read_form_renders_back_to_itself(self):
        for text in ["(fn-statep *w*)", "'(1 2 3)", '(equal "a" (f 3))',
                     "(not (member-equal :k (g '(:a))))"]:
            form = teeth_check.ledger.read_forms(text)[0]
            self.assertIsNotNone(teeth_check.renderable(form), text)

    def test_an_exact_rational_is_refused(self):
        # The ledger's reader keeps `1/2` as the plain string "1/2", which is
        # what a Lisp string literal also reads as, so rendering it back
        # would hand ACL2 a STRING.  `renderable` must decline.
        form = teeth_check.ledger.read_forms("(< (fn-sched-pos x) 1/2)")[0]
        self.assertIsNone(teeth_check.renderable(form))
        keep = teeth_check.ledger.read_forms("(< (fn-sched-pos x) 2)")[0]
        self.assertIsNotNone(teeth_check.renderable(keep))


class ReadingABook(unittest.TestCase):
    SOURCE = '''(in-package "ACL2")
(include-book "../../books/thing")
(defconst *w* (fn-make 1))
(assert-event (equal (symbol-class 'fn-f (w state)) :common-lisp-compliant))
(assert-event (not (fn-thingp *w*)))
(assert-event (and (fn-thingp *w*) (equal (fn-a *w*) 1)))
'''

    def setUp(self):
        self.all, self.constants, self.error = read(self.SOURCE)
        # A `defconst` body is read for the multi-valued check and is not an
        # assertion; the counts and the probes see only the assertions.
        self.assertions = [a for a in self.all if a.kind == "assert-event"]

    def test_no_read_error(self):
        self.assertIsNone(self.error)

    def test_the_guard_world_audit_is_not_a_witness(self):
        self.assertTrue(self.assertions[0].audit)
        self.assertFalse(self.assertions[1].audit)

    def test_defconsts_are_collected(self):
        self.assertEqual(self.constants, ["*w*"])

    def test_a_negated_claim_keeps_its_polarity_and_predicate(self):
        claim = self.assertions[1].claims[0]
        self.assertFalse(claim.positive)
        self.assertEqual(claim.predicate, "fn-thingp")

    def test_a_conjunction_splits_into_claims(self):
        self.assertEqual(len(self.assertions[2].claims), 2)
        self.assertTrue(all(c.positive for c in self.assertions[2].claims))

    def test_each_assertion_knows_its_top_level_form(self):
        self.assertEqual([a.top for a in self.assertions], [3, 4, 5])
        self.assertEqual([a.kind for a in self.all][0], "defconst")


class Degeneracy(unittest.TestCase):
    def test_the_empty_values(self):
        for value in ["NIL", '""', "()"]:
            self.assertIsNotNone(teeth_check.degenerate(value), value)

    def test_zero_is_a_number_and_not_an_absence(self):
        # `*anchor-mint*` is 0, two staged records really do share txid 0,
        # and `fn-nntp-group-low` of an empty group is 0.  Calling 0 empty
        # flagged all three and found nothing.
        self.assertIsNone(teeth_check.degenerate("0"))

    def test_a_record_with_no_members_is_reported_not_called_empty(self):
        self.assertTrue(teeth_check.tag_only("(:FN-DELTA)"))
        self.assertIsNone(teeth_check.degenerate("(:FN-DELTA)"))

    def test_a_record_whose_field_is_nil_is_still_a_record(self):
        self.assertIsNone(teeth_check.degenerate("(:WANT NIL)"))

    def test_a_real_value_is_not_degenerate(self):
        self.assertIsNone(teeth_check.degenerate("(:OK (1 2 3))"))
        self.assertIsNone(teeth_check.degenerate("T"))


class TheDriver(unittest.TestCase):
    """The probes go where the assertion is, not at the end of the book."""

    SOURCE = '''(in-package "ACL2")
(defattach fn-digest fn-toy-a)
(assert-event (equal (fn-digest '(1)) (fn-digest '(2))))
(defattach fn-digest fn-toy-b)
(assert-event (not (equal (fn-digest '(1)) (fn-digest '(2)))))
'''

    def setUp(self):
        self.path = ROOT / "tests/acl2/x-tests.lisp"
        self.assertions, _, _ = read(self.SOURCE)
        self.probes = teeth_check.probes_for(self.assertions)
        self.where = {p.key: teeth_check.top_of(p.key, self.assertions)
                      for p in self.probes}
        source = self.SOURCE.splitlines(keepends=True)
        forms = [source[1], source[2], source[3], source[4]]
        self.text = teeth_check.driver(
            self.path, self.probes, [source[0]] + forms, self.where)

    def test_the_first_probe_precedes_the_second_defattach(self):
        first = self.text.index("<FNT a0")
        second = self.text.index("(defattach fn-digest fn-toy-b)")
        self.assertLess(first, second)

    def test_every_probe_is_guard_free(self):
        self.assertEqual(self.text.count("with-guard-checking :none"),
                         len(self.probes))

    def test_the_book_source_is_the_driver(self):
        self.assertIn("(defattach fn-digest fn-toy-a)", self.text)


class ParsingALog(unittest.TestCase):
    """One real ACL2 8.7 fragment: `cw` prints the marker, then the value."""

    LOG = ("ACL2 !>>\n"
           "<FNT a3c0t>\n"
           "(:OK ((:POSITIVE (97 42))))\n"
           "</FNT>\n"
           "ACL2 !>>\n"
           "<FNT a4>\n"
           "NIL\n"
           "</FNT>\n"
           "ACL2 !>> <FNT-PREFIX-DONE>\n")

    def test_values_by_key(self):
        values = teeth_check.parse_log(self.LOG)
        self.assertEqual(values["a3c0t"], "(:OK ((:POSITIVE (97 42))))")
        self.assertEqual(values["a4"], "NIL")


class Findings(unittest.TestCase):
    def claim(self, text: str, positive: bool = True) -> Assertion:
        body = teeth_check.ledger.read_forms(text)[0]
        inner, polarity = teeth_check.strip_wrappers(body)
        record = Assertion(book="tests/acl2/x-tests.lisp", line=7, index=0,
                           top=0, body=body, audit=False)
        record.claims = [Claim(book=record.book, line=7, index=0, clause=0,
                               positive=polarity, term=inner,
                               predicate=teeth_check.head(inner))]
        return record

    def run_findings(self, record: Assertion, values: dict[str, str]):
        books = {record.book: [record]}
        saved = {record.book: {"book": record.book, "exit": 0, "prefix": "ok",
                               "include_failed": False, "values": values,
                               "probes": {k: "t" for k in values}}}
        return {f.check for f in teeth_check.evaluated_findings(books, saved)}

    def test_both_sides_empty(self):
        # The S4-1 shape: the delta and the expectation were both NIL.
        record = self.claim("(equal (fn-delta *a*) (fn-delta *b*))")
        found = self.run_findings(record, {"a0": "T", "a0c0t": "T",
                                           "a0c0s0": "NIL", "a0c0s1": "NIL"})
        self.assertIn("both-sides-degenerate", found)

    def test_a_nil_hypothesis_is_vacuous(self):
        record = self.claim("(implies (fn-p *a*) (fn-q *a*))")
        found = self.run_findings(record, {"a0": "T", "a0c0h": "NIL"})
        self.assertIn("vacuous-implies", found)

    def test_an_assertion_that_does_not_hold(self):
        record = self.claim("(fn-thingp *a*)")
        found = self.run_findings(record, {"a0": "NIL"})
        self.assertIn("assertion-false", found)

    def test_a_claim_over_an_empty_collection(self):
        record = self.claim("(member-equal *x* (fn-held *s*))")
        found = self.run_findings(record, {"a0": "T", "a0c0t": "T",
                                           "a0c0s0": "(1 2)", "a0c0s1": "NIL"})
        self.assertIn("empty-collection", found)

    def test_a_real_value_raises_nothing(self):
        record = self.claim("(equal (fn-delta *a*) '(1 2))")
        found = self.run_findings(record, {"a0": "T", "a0c0t": "T",
                                           "a0c0s0": "(1 2)"})
        self.assertEqual(found, set())


class Recognisers(unittest.TestCase):
    def test_a_connective_is_not_a_recogniser(self):
        self.assertFalse(teeth_check.recogniser("or"))
        self.assertFalse(teeth_check.recogniser(None))

    def test_a_name_the_tree_does_not_define_is_not_a_recogniser(self):
        self.assertFalse(teeth_check.recogniser("fn-no-such-thingp"))

    def test_one_the_tree_does_define(self):
        self.assertTrue(teeth_check.recogniser("fn-statep"))


class TheCorpus(unittest.TestCase):
    """The static pass runs over the real tree and reports, never raises."""

    def test_every_test_book_reads(self):
        paths = teeth_check.test_books([])
        self.assertGreater(len(paths), 50)
        assertions, _constants, errors = teeth_check.load_books(paths)
        self.assertEqual(errors, {})
        self.assertGreater(teeth_check.counts(assertions)["assertions"], 1000)

    def test_the_summary_exits_zero(self):
        self.assertEqual(teeth_check.main(["--summary"]), 0)


if __name__ == "__main__":
    unittest.main()


class MultiValued(unittest.TestCase):
    """`(mv-nth n (f ...))` in an evaluation context: the form does not run.

    Fifteen of these sat in `tests/acl2/peer-feed-tests.lisp` until
    2026-09-20 and nothing reported them, because the book had never
    certified.  This is the "the book never ran" class, not the "the
    assertion did not bite" class.
    """

    def flagged(self, text: str):
        form = teeth_check.ledger.read_forms(text)[0]
        return teeth_check.multi_valued_calls(form, teeth_check.mv_functions())

    def test_the_illegal_shape(self):
        self.assertEqual(self.flagged("(mv-nth 0 (fn-feed-tick-step f obs))"),
                         ["fn-feed-tick-step"])

    def test_the_repair_is_clean(self):
        self.assertEqual(
            self.flagged("(nth 0 (mv-list 2 (fn-feed-tick-step f obs)))"), [])

    def test_a_real_multi_value_context_is_clean(self):
        self.assertEqual(
            self.flagged("(mv-let (g fx) (fn-feed-observe a b) (list g fx))"),
            [])

    def test_a_macro_wrapper_is_not_flagged(self):
        # `bst-res` in byte-store-tests expands to an `mv-let`; a static
        # reader cannot see through a macro, so it does not guess.
        self.assertEqual(self.flagged("(bst-res (fn-bs-fsync-file s 2 :ok))"),
                         [])

    def test_a_single_valued_function_is_not_multi_valued(self):
        self.assertNotIn("fn-bs-fence-file", teeth_check.mv_functions())
        self.assertIn("fn-bs-fsync-file", teeth_check.mv_functions())


class Acl2Errors(unittest.TestCase):
    def test_a_translate_error_names_its_form(self):
        log = ("ACL2 Error [Translate] in ( DEFCONST *FF2* ...):  It is\n"
               "ACL2 Error in ( DEFTHEORY FN-OWN-INVARIANTS-VOCABULARY ...): \n")
        found = teeth_check.ACL2_ERROR.findall(log)
        self.assertEqual([m[1] for m in found], ["DEFCONST", "DEFTHEORY"])
        self.assertEqual(found[0][0], "Translate")

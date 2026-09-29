"""Teeth for tools/payload_kind_check.py and harness_check's entry-guards.

Each case is a definition shaped like one of 2026-09-27's defects or like
its fix, read by the same reader the check uses."""
import unittest

from tools import ledger
from tools import payload_kind_check as pk
from tools import harness_check as hc

SINKS = {"fn-handle-bytes", "natp", "fn-make-article"}


def bad_sites(source):
    form = ledger.Reader(source).top_level()[0][0]
    bad = []
    for item in form[3:]:
        pk.scan_body(item, SINKS, bad)
    return bad


class PayloadKindTests(unittest.TestCase):
    def test_moderation_defect_is_found(self):
        # books/moderation-verbs.lisp fn-mvb-held-article before its fix
        self.assertEqual(len(bad_sites(
            "(defun f (a) (fn-mvb-after-blank (fn-article-payload a)))")), 1)

    def test_reading_through_the_arena_is_accepted(self):
        self.assertEqual(bad_sites(
            "(defun f (a fn-arena) (fn-mvb-after-blank "
            "(fn-handle-bytes (fn-article-payload a) fn-arena)))"), [])

    def test_a_let_bound_handle_used_as_octets_is_found(self):
        # books/store-reclaim.lisp fn-rcl-summary's shape
        bad = bad_sites("(defun f (a) (let ((payload (fn-article-payload a))) "
                        "(+ (len payload) 1)))")
        self.assertEqual(len(bad), 1)
        self.assertIn("len", bad[0][1])

    def test_a_let_bound_handle_used_as_a_handle_is_accepted(self):
        self.assertEqual(bad_sites(
            "(defun f (a) (let ((p (fn-article-payload a))) (natp p)))"), [])

    def test_the_held_row_accessor_is_checked_too(self):
        self.assertEqual(len(bad_sites("(defun f (h) (len (fn-held-payload h)))")), 1)

    # W1 (entry-guards-2's finding): one hop from the accessor.
    WIRE = {"fn-stx-lace-of-store", "fn-stx-index-of-store"}

    def hop_sites(self, source):
        form = ledger.Reader(source).top_level()[0][0]
        bad = []
        for item in form[3:]:
            pk.wire_calls(item, self.WIRE, bad)
        return bad

    def test_retained_articles_into_the_octet_model_are_found(self):
        # books/stx-lace.lisp fn-stx-lace's shape, fn-stx-store inlined
        self.assertEqual(self.hop_sites(
            "(defun f (node k) (fn-stx-lace-of-store "
            "(fn-state-articles (fn-node-acceptance node)) k))"),
            ["fn-stx-lace-of-store"])

    def test_converted_articles_are_accepted(self):
        self.assertEqual(self.hop_sites(
            "(defun f (node k fn-arena) (fn-stx-lace-of-store (fn-articles-wire-of "
            "(fn-state-articles (fn-node-acceptance node)) fn-arena) k))"), [])

    def test_a_keyless_index_reads_no_payload(self):
        # books/replay-identity-index.lisp fn-rii-sco-finalize-configured
        self.assertEqual(self.hop_sites(
            "(defun f (node) (fn-stx-index-of-store (fn-stx-store node) nil))"), [])
        self.assertEqual(len(self.hop_sites(
            "(defun f (node k) (fn-stx-index-of-store (fn-stx-store node) k))")), 1)

    def test_the_tree_has_no_undeclared_reader(self):
        findings, counts = pk.scan()
        self.assertEqual(findings, [])
        self.assertGreater(counts["definitions_reading_payload"], 30)


class EntryGuardHelperTests(unittest.TestCase):
    KINDS = {"fn-cbor-octet-listp", "natp"}

    def form(self, source):
        return ledger.Reader(source).top_level()[0][0]

    def test_guard_conjuncts_name_the_covered_formals(self):
        f = self.form("(defun e (octets n state) (declare (xargs :stobjs state "
                      ":guard (and (fn-cbor-octet-listp octets) (natp n) (foo octets n)))) nil)")
        guard, stobjs = hc._xargs(f)
        self.assertEqual(stobjs, ["state"])
        self.assertEqual(hc._unary_kind_conjuncts(guard, self.KINDS), {"octets", "n"})

    def test_an_unguarded_entry_covers_nothing(self):
        f = self.form("(defun e (octets) (declare (xargs :mode :program)) octets)")
        guard, _ = hc._xargs(f)
        self.assertEqual(hc._unary_kind_conjuncts(guard, self.KINDS), set())

    def test_a_body_first_refusal_counts(self):
        f = self.form("(defun e (octets) (if (or (not (fn-cbor-octet-listp octets)) (bad)) "
                      ":refused (go octets)))")
        self.assertEqual(hc._body_checks(f[-1], self.KINDS), {"octets"})

    def test_the_kind_list_is_read_from_the_book(self):
        kinds = hc.entry_guard_kinds(hc.ROOT)
        self.assertIn("fn-payload-handle-p", kinds)
        self.assertIn("fn-cbor-octet-listp", kinds)


if __name__ == "__main__":
    unittest.main()

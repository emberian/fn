"""A certified registry claim needs events and current closure evidence."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest

from tools import certified_claims, green_check
from tests.test_green_check import book, manifest


class CertifiedClaimsTests(unittest.TestCase):
    def setUp(self):
        self.tree = SimpleNamespace(
            theorems={"proved": SimpleNamespace(book="books/top.lisp")},
            functions={}, constrained={}, suspects={},
            closure={"books/top.lisp"},
        )
        self.proofs = [{"id": "PRF-TEST", "status": "certified",
                        "events": ["proved"]}]
        self.curated = {"targets": [{"id": "PRF-TEST", "events":
                                     [{"name": "proved", "kind": "theorem"}]}]}

    def test_existing_event_with_matching_closure_is_clear(self):
        owners, warnings = certified_claims.event_owners(
            self.proofs, self.curated, self.tree)
        self.assertEqual(warnings, [])
        self.assertEqual(owners, {"PRF-TEST": {"books/top"}})
        report = {"books_by_verdict": {"books/top":
                  {"verdict": "green", "deps_moved_since": []}}}
        self.assertEqual(certified_claims.evidence_warnings(owners, report), [])

    def test_missing_registry_events_and_missing_definition_are_warned(self):
        self.proofs[0]["events"] = []
        self.curated["targets"][0]["events"][0]["name"] = "absent"
        owners, warnings = certified_claims.event_owners(
            self.proofs, self.curated, self.tree)
        self.assertEqual(owners, {"PRF-TEST": set()})
        self.assertTrue(any("events differ" in warning for warning in warnings))
        self.assertTrue(any("theorem 'absent' is absent" in warning for warning in warnings))

    def test_no_curated_events_cannot_support_certified_status(self):
        owners, warnings = certified_claims.event_owners(
            self.proofs, {"targets": []}, self.tree)
        self.assertEqual(owners, {"PRF-TEST": set()})
        self.assertTrue(any("no curated ACL2 events" in warning for warning in warnings))

    def test_missing_manifest_record_is_not_treated_as_a_pass(self):
        warnings = certified_claims.evidence_warnings(
            {"PRF-TEST": {"books/top"}}, {"books_by_verdict": {}})
        self.assertTrue(any("no closure evidence record" in warning
                            for warning in warnings))

    def test_cited_function_needs_verified_guards(self):
        self.proofs[0]["events"] = ["unguarded"]
        self.curated["targets"][0]["events"] = [
            {"name": "unguarded", "kind": "guarded-function"}]
        self.tree.functions["unguarded"] = SimpleNamespace(
            book="books/top.lisp", guard_status="declared-off")
        _, warnings = certified_claims.event_owners(
            self.proofs, self.curated, self.tree)
        self.assertTrue(any("guard status declared-off" in warning
                            for warning in warnings))

    def test_changed_book_digest_and_include_are_distinct_gaps(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            dep_body = '(in-package "ACL2") ; dep\n'
            top_body = '(in-package "ACL2")\n(include-book "dep")\n'
            dep = book(root, "books/dep", dep_body)
            top = book(root, "books/top", top_body)
            manifest(root, "certify-20260901T010000Z-1", status="passed",
                     passed={"books/top": top}, closure={"books/dep": dep})
            owners = {"PRF-TEST": {"books/top"}}
            report = green_check.audit(root, roots=["books/top"])
            self.assertEqual(certified_claims.evidence_warnings(owners, report), [])

            book(root, "books/top", top_body + "; changed own bytes\n")
            report = green_check.audit(root, roots=["books/top"])
            self.assertTrue(any("never evidence" in warning for warning in
                                certified_claims.evidence_warnings(owners, report)))

            book(root, "books/top", top_body)
            book(root, "books/dep", dep_body + "; changed include\n")
            report = green_check.audit(root, roots=["books/top"])
            self.assertTrue(any("include-closure evidence" in warning for warning in
                                certified_claims.evidence_warnings(owners, report)))


if __name__ == "__main__":
    unittest.main()

"""A certified registry claim needs events and current closure evidence."""

from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest import mock

from tools import certified_claims, green_check
from tests.test_green_check import book, digest, manifest


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


    def write_manifest(self, root: Path, run_id: str, body: str,
                       result: str = "passed") -> str:
        relative = f"planning/evidence/manifests/{run_id}.json"
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({
            "book_results": {"books/top": result},
            "source_digests_sha256": {"books/top.lisp": digest(body)},
        }), encoding="utf-8")
        return relative

    def test_row_without_manifest_citation_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            book(root, "books/top", '(in-package "ACL2")\n')
            self.proofs[0]["evidence"] = ["books/top.lisp"]
            failures = certified_claims.manifest_failures(
                self.proofs, {"PRF-TEST": {"books/top"}}, root)
            self.assertEqual(failures, ["PRF-TEST: cites no manifest under "
                                        "planning/evidence/manifests/"])

    def test_absent_cited_manifest_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            book(root, "books/top", '(in-package "ACL2")\n')
            self.proofs[0]["evidence"] = [
                "planning/evidence/manifests/certify-20260901T010000Z-9.json"]
            failures = certified_claims.manifest_failures(
                self.proofs, {"PRF-TEST": {"books/top"}}, root)
            self.assertTrue(any("is absent" in failure for failure in failures))

    def test_row_with_matching_manifest_passes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            body = '(in-package "ACL2")\n'
            book(root, "books/top", body)
            cited = self.write_manifest(root, "certify-20260901T010000Z-1", body)
            self.proofs[0]["evidence"] = ["books/top.lisp", cited]
            self.assertEqual(certified_claims.manifest_failures(
                self.proofs, {"PRF-TEST": {"books/top"}}, root), [])
            # A cited manifest that attempted but failed the book does not count.
            self.write_manifest(root, "certify-20260901T010000Z-1", body,
                                result="failed")
            failures = certified_claims.manifest_failures(
                self.proofs, {"PRF-TEST": {"books/top"}}, root)
            self.assertTrue(any("does not record it passed" in failure
                                for failure in failures))

    def test_row_with_stale_digest_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            body = '(in-package "ACL2")\n'
            cited = self.write_manifest(root, "certify-20260901T010000Z-1", body)
            book(root, "books/top", body + "; changed own bytes\n")
            self.proofs[0]["evidence"] = [cited]
            failures = certified_claims.manifest_failures(
                self.proofs, {"PRF-TEST": {"books/top"}}, root)
            self.assertEqual(len(failures), 1)
            self.assertIn("no cited manifest certified books/top", failures[0])
            self.assertIn("(stale digest)", failures[0])

    def test_explain_names_book_digest_and_newest_certifier(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            body = '(in-package "ACL2")\n'
            book(root, "books/top", body)
            (root / "planning").mkdir()
            (root / "planning/proofs.json").write_text(json.dumps(
                {"proofs": self.proofs}), encoding="utf-8")
            (root / "planning/proof-events.json").write_text(json.dumps(
                self.curated), encoding="utf-8")
            with mock.patch.object(certified_claims.ledger, "load_tree",
                                   return_value=self.tree):
                lines = certified_claims.explain("PRF-TEST", root)
                self.assertIn("cited-manifests=none", lines[0])
                self.assertEqual(lines[1], f"  proved (theorem): book=books/top "
                                 f"digest={digest(body)} newest-certifying-manifest=none")
                manifest(root, "certify-20260901T010000Z-1", status="passed",
                         passed={"books/top": digest(body)})
                self.proofs[0]["evidence"] = [
                    "planning/evidence/manifests/certify-20260901T010000Z-1.json"]
                (root / "planning/proofs.json").write_text(json.dumps(
                    {"proofs": self.proofs}), encoding="utf-8")
                lines = certified_claims.explain("PRF-TEST", root)
                self.assertTrue(lines[1].endswith(
                    "newest-certifying-manifest=certify-20260901T010000Z-1 (cited)"))
                with self.assertRaises(KeyError):
                    certified_claims.explain("PRF-NONE", root)


if __name__ == "__main__":
    unittest.main()

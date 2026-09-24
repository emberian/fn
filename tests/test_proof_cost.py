"""Proof-cost diagnostics must keep timing and evidence scopes distinct."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from tools import proof_cost


class ProofCostTests(unittest.TestCase):
    def test_report_names_slow_certified_book_and_omits_installed_book(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "books" / "slow.lisp"
            source.parent.mkdir()
            source.write_text('(in-package "ACL2")\n')
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            run = root / "build" / "acl2" / "certify-one"
            run.mkdir(parents=True)
            manifest = run / "manifest.json"
            manifest.write_text(json.dumps({
                "status": "passed", "tree": str(root),
                "git_revision": "abc123", "hostname": "test-host",
                "acl2_toolchain_identity": "toolchain-123",
                "jobs_effective": 2, "started_utc": "2026-09-23T00:00:00+00:00",
                "finished_utc": "2026-09-23T00:00:20+00:00",
                "source_digests_sha256": {"books/slow.lisp": digest},
                "book_wall_seconds": {"books/slow": 12.0},
                "book_results": {"books/slow": "passed"},
                "installed_books": {"books/cached": "origin"},
                "slot_wait_seconds": {"books/slow": 3.0},
                "certify_wall_seconds": 12.5,
            }))
            (run / "books--slow.certify.log").write_text(
                "Summary\nForm: ( ENCAPSULATE ...)\nTime: 99.00 seconds\n"
                "Summary\nForm: ( DEFTHM SLOW-LEMMA ...)\n"
                "Time: 11.00 seconds (prove: 10.00)\n")
            lines = proof_cost.report(manifest, 10)
            joined = "\n".join(lines)
            self.assertIn("installed=1 certified-attempted=1", joined)
            self.assertIn("source-closure=matches", joined)
            self.assertIn("total=20s", joined)
            self.assertIn("sum-of-slot-waits=3.000s; CPU=unavailable", joined)
            self.assertIn("WARNING books/slow: process-wall=12.000s", joined)
            self.assertIn("slowest-event=( DEFTHM SLOW-LEMMA ...) 11.00s", joined)
            self.assertNotIn("WARNING books/cached", joined)
            source.write_text("; changed\n")
            self.assertIn("source-closure=stale", "\n".join(proof_cost.report(manifest, 10)))

    def test_remote_manifest_tree_falls_back_to_explicit_checkout_comparison(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory)
            source = checkout / "books" / "remote.lisp"
            source.parent.mkdir()
            source.write_text('(in-package "ACL2")\n')
            digest = proof_cost.certs.content_hash(source)
            manifest = {
                "tree": "/unavailable/farm/worktree",
                "source_digests_sha256": {"books/remote.lisp": digest},
            }
            self.assertEqual(
                proof_cost.source_scope(manifest, checkout),
                "source-closure=matches (0 of 1 source digests differ; checkout comparison)",
            )

            source.write_text("; changed checkout bytes\n")
            self.assertEqual(
                proof_cost.source_scope(manifest, checkout),
                "source-closure=stale (1 of 1 source digests differ; checkout comparison)",
            )

    def test_missing_log_and_manifest_are_explicitly_unavailable(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertIsNone(proof_cost.latest_manifest(root))
            run = root / "build" / "acl2" / "certify-one"
            run.mkdir(parents=True)
            manifest = run / "manifest.json"
            manifest.write_text(json.dumps({"book_wall_seconds": {"books/x": 13},
                                            "book_results": {"books/x": "failed"}}))
            lines = proof_cost.report(manifest, 10)
            self.assertIn("source-closure=current-bytes unavailable", lines)
            self.assertIn("per-event=unavailable", "\n".join(lines))


if __name__ == "__main__":
    unittest.main()

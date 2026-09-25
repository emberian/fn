"""Proof-cost diagnostics must keep timing and evidence scopes distinct."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from tools import proof_cost


class ProofCostTests(unittest.TestCase):
    def fixture_book(self, root: Path, name: str, text: str) -> None:
        path = root / f"{name}.lisp"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def fixture_run(self, stamp: str, *, host: str = "hbox", toolchain: str = "tool-A",
                    sources: dict[str, str], walls: dict[str, float],
                    installed: dict[str, str] | None = None,
                    results: dict[str, str] | None = None,
                    jobs: int | None = 2):
        run_id = f"certify-{stamp}-1"
        run = proof_cost.green_check.Run(run_id, host, True, sources)
        manifest = {
            "run_id": run_id, "acl2_toolchain_identity": toolchain,
            "source_digests_sha256": sources,
            "source_digests_sha256_after": sources,
            "book_wall_seconds": walls,
            "book_results": results or {book: "passed" for book in walls},
            "installed_books": installed or {},
        }
        if jobs is not None:
            manifest["jobs_effective"] = jobs
        return run, manifest

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
                "Time: 11.00 seconds (prove: 10.00)\n"
                "Summary\nForm: (CERTIFY-BOOK \"books/slow\" ...)\n"
                "Time: 12.00 seconds\n")
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

    def test_current_book_scope_reads_includes_without_a_generated_ledger(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture_book(root, "books/base", '(in-package "ACL2")\n')
            self.fixture_book(root, "books/top",
                              '(in-package "ACL2")\n(include-book "base")\n')
            with mock.patch.object(proof_cost.ledger, "makefile_roots",
                                   return_value=["books/top"]):
                self.assertEqual(proof_cost.current_books(root),
                                 {"books/top", "books/base"})

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

    def test_newest_partial_run_does_not_hide_older_matching_slow_book(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture_book(root, "books/base", '(in-package "ACL2")\n')
            self.fixture_book(root, "books/slow",
                              '(in-package "ACL2")\n(include-book "base")\n')
            self.fixture_book(root, "books/fast", '(in-package "ACL2")\n')
            sources = {f"{book}.lisp": proof_cost.certs.content_hash(
                root / f"{book}.lisp") for book in
                ("books/base", "books/slow", "books/fast")}
            old = self.fixture_run("20260901T010000Z", sources=sources,
                                   walls={"books/slow": 55.0})
            partial = self.fixture_run("20260902T010000Z", sources=sources,
                                       walls={"books/fast": 1.0},
                                       installed={"books/slow": "cache-origin"})
            wrong_closure = self.fixture_run(
                "20260903T010000Z",
                sources={**sources, "books/base.lisp": "0" * 64},
                walls={"books/slow": 1.0})
            selected, _, _ = proof_cost.history(
                root, {"books/slow", "books/fast"},
                runs=[old, partial, wrong_closure])
            slow = selected[("books/slow", "hbox", "tool-A", "scoped")]
            self.assertEqual((slow.seconds, slow.run_id), (55.0, old[0].run_id))
            lines = proof_cost.history_report(
                root, 10, books={"books/slow", "books/fast"},
                runs=[old, partial, wrong_closure])
            self.assertIn("WARNING books/slow: process-wall=55.000s", "\n".join(lines))
            self.assertNotIn("WARNING books/fast", "\n".join(lines))

    def test_changed_book_or_include_cannot_supply_current_measurement(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture_book(root, "books/base", '(in-package "ACL2")\n')
            top = '(in-package "ACL2")\n(include-book "base")\n'
            self.fixture_book(root, "books/top", top)
            sources = {f"{book}.lisp": proof_cost.certs.content_hash(
                root / f"{book}.lisp") for book in ("books/base", "books/top")}
            run = self.fixture_run("20260901T010000Z", sources=sources,
                                   walls={"books/top": 45.0})
            self.assertEqual(len(proof_cost.history(root, {"books/top"}, runs=[run])[0]), 1)
            self.fixture_book(root, "books/top", top + "; new own bytes\n")
            self.assertEqual(proof_cost.history(root, {"books/top"}, runs=[run])[0], {})
            self.fixture_book(root, "books/top", top)
            self.fixture_book(root, "books/base", '(in-package "ACL2")\n; new include bytes\n')
            self.assertEqual(proof_cost.history(root, {"books/top"}, runs=[run])[0], {})

    def test_host_and_toolchain_remain_separate_and_failed_cost_is_named(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture_book(root, "books/x", '(in-package "ACL2")\n')
            sources = {"books/x.lisp": proof_cost.certs.content_hash(
                root / "books/x.lisp")}
            runs = [
                self.fixture_run("20260901T010000Z", sources=sources,
                                 walls={"books/x": 50.0}),
                self.fixture_run("20260902T010000Z", host="persvati",
                                 sources=sources, walls={"books/x": 60.0}),
                self.fixture_run("20260903T010000Z", toolchain="tool-B",
                                 sources=sources, walls={"books/x": 70.0},
                                 results={"books/x": "failed"}),
            ]
            selected, _, _ = proof_cost.history(root, {"books/x"}, runs=runs)
            self.assertEqual(set(selected), {
                ("books/x", "hbox", "tool-A", "scoped"),
                ("books/x", "persvati", "tool-A", "scoped"),
                ("books/x", "hbox", "tool-B", "scoped")})
            self.assertEqual(selected[("books/x", "hbox", "tool-B", "scoped")].verdict,
                             "failed")
            filtered, _, _ = proof_cost.history(
                root, {"books/x"}, toolchain="tool-A", host="hbox", runs=runs)
            self.assertEqual(list(filtered), [("books/x", "hbox", "tool-A", "scoped")])

    def test_installed_only_and_never_measured_are_not_zero_cost(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for book in ("books/cached", "books/unseen"):
                self.fixture_book(root, book, '(in-package "ACL2")\n')
            source = {"books/cached.lisp": proof_cost.certs.content_hash(
                root / "books/cached.lisp")}
            run = self.fixture_run("20260901T010000Z", sources=source,
                                   walls={}, installed={"books/cached": "prior"})
            selected, installed, _ = proof_cost.history(
                root, {"books/cached", "books/unseen"}, runs=[run])
            self.assertEqual(selected, {})
            self.assertEqual(installed, {"books/cached"})
            lines = proof_cost.history_report(
                root, 10, books={"books/cached", "books/unseen"}, runs=[run])
            self.assertIn("unmeasured=2 installed-only=1", lines[0])
            self.assertIn("WARNING unmeasured: 2", "\n".join(lines))


    def measurement(self, book, seconds, host="hbox", tool="tool-A", run="certify-x",
                    jobs=2):
        record = proof_cost.Measurement(book, seconds, "passed", run, host, tool, jobs)
        return {(book, host, tool, record.band): record}

    def test_ratchet_fails_new_and_regressed_books_and_names_improved(self):
        selected = {}
        selected.update(self.measurement("books/new", 12.0))
        selected.update(self.measurement("books/held", 30.0))
        selected.update(self.measurement("books/held", 34.0, host="persvati"))
        selected.update(self.measurement("books/worse", 40.0))
        selected.update(self.measurement("books/fast", 4.0))
        baseline = {"books/held": {"seconds": 31.0}, "books/worse": {"seconds": 31.0},
                    "books/fast": {"seconds": 15.0}, "books/unmeasured": {"seconds": 20.0},
                    "books/gone": {"seconds": 20.0}}
        books = {"books/new", "books/held", "books/worse", "books/fast",
                 "books/unmeasured"}
        verdict = proof_cost.ratchet(selected, books, baseline, 10)
        failing = "\n".join(verdict.failing)
        self.assertEqual(len(verdict.failing), 2)
        self.assertIn("FAIL books/new: worst=12.000s > 10s", failing)
        self.assertIn("not in baseline", failing)
        # 40 > 31 * 1.25 = 38.75; the persvati 34s is within 25% of 31.
        self.assertIn("FAIL books/worse: worst=40.000s > baseline 31.000s +25% = 38.750s",
                      failing)
        self.assertNotIn("books/held", failing)
        self.assertTrue(any("KEPT books/held: worst=34.000s" in line
                            for line in verdict.kept))
        improved = "\n".join(verdict.improved)
        self.assertIn("IMPROVED books/fast", improved)
        self.assertIn("improved; remove from baseline", improved)
        self.assertIn("IMPROVED books/gone", improved)
        # Only-shrinking proposal: improved and gone dropped, nothing added,
        # held not raised, unmeasured kept.
        self.assertEqual(set(verdict.proposed),
                         {"books/held", "books/worse", "books/unmeasured"})
        self.assertEqual(verdict.proposed["books/held"]["seconds"], 31.0)

    def test_ratchet_lowers_a_faster_baseline_number(self):
        selected = self.measurement("books/held", 20.0, run="certify-new")
        verdict = proof_cost.ratchet(selected, {"books/held"},
                                     {"books/held": {"seconds": 31.0}}, 10)
        self.assertEqual(verdict.failing, [])
        self.assertEqual(verdict.proposed["books/held"],
                         {"seconds": 20.0, "run": "certify-new", "host": "hbox",
                          "jobs": 2, "verdict": "passed"})

    def test_write_baseline_refuses_to_add_without_allow_regression(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "baseline.json"
            selected = self.measurement("books/new", 12.0)
            computed = (selected, set(), 1)
            with mock.patch.object(proof_cost, "current_books", return_value={"books/new"}), \
                    mock.patch.object(proof_cost, "history", return_value=computed), \
                    mock.patch("sys.stdout"):
                self.assertEqual(proof_cost.main(["--baseline", str(path)]), 1)
                self.assertEqual(proof_cost.main(
                    ["--baseline", str(path), "--write-baseline"]), 1)
                self.assertFalse(path.exists())
                self.assertEqual(proof_cost.main(
                    ["--baseline", str(path), "--write-baseline",
                     "--allow-regression"]), 0)
                self.assertEqual(proof_cost.load_baseline(path)["books/new"]["seconds"], 12.0)
                self.assertEqual(proof_cost.main(["--baseline", str(path)]), 0)

    def test_allow_regression_keeps_unmeasured_baseline_entries(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "baseline.json"
            proof_cost.write_baseline(path, {
                "books/old": {"seconds": 40.0, "run": "r0", "host": "h", "verdict": "passed"}},
                10.0)
            selected = self.measurement("books/new", 12.0)
            computed = (selected, set(), 1)
            with mock.patch.object(proof_cost, "current_books",
                                   return_value={"books/new", "books/old"}), \
                    mock.patch.object(proof_cost, "history", return_value=computed), \
                    mock.patch("sys.stdout"):
                self.assertEqual(proof_cost.main(
                    ["--baseline", str(path), "--write-baseline",
                     "--allow-regression"]), 0)
            written = proof_cost.load_baseline(path)
            self.assertEqual(written["books/new"]["seconds"], 12.0)
            self.assertEqual(written["books/old"]["seconds"], 40.0,
                             "an allowance must not forget an unmeasured defect")

    # D26: the ten-second rule's number is the scoped (<= 2 jobs) measurement.

    def test_four_job_measurement_over_the_limit_does_not_fail(self):
        selected = self.measurement("books/wide", 30.0, jobs=4)
        verdict = proof_cost.ratchet(selected, {"books/wide"}, {}, 10)
        self.assertEqual(verdict.failing, [])
        self.assertEqual(verdict.proposed, {})
        self.assertEqual(proof_cost.regression_baseline(selected, 10), {})

    def test_two_job_measurement_over_the_limit_fails(self):
        # D30: ten to eleven seconds is the NEAR band (a warning that names
        # the run); above eleven an unbaselined book fails.
        for jobs in (1, 2):
            selected = self.measurement("books/scoped", 10.5, jobs=jobs)
            verdict = proof_cost.ratchet(selected, {"books/scoped"}, {}, 10)
            self.assertEqual(verdict.failing, [])
            self.assertTrue(any(f"NEAR books/scoped: worst=10.500s" in line and f"jobs={jobs}" in line
                                for line in verdict.kept), verdict.kept)
            selected = self.measurement("books/scoped", 11.5, jobs=jobs)
            verdict = proof_cost.ratchet(selected, {"books/scoped"}, {}, 10)
            self.assertEqual(len(verdict.failing), 1)
            self.assertIn(f"FAIL books/scoped: worst=11.500s > 10s host=hbox jobs={jobs}",
                          verdict.failing[0])

    def test_scoped_number_ratchets_while_a_wider_one_is_recorded(self):
        # The same book at 2 jobs (9 s) and at 4 jobs (17 s): the baseline
        # entry is improved by the scoped number; the wide one only prints.
        selected = {}
        selected.update(self.measurement("books/b", 9.0, host="persvati", jobs=2))
        selected.update(self.measurement("books/b", 17.0, host="hbox", jobs=4))
        verdict = proof_cost.ratchet(selected, {"books/b"},
                                     {"books/b": {"seconds": 17.0}}, 10)
        self.assertEqual(verdict.failing, [])
        self.assertIn("IMPROVED books/b: worst=9.000s", "\n".join(verdict.improved))
        self.assertEqual(verdict.proposed, {})

    def test_newer_wide_run_does_not_hide_the_scoped_measurement(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture_book(root, "books/x", '(in-package "ACL2")\n')
            sources = {"books/x.lisp": proof_cost.certs.content_hash(
                root / "books/x.lisp")}
            runs = [self.fixture_run("20260901T010000Z", sources=sources,
                                     walls={"books/x": 12.0}, jobs=2),
                    self.fixture_run("20260902T010000Z", sources=sources,
                                     walls={"books/x": 25.0}, jobs=8)]
            selected, _, _ = proof_cost.history(root, {"books/x"}, runs=runs)
            self.assertEqual(selected[("books/x", "hbox", "tool-A", "scoped")].seconds, 12.0)
            self.assertEqual(selected[("books/x", "hbox", "tool-A", "wide")].jobs, 8)
            lines = "\n".join(proof_cost.history_report(
                root, 10, books={"books/x"}, runs=runs))
            self.assertIn("WARNING books/x: process-wall=12.000s > 10s jobs=2", lines)
            self.assertIn("RECORDED books/x: process-wall=25.000s > 10s recorded at 8 jobs",
                          lines)
            self.assertNotIn("WARNING books/x: process-wall=25", lines)

    def test_manifest_without_jobs_is_unknown_skipped_and_named(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture_book(root, "books/x", '(in-package "ACL2")\n')
            sources = {"books/x.lisp": proof_cost.certs.content_hash(
                root / "books/x.lisp")}
            run = self.fixture_run("20260901T010000Z", sources=sources,
                                   walls={"books/x": 40.0}, jobs=None)
            selected, _, _ = proof_cost.history(root, {"books/x"}, runs=[run])
            self.assertEqual(list(selected), [("books/x", "hbox", "tool-A", "unknown")])
            self.assertEqual(proof_cost.ratchet(selected, {"books/x"}, {}, 10).failing, [])
            lines = "\n".join(proof_cost.history_report(
                root, 10, books={"books/x"}, runs=[run]))
            self.assertIn("WARNING jobs unknown: 1 manifest(s) without jobs_effective", lines)
            self.assertIn(run[0].run_id, lines)
            for bad in (0, True, "2", None):
                self.assertIsNone(proof_cost.manifest_jobs({"jobs_effective": bad}))

    def test_single_manifest_report_names_its_ratchet_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "manifest.json"
            for jobs, word in ((2, "eligible"), (4, "recorded only"), (None, "skipped")):
                value = {} if jobs is None else {"jobs_effective": jobs}
                path.write_text(json.dumps(value), encoding="utf-8")
                self.assertIn(f"ratchet: {word}",
                              "\n".join(proof_cost.report(path, 10)))


if __name__ == "__main__":
    unittest.main()

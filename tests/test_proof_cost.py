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
                    jobs=2, steps=None, load=1.0, cpus=24, verdict="passed"):
        # Quiet by default (load 1 on 24 CPUs): the seconds rules as before.
        record = proof_cost.Measurement(book, seconds, verdict, run, host, tool, jobs,
                                        steps, load, cpus)
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
        self.assertIn("FAIL books/new: best=12.000s > 10s", failing)
        self.assertIn("not in baseline", failing)
        # 40 > 31 * 1.25 = 38.75; the persvati 34s is within 25% of 31.
        self.assertIn("FAIL books/worse: best=40.000s > baseline 31.000s +25% = 38.750s",
                      failing)
        self.assertNotIn("books/held", failing)
        # The fastest measurement of the same bytes is the book's figure (load
        # only adds time): hbox's 30 s, not persvati's 34 s.
        improved = "\n".join(verdict.improved)
        self.assertIn("IMPROVED books/fast", improved)
        self.assertIn("improved; remove from baseline", improved)
        self.assertIn("IMPROVED books/gone", improved)
        # Only-shrinking proposal: improved and gone dropped, nothing added,
        # held not raised, unmeasured kept.
        self.assertEqual(set(verdict.proposed),
                         {"books/held", "books/worse", "books/unmeasured"})
        self.assertEqual(verdict.proposed["books/held"]["seconds"], 30.0)

    def test_near_line_adds_quiet_rows_ratchets_their_steps_and_drops_below(self):
        selected = {}
        selected.update(self.measurement("books/near", 6.0, steps=1000))
        selected.update(self.measurement("books/loud", 6.0, steps=1000, load=20.0))
        selected.update(self.measurement("books/small", 3.0, steps=100))
        selected.update(self.measurement("books/grew", 7.0, steps=1200))
        selected.update(self.measurement("books/shrunk", 4.0, steps=500))
        baseline = {"books/grew": {"seconds": 6.5, "steps": 1000},
                    "books/shrunk": {"seconds": 6.5, "steps": 900}}
        books = {"books/near", "books/loud", "books/small", "books/grew", "books/shrunk"}
        # Without --write-baseline nothing is added, but a near row is ratcheted.
        verdict = proof_cost.ratchet(selected, books, baseline, 10, near=5.0)
        self.assertEqual(len(verdict.failing), 1)
        self.assertIn("FAIL books/grew: steps=1,200 > baseline 1,000", verdict.failing[0])
        self.assertIn("IMPROVED books/shrunk", "\n".join(verdict.improved))
        self.assertNotIn("books/near", verdict.proposed)
        # With it: the quiet 6 s book gets a row; the loaded one and the 3 s do not.
        verdict = proof_cost.ratchet(selected, books, baseline, 10, near=5.0,
                                     add_near=True)
        self.assertIn("books/near", verdict.proposed)
        self.assertEqual(verdict.proposed["books/near"]["steps"], 1000)
        self.assertNotIn("books/loud", verdict.proposed)
        self.assertNotIn("books/small", verdict.proposed)
        self.assertNotIn("books/shrunk", verdict.proposed)
        # No near line: the old rule, a row under the threshold is improved.
        verdict = proof_cost.ratchet(selected, books, baseline, 10)
        self.assertEqual(verdict.failing, [])
        self.assertIn("IMPROVED books/grew", "\n".join(verdict.improved))

    def test_a_kept_steps_row_still_lowers_its_seconds(self):
        selected = self.measurement("books/cat", 6.4, steps=1050, run="certify-fast")
        verdict = proof_cost.ratchet(selected, {"books/cat"},
                                     {"books/cat": {"seconds": 10.36, "steps": 1000,
                                                    "run": "certify-old"}}, 10, near=5.0)
        self.assertEqual(verdict.failing, [])
        row = verdict.proposed["books/cat"]
        self.assertEqual((row["seconds"], row["steps"], row["run"]), (6.4, 1000, "certify-fast"))

    def test_near_seconds_round_trips_through_the_baseline(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "b.json"
            proof_cost.write_baseline(path, {"books/a": {"seconds": 6.0, "steps": 5}},
                                      10.0, 5.0)
            self.assertEqual(proof_cost.load_near(path), 5.0)
            proof_cost.write_baseline(path, {}, 10.0)
            self.assertIsNone(proof_cost.load_near(path))

    def aggregate_fixture(self, steps: dict[str, int]):
        # a <- b <- c (c includes b includes a) and d includes a: the heaviest
        # chain is the include path with the most summed steps.
        edges = {"books/a": [], "books/b": ["books/a"], "books/c": ["books/b"],
                 "books/d": ["books/a"]}
        selected = {}
        for book, count in steps.items():
            selected.update(self.measurement(book, 2.0, steps=count))
        best = proof_cost.decisive(selected)[0]
        return proof_cost.aggregate(best, set(edges), edges)

    def test_aggregate_sums_steps_and_finds_the_heaviest_include_chain(self):
        current = self.aggregate_fixture({"books/a": 100, "books/b": 10,
                                          "books/c": 1, "books/d": 50})
        self.assertTrue(current.complete)
        self.assertEqual(current.steps, 161)
        self.assertEqual(current.seconds, 8.0)
        # d -> a (150) outweighs c -> b -> a (111) although it is shallower.
        self.assertEqual((current.chain_steps, current.chain), (150, ("books/d", "books/a")))
        self.assertEqual(current.chain_seconds, 4.0)

    def test_aggregate_is_partial_and_never_fails_with_an_unmeasured_book(self):
        current = self.aggregate_fixture({"books/a": 100, "books/b": 10, "books/c": 1})
        self.assertFalse(current.complete)
        lines, failing = proof_cost.aggregate_verdict(
            current, {"books": 4, "steps": 1, "chain_steps": 1})
        self.assertEqual(failing, [])
        self.assertIn("AGGREGATE PARTIAL", lines[0])
        self.assertIn("not a verdict", lines[0])

    def test_aggregate_fails_over_its_recorded_tolerance_and_passes_within(self):
        current = self.aggregate_fixture({"books/a": 100, "books/b": 10,
                                          "books/c": 1, "books/d": 50})
        within = {"books": 4, "steps": 150, "chain_steps": 140, "tolerance": 0.10}
        lines, failing = proof_cost.aggregate_verdict(current, within)
        self.assertEqual(failing, [])
        self.assertIn("within 10%", lines[0])
        over = {"books": 4, "steps": 140, "chain_steps": 150, "tolerance": 0.10}
        lines, failing = proof_cost.aggregate_verdict(current, over)
        self.assertEqual(lines, [])
        self.assertEqual(len(failing), 1)
        self.assertIn("FAIL AGGREGATE steps=161 > recorded 140 +10% = 154", failing[0])
        # No recorded convergence: reported, never failing.
        lines, failing = proof_cost.aggregate_verdict(current, None)
        self.assertEqual(failing, [])
        self.assertIn("--write-aggregate", lines[0])

    def test_write_aggregate_refuses_partial_and_over_tolerance_and_keeps_rows(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "b.json"
            rows = {"books/a": {"seconds": 6.0, "steps": 5}}
            partial = self.aggregate_fixture({"books/a": 100})
            self.assertEqual(proof_cost.write_aggregate(
                path, rows, 5.0, 10.0, partial, None, [], False, None), 1)
            self.assertFalse(path.exists())
            current = self.aggregate_fixture({"books/a": 100, "books/b": 10,
                                              "books/c": 1, "books/d": 50})
            self.assertEqual(proof_cost.write_aggregate(
                path, rows, 5.0, 10.0, current, None, [], False, None), 0)
            recorded = proof_cost.load_aggregate(path)
            self.assertEqual((recorded["steps"], recorded["chain_steps"],
                              recorded["tolerance"]), (161, 150, 0.10))
            self.assertEqual(proof_cost.load_baseline(path), rows)
            self.assertEqual(proof_cost.load_near(path), 5.0)
            # --write-baseline keeps the recorded aggregate.
            proof_cost.write_baseline(path, {}, 10.0, 5.0, recorded)
            self.assertEqual(proof_cost.load_aggregate(path)["steps"], 161)
            # Over tolerance: refused without --allow-regression, taken with it.
            _, failing = proof_cost.aggregate_verdict(
                current, {"books": 4, "steps": 100, "chain_steps": 100})
            self.assertEqual(proof_cost.write_aggregate(
                path, {}, 5.0, 10.0, current, recorded, failing, False, None), 1)
            self.assertEqual(proof_cost.write_aggregate(
                path, {}, 5.0, 10.0, current, recorded, failing, True, 0.05), 0)
            self.assertEqual(proof_cost.load_aggregate(path)["tolerance"], 0.05)

    def test_a_malformed_recorded_aggregate_is_refused_by_name(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "b.json"
            path.write_text(json.dumps({"books": {}, "aggregate": {"steps": "many"}}))
            with self.assertRaisesRegex(ValueError, "aggregate needs"):
                proof_cost.load_aggregate(path)

    def test_ratchet_lowers_a_faster_baseline_number(self):
        selected = self.measurement("books/held", 20.0, run="certify-new")
        verdict = proof_cost.ratchet(selected, {"books/held"},
                                     {"books/held": {"seconds": 31.0}}, 10)
        self.assertEqual(verdict.failing, [])
        self.assertEqual(verdict.proposed["books/held"],
                         {"seconds": 20.0, "run": "certify-new", "host": "hbox",
                          "jobs": 2, "verdict": "passed", "load": 1.0, "cpus": 24})

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
            self.assertTrue(any(f"NEAR books/scoped: best=10.500s" in line and f"jobs={jobs}" in line
                                for line in verdict.kept), verdict.kept)
            selected = self.measurement("books/scoped", 11.5, jobs=jobs)
            verdict = proof_cost.ratchet(selected, {"books/scoped"}, {}, 10)
            self.assertEqual(len(verdict.failing), 1)
            self.assertIn(f"FAIL books/scoped: best=11.500s > 10s steps=unknown "
                          f"load=1/24cpu (quiet) host=hbox jobs={jobs}",
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
        self.assertIn("IMPROVED books/b: best=9.000s", "\n".join(verdict.improved))
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


    # 2026-09-27: steps are the ratchet; seconds decide D26 only when quiet.

    def test_failed_fast_attempt_is_failed_never_improved(self):
        # A book that failed in 0.06 s measured no cost: FAILED, row kept.
        selected = self.measurement("books/red", 0.06, verdict="failed")
        verdict = proof_cost.ratchet(selected, {"books/red"},
                                     {"books/red": {"seconds": 30.0, "steps": 900}}, 10)
        self.assertEqual(verdict.improved, [])
        self.assertEqual(verdict.failing, [])
        self.assertEqual(len(verdict.failed), 1)
        self.assertIn("FAILED books/red", verdict.failed[0])
        self.assertIn("measures no cost", verdict.failed[0])
        self.assertEqual(verdict.proposed["books/red"], {"seconds": 30.0, "steps": 900})

    def test_failed_attempt_never_replaces_a_passed_one(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture_book(root, "books/x", '(in-package "ACL2")\n')
            sources = {"books/x.lisp": proof_cost.certs.content_hash(
                root / "books/x.lisp")}
            runs = [self.fixture_run("20260901T010000Z", sources=sources,
                                     walls={"books/x": 25.0}),
                    self.fixture_run("20260902T010000Z", sources=sources,
                                     walls={"books/x": 0.06},
                                     results={"books/x": "failed"})]
            selected, _, _ = proof_cost.history(root, {"books/x"}, runs=runs)
            record = selected[("books/x", "hbox", "tool-A", "scoped")]
            self.assertEqual((record.seconds, record.verdict), (25.0, "passed"))
            verdict = proof_cost.ratchet(selected, {"books/x"},
                                         {"books/x": {"seconds": 25.0}}, 10)
            self.assertEqual(verdict.improved, [])

    def test_fastest_passed_attempt_of_the_same_bytes_is_kept_with_its_load(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture_book(root, "books/x", '(in-package "ACL2")\n')
            sources = {"books/x.lisp": proof_cost.certs.content_hash(
                root / "books/x.lisp")}
            quiet = self.fixture_run("20260901T010000Z", sources=sources,
                                     walls={"books/x": 6.4})
            quiet[1].update({"book_load_average": {"books/x": [2.0, 3.5]},
                             "cpu_count": 24, "book_prover_steps": {"books/x": 1488179}})
            loaded = self.fixture_run("20260902T010000Z", sources=sources,
                                      walls={"books/x": 14.9})
            loaded[1].update({"book_load_average": {"books/x": [15.0, 12.0]},
                              "cpu_count": 24})
            selected, _, _ = proof_cost.history(root, {"books/x"}, runs=[quiet, loaded])
            record = selected[("books/x", "hbox", "tool-A", "scoped")]
            self.assertEqual((record.seconds, record.steps, record.load, record.cpus),
                             (6.4, 1488179, 3.5, 24))
            self.assertIs(record.quiet, True)
            verdict = proof_cost.ratchet(selected, {"books/x"},
                                         {"books/x": {"seconds": 14.9}}, 10)
            self.assertIn("IMPROVED books/x: best=6.400s", "\n".join(verdict.improved))
            self.assertEqual(verdict.proposed, {})

    def test_loaded_or_unrecorded_measurement_over_the_line_is_unquiet_not_fail(self):
        for load, cpus in ((12.0, 24), (None, None)):
            selected = self.measurement("books/new", 17.0, load=load, cpus=cpus)
            verdict = proof_cost.ratchet(selected, {"books/new"}, {}, 10)
            self.assertEqual(verdict.failing, [], (load, cpus))
            self.assertEqual(len(verdict.unquiet), 1)
            self.assertIn("UNQUIET books/new: best=17.000s", verdict.unquiet[0])
            self.assertIn("not a verdict", verdict.unquiet[0])
            self.assertEqual(proof_cost.regression_baseline(selected, 10), {})
        # Above LOAD_FACTOR times the line no load explains it: FAIL.
        selected = self.measurement("books/new", 34.0, load=20.0)
        verdict = proof_cost.ratchet(selected, {"books/new"}, {}, 10)
        self.assertEqual(len(verdict.failing), 1)
        self.assertIn("FAIL books/new: best=34.000s", verdict.failing[0])
        # A quiet measurement over the line is a verdict.
        selected = self.measurement("books/new", 12.0, load=6.0, cpus=24)
        self.assertEqual(len(proof_cost.ratchet(selected, {"books/new"}, {}, 10).failing), 1)
        selected = self.measurement("books/new", 12.0, load=6.1, cpus=24)
        self.assertEqual(proof_cost.ratchet(selected, {"books/new"}, {}, 10).failing, [])

    def test_steps_ratchet_a_baseline_book_whatever_its_seconds(self):
        baseline = {"books/b": {"seconds": 30.0, "steps": 1_000_000, "run": "r0"}}
        # Seconds far above the row under load, steps unchanged: no failure.
        selected = self.measurement("books/b", 80.0, steps=1_000_000, load=20.0)
        verdict = proof_cost.ratchet(selected, {"books/b"}, baseline, 10)
        self.assertEqual((verdict.failing, verdict.unquiet), ([], []))
        self.assertEqual(verdict.proposed["books/b"]["steps"], 1_000_000)
        self.assertEqual(verdict.proposed["books/b"]["seconds"], 30.0)
        # Quiet seconds under the row, steps 11% over: FAIL on steps.
        selected = self.measurement("books/b", 20.0, steps=1_110_000)
        verdict = proof_cost.ratchet(selected, {"books/b"}, baseline, 10)
        self.assertEqual(len(verdict.failing), 1)
        self.assertIn("FAIL books/b: steps=1,110,000 > baseline 1,000,000 +10%",
                      verdict.failing[0])
        self.assertEqual(verdict.proposed["books/b"], baseline["books/b"])
        # Within the band: KEPT, not raised.
        selected = self.measurement("books/b", 20.0, steps=1_050_000)
        verdict = proof_cost.ratchet(selected, {"books/b"}, baseline, 10)
        self.assertEqual(verdict.failing, [])
        self.assertIn("KEPT books/b: steps=1,050,000", "\n".join(verdict.kept))
        self.assertEqual(verdict.proposed["books/b"]["steps"], 1_000_000)
        # Fewer steps and a faster run: both numbers lowered.
        selected = self.measurement("books/b", 20.0, steps=400_000, run="r1")
        verdict = proof_cost.ratchet(selected, {"books/b"}, baseline, 10)
        self.assertEqual((verdict.proposed["books/b"]["steps"],
                          verdict.proposed["books/b"]["seconds"],
                          verdict.proposed["books/b"]["run"]), (400_000, 20.0, "r1"))

    def test_row_without_steps_uses_seconds_under_the_quiet_rule_and_gains_steps(self):
        baseline = {"books/b": {"seconds": 20.0}}
        loaded = self.measurement("books/b", 40.0, load=None, cpus=None)
        verdict = proof_cost.ratchet(loaded, {"books/b"}, baseline, 10)
        self.assertEqual(verdict.failing, [])
        self.assertIn("UNQUIET books/b", "\n".join(verdict.unquiet))
        quiet = self.measurement("books/b", 40.0)
        self.assertEqual(len(proof_cost.ratchet(quiet, {"books/b"}, baseline, 10).failing), 1)
        faster = self.measurement("books/b", 15.0, steps=700)
        proposed = proof_cost.ratchet(faster, {"books/b"}, baseline, 10).proposed
        self.assertEqual((proposed["books/b"]["seconds"], proposed["books/b"]["steps"]),
                         (15.0, 700))

    def test_steps_come_from_the_local_log_when_the_manifest_lacks_them(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture_book(root, "books/x", '(in-package "ACL2")\n')
            sources = {"books/x.lisp": proof_cost.certs.content_hash(
                root / "books/x.lisp")}
            run = self.fixture_run("20260901T010000Z", sources=sources,
                                   walls={"books/x": 12.0})
            log = root / "build/acl2" / run[0].run_id / "books--x.certify.log"
            log.parent.mkdir(parents=True)
            log.write_text(
                "Summary\nForm:  ( DEFTHM A ...)\nTime:  1.00 seconds\n"
                "Prover steps counted:  700\n"
                "Summary\nForm:  ( ENCAPSULATE NIL ...)\nTime:  9.00 seconds\n"
                "Prover steps counted:  5,000\n"
                "Summary\nForm:  ( DEFTHM B ...)\nTime:  2.00 seconds\n"
                "Prover steps counted:  4300\n"
                "Summary\nForm:  (CERTIFY-BOOK \"books/x\" ...)\n"
                "Time:  12.00 seconds (prove: 3.00)\nProver steps counted:  5000\n")
            selected, _, _ = proof_cost.history(root, {"books/x"}, runs=[run])
            self.assertEqual(selected[("books/x", "hbox", "tool-A", "scoped")].steps, 5000)
            detail = proof_cost.event_detail(log)
            self.assertIn("costliest-event=( DEFTHM B ...) 4,300 steps", detail)


class Acl2CostTests(unittest.TestCase):
    def test_book_steps_are_the_certify_book_summary_or_unknown(self):
        from tools import acl2_cost
        passed = ("Summary\nForm:  ( DEFTHM A ...)\nTime:  0.5 seconds\n"
                  "Prover steps counted:  More than 1,000\n"
                  "Summary\nForm:  (CERTIFY-BOOK \"b\" ...)\nTime:  3.0 seconds\n"
                  "Prover steps counted:  299345\n")
        self.assertEqual(acl2_cost.book_steps(passed), 299345)
        self.assertTrue(acl2_cost.events(passed)[0].capped)
        self.assertEqual(acl2_cost.book_steps("Summary\nForm:  ( DEFTHM A ...)\n"
                                              "Time:  0.5 seconds\n"), None)
        self.assertEqual(acl2_cost.book_steps(
            "Summary\nForm:  (CERTIFY-BOOK \"b\" ...)\nTime:  0.1 seconds\n"), 0)
        self.assertIsNone(acl2_cost.costliest_event(""))


if __name__ == "__main__":
    unittest.main()

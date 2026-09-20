"""tools/scale_gate.py against a local fake host: no ssh, no ACL2, no network.

Two whole runs of the gate are under test.

* `CeilingTests` runs it against a fake series whose recover curve crosses the
  ceiling it was given, a fake reader with no OVER, and the fake `generate`
  and `measure` of the like-for-like phase. It requires the gate to stop where
  the fake stops, to name the largest passing store, to render every table,
  to record the OVER substitution as a gap rather than as an OVER figure, and
  to put a ratio against the cited pre-realignment number.
* `PartialCurveTests` makes the series die mid-post, the way a real one dies
  when the bridge's prompt deadline passes. The points already measured must
  survive into the evidence -- that is the open item
  `planning/lanes/HANDOFF-w3-scale-profile.md` recorded, and the reason the
  series writes its JSON from a `finally`.

A green run here says the harness works. Every number in the tables comes
from a fake in `tests/`; nothing here is evidence about fn.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import scale_gate  # noqa: E402

FAKE_ACL2 = "#!/bin/sh\necho 'ACL2 Version 8.7 fake'\ncat > /dev/null\nexit 0\n"


class DryRun:
    """One whole gate run against fake host tooling in a temporary HOME."""

    extra_argv: list = []
    environment: dict = {}

    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="fn-scale-gate-")
        cls.home = Path(cls.temp.name) / "home"
        acl2 = cls.home / "fn-tools/acl2-8.7"
        acl2.mkdir(parents=True)
        (acl2 / "saved_acl2").write_text(FAKE_ACL2)
        (acl2 / "saved_acl2").chmod(0o755)
        commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                stdout=subprocess.PIPE, check=True).stdout.decode().strip()
        cls.rev = commit[:7]
        books = cls.home / "fn-gates/dev-{}/books".format(cls.rev)
        books.mkdir(parents=True)
        (books / "acceptance.cert").write_text("(:CERT fake)\n")
        (books / "acceptance.port").write_text("()\n")
        cls.evidence = Path(cls.temp.name) / "scale-evidence.md"
        argv = [commit, "--dry-run", "--home", str(cls.home), "--repo", str(ROOT),
                "--evidence", str(cls.evidence), "--keep",
                "--overlay", str(ROOT / "tests/deploy_gate_fake"),
                "--overlay", str(ROOT / "tests/scale_gate_fake"),
                "--payload", "1024", "--start", "8", "--max-articles", "64",
                "--recover-ceiling", "20", "--connections", "7"] + cls.extra_argv
        restore = {key: os.environ.get(key) for key in cls.environment}
        os.environ.update(cls.environment)
        try:
            cls.code = scale_gate.main(argv)
        finally:
            for key, value in restore.items():
                if value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = value
        cls.text = cls.evidence.read_text()

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def section(self, title):
        out, inside = [], False
        for line in self.text.splitlines():
            if line.startswith("## "):
                inside = line.strip().lstrip("#").strip() == title
                continue
            if inside:
                out.append(line)
        return "\n".join(out)

    def failures(self):
        return [line for line in self.text.splitlines() if " FAIL " in line]


class CeilingTests(DryRun, unittest.TestCase):
    """The series stops at a ceiling, and every table is rendered from it."""

    def test_the_gate_is_green_and_no_step_failed(self):
        self.assertEqual(self.code, 0, "\n".join(self.failures()))
        self.assertEqual(self.failures(), [])

    def test_the_series_table_holds_every_measured_point(self):
        table = self.section("The series: one store, grown by doubling")
        self.assertIn("### 1024 octets per article", table)
        for size in (8, 16, 32):
            self.assertRegex(table, r"\| {} \| \d+ \|".format(size))
        self.assertNotIn("| 64 |", table)          # the series stopped before it

    def test_the_stop_is_the_ceiling_that_was_crossed(self):
        table = self.section("The series: one store, grown by doubling")
        self.assertIn("Stopped by: recover took 29.4 s, over the 20 s ceiling", table)
        self.assertIn("Largest passing store: 16 articles", table)

    def test_the_largest_store_fact_separates_passing_from_measured(self):
        self.assertIn("| largest store | 16 articles of 1024 octets inside both "
                      "ceilings; 32 measured |", self.text)

    def test_every_operation_has_a_pessimistic_sentence_with_its_scope(self):
        ceiling = self.section("The ceiling per operation")
        for operation in ("**post, 1024 octets**", "**recover, 1024 octets**",
                          "**`run_store.py recover`**", "**GROUP**",
                          "**ARTICLE by number**", "**a connection**",
                          "**where the reopen's seconds go**"):
            self.assertIn(operation, ceiling)
        # every bullet is an operation, and every operation carries its scope
        self.assertEqual(ceiling.count("Scope:"), ceiling.count("- **"))

    def test_the_post_sentence_quotes_the_deadline_the_call_was_racing(self):
        ceiling = self.section("The ceiling per operation")
        self.assertIn("against the 20.0 s prompt deadline that call was racing",
                      ceiling)

    def test_the_profile_names_where_the_reopen_spent_its_seconds(self):
        self.assertIn("fn-store-sn-recover took 28.9 s over 1 calls",
                      self.section("The ceiling per operation"))

    def test_over_is_recorded_as_a_substitution_and_never_as_over(self):
        ceiling = self.section("The ceiling per operation")
        self.assertIn("**OVER-equivalent over the full range**", ceiling)
        self.assertNotIn("- **OVER over the full range**", ceiling)
        self.assertIn("it is a substitution, not OVER", ceiling)
        self.assertIn("OVER is not served on this commit",
                      self.section("What was NOT exercised"))

    def test_the_reader_table_covers_the_whole_range_and_the_connections(self):
        reader = self.section("The reader at the largest store")
        self.assertIn("| GROUP fn.letters (32 articles) |", reader)
        self.assertIn("| OVER 1-32 |", reader)
        self.assertIn("| LISTGROUP + 32 HEADs (OVER substitution) |", reader)
        self.assertIn("| 7 sequential connections, total |", reader)

    def test_the_connections_all_completed(self):
        reader = self.section("The ceiling per operation")
        self.assertIn("7 of 7 sequential connections completed", reader)

    def test_the_comparison_runs_the_previous_method_and_cites_its_table(self):
        table = self.section("Like for like with the pre-realignment measurement")
        self.assertIn("planning/lanes/HANDOFF-w3-scale-profile.md", table)
        self.assertIn("0.793", table)              # the cited N=16 reopen median
        self.assertIn("12.729", table)             # the cited N=256 reopen median
        for count in scale_gate.PREVIOUS_METHOD_POINTS:
            self.assertRegex(table, r"\| {} \| \d".format(count))
        self.assertRegex(table, r"\| \d+\.\d+x \|")   # a ratio was computed

    def test_the_hundred_connection_default_is_the_shipped_one(self):
        """The test runs seven; the gate a lane runs must ask for a hundred."""
        parsed = scale_gate.main.__globals__["argparse"]
        self.assertIsNotNone(parsed)
        parser = [line for line in Path(ROOT / "tools/scale_gate.py").read_text()
                  .splitlines() if '"--connections"' in line]
        self.assertTrue(any("default=100" in line for line in parser), parser)


class PartialCurveTests(DryRun, unittest.TestCase):
    """A series that dies mid-post keeps the points it already measured."""

    extra_argv = ["--skip-previous"]
    environment = {"FN_FAKE_SERIES_DIE": "32"}

    def test_the_gate_still_renders_and_names_the_death(self):
        self.assertEqual(self.code, 0, "\n".join(self.failures()))
        self.assertIn("StoreError: ACL2 prompt timeout", self.text)

    def test_the_partial_point_survives_with_the_posts_it_did_make(self):
        table = self.section("The series: one store, grown by doubling")
        self.assertRegex(table, r"\| 32 \| 8 \|")   # eight of sixteen posts landed
        self.assertIn("- N=32: StoreError: ACL2 prompt timeout", table)

    def test_the_nonzero_exit_of_the_series_is_a_gap_not_a_pass(self):
        gaps = self.section("What was NOT exercised")
        self.assertIn("the 1024 octet series exited 3", gaps)
        self.assertIn("not measured, not absent", gaps)

    def test_the_reader_still_measured_the_store_that_survived(self):
        self.assertIn("| GROUP fn.letters (24 articles) |",
                      self.section("The reader at the largest store"))

    def test_the_like_for_like_phase_is_a_skip_and_never_a_pass(self):
        self.assertIn("--skip-previous", self.section("What was NOT exercised"))
        self.assertIn("The like-for-like phase did not run.",
                      self.section("Like for like with the pre-realignment measurement"))


if __name__ == "__main__":
    unittest.main()


class ReuseAndAdoptTests(DryRun, unittest.TestCase):
    """A four-hour series is measured once; a later invocation adopts it.

    The first run here is `CeilingTests`' own: this class runs the gate a
    second time against the same fake HOME with `--reuse`, adopting the 1024
    octet series from the JSON the first run left on the host. The tree and
    its stores must survive, the tables must be rendered from the adopted
    file, and the adoption must appear as a gap -- the steps that produced
    those numbers are the earlier run's.
    """

    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        series = cls.home / "fn-deploy/{}/gate-run/series-1024.json".format(cls.rev)
        cls.adopted = json.loads(series.read_text())
        second = Path(cls.temp.name) / "scale-evidence-2.md"
        argv = [cls.rev, "--dry-run", "--home", str(cls.home), "--repo", str(ROOT),
                "--evidence", str(second), "--keep", "--reuse", "--skip-previous",
                "--overlay", str(ROOT / "tests/deploy_gate_fake"),
                "--overlay", str(ROOT / "tests/scale_gate_fake"),
                "--adopt-series", "1024={}".format(series),
                "--payload", "1024", "--start", "8", "--max-articles", "8",
                "--connections", "3"]
        cls.second_code = scale_gate.main(argv)
        cls.text = second.read_text()

    def test_the_second_run_is_green_and_kept_the_stores(self):
        self.assertEqual(self.second_code, 0, "\n".join(self.failures()))
        self.assertIn("REUSING", self.text)

    def test_the_adopted_series_is_what_the_tables_report(self):
        table = self.section("The series: one store, grown by doubling")
        self.assertIn("Largest passing store: {} articles".format(
            self.adopted["largest_passing"]), table)
        self.assertIn(self.adopted["stopped_by"], table)

    def test_an_adopted_payload_is_not_measured_a_second_time(self):
        self.assertNotIn("| series 1024 octets |", self.text)
        self.assertIn("| adopt series 1024 octets |", self.text)

    def test_the_overlays_are_pushed_even_though_there_is_no_ship(self):
        """An overlay under --reuse must still reach the tree, or the gate
        measures the file the earlier run left there."""
        pushed = [line for line in self.text.splitlines()
                  if line.startswith("| ") and "| overlay tests/bench/" in line]
        self.assertTrue(pushed, "no overlay step in the reuse run")

    def test_the_adoption_is_recorded_as_a_gap(self):
        self.assertIn("was measured by an earlier invocation of this gate",
                      self.section("What was NOT exercised"))

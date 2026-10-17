"""tools/certify_triage.py: a certify run's failures, told apart.

The three fixtures in `tests/fixtures/certify_triage/` are unmodified excerpts
of per-book logs from the hbox run of 2026-10-04 whose raw
`grep -l "FAILED\\|ACL2 Error"` said 297 red:

  books--consumer-reason.real-excerpt.log   a defthm refused, with its key
                                            checkpoint (a real red)
  books--acceptance-payload-ref.cascade.log  refused at `include-book "owner"`
                                            for want of a certificate
  books--peer-pull.echo-excerpt.log          a PASSED book whose echoed source
                                            contains `:FAILED`

The other kinds need no real log to be told apart: a limit and a killed book
are decided by the exit code the manifest or `*.active.json` carries.
"""

from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import certify_triage  # noqa: E402

FIXTURES = ROOT / "tests" / "fixtures" / "certify_triage"


def fixture(name: str) -> str:
    return (FIXTURES / name).read_text(encoding="utf-8")


class ClassifyTests(unittest.TestCase):
    def test_real_red_carries_its_checkpoint(self) -> None:
        row = certify_triage.classify(
            "books/consumer-reason", fixture("books--consumer-reason.real-excerpt.log"), 0)
        self.assertEqual(row["kind"], "real")
        self.assertIn("FN-NCR-PRINTED-REASON-IS-THE-DECISIONS", row["detail"])
        self.assertTrue(row["checkpoint"].startswith("*** Key checkpoint"))
        self.assertIn("Subgoal 27'", row["checkpoint"])

    def test_missing_certificate_is_a_cascade_naming_its_cause(self) -> None:
        row = certify_triage.classify(
            "books/acceptance-payload-ref",
            fixture("books--acceptance-payload-ref.cascade.log"), 0)
        self.assertEqual(row["kind"], "cascade")
        self.assertIn("owner", row["detail"])

    def test_passed_book_with_failed_in_its_source_is_echo_not_red(self) -> None:
        text = fixture("books--peer-pull.echo-excerpt.log")
        self.assertIn("FAILED", text)
        row = certify_triage.classify("books/peer-pull", text, 0)
        self.assertEqual(row["kind"], "echo")

    def test_passed_book_with_a_real_error_line_is_must_fail(self) -> None:
        text = fixture("books--peer-pull.echo-excerpt.log") + "\nACL2 Error in ( THM ...): x\n"
        self.assertEqual(certify_triage.classify("b", text, 0)["kind"], "must-fail")

    def test_exit_code_decides_killed_and_limit(self) -> None:
        text = fixture("books--consumer-reason.real-excerpt.log")
        self.assertEqual(certify_triage.classify("b", text, 143)["kind"], "killed")
        self.assertEqual(certify_triage.classify("b", text, "timed out after 900s")["kind"], "limit")

    def test_failure_with_no_error_text_is_other(self) -> None:
        self.assertEqual(certify_triage.classify("b", "nothing here\n", 0)["kind"], "other")

    def test_manifest_verdict_overrides_marker_search(self) -> None:
        manifest = {"book_results": {"books/peer-pull": "failed"}}
        row = certify_triage.classify(
            "books/peer-pull", fixture("books--peer-pull.echo-excerpt.log"), 0, manifest)
        self.assertEqual(row["kind"], "other")


class RunTests(unittest.TestCase):
    def test_run_directory_counts_and_exit_code(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            directory = Path(raw)
            for name, book in (("books--consumer-reason.real-excerpt.log", "books--consumer-reason"),
                               ("books--acceptance-payload-ref.cascade.log", "books--acceptance-payload-ref"),
                               ("books--peer-pull.echo-excerpt.log", "books--peer-pull")):
                (directory / (book + ".certify.log")).write_text(fixture(name))
            (directory / "certify.log").write_text("combined log, not a book\n")
            rows = certify_triage.triage_run(directory)
            kinds = sorted(row["kind"] for row in rows)
            self.assertEqual(kinds, ["cascade", "echo", "real"])
            tsv = directory / "out" / "t.tsv"
            self.assertEqual(certify_triage.main([str(directory), "--tsv", str(tsv)]), 1)
            self.assertEqual(len(tsv.read_text().splitlines()), 4)

    def test_empty_directory_is_exit_2(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            self.assertEqual(certify_triage.main([raw]), 2)


if __name__ == "__main__":
    unittest.main()

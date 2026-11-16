"""Distinguish an unfinished live-run log from a terminal proof failure."""
import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import certify_triage as triage


class TerminalResults(unittest.TestCase):
    def test_unfinished_log_is_not_a_failure_or_a_liveness_claim(self):
        for text in ("ACL2 !> (certify-book ...)",
                     "ACL2 Error in ( DEFTHM EXPECTED-NEGATIVE ...): refused\n"):
            row = triage.classify("books/example", text, None)
            self.assertEqual(row["kind"], "incomplete")
            self.assertIn("liveness not established", row["detail"])

    def test_terminal_failures_are_not_hidden(self):
        self.assertEqual(triage.classify("books/example", "", 0)["kind"], "other")
        self.assertEqual(triage.classify("books/example", "", -15)["kind"], "killed")
        row = triage.classify("books/example", "", None,
                             {"book_results": {"books/example": "failed"}})
        self.assertEqual(row["kind"], "other")

    def test_success_marker_can_precede_exit_metadata(self):
        marker = "FN_CERTIFY_SUCCESS " + "a" * 32 + " " + "b" * 12 + "\n"
        self.assertEqual(triage.classify("books/example", marker, None)["kind"], "clean")

    def test_existing_failure_and_echo_fixtures_keep_their_meaning(self):
        fixtures = Path(__file__).parent / "fixtures" / "certify_triage"
        for filename, kind in (("books--consumer-reason.real-excerpt.log", "real"),
                               ("books--acceptance-payload-ref.cascade.log", "cascade"),
                               ("books--peer-pull.echo-excerpt.log", "echo")):
            manifest = {"book_results": {"books/example": "passed"}} if kind == "echo" else {}
            with self.subTest(kind=kind):
                row = triage.classify("books/example", (fixtures / filename).read_text(),
                                      0 if kind == "echo" else 1, manifest)
                self.assertEqual(row["kind"], kind)

    def test_live_run_exit_is_distinct_and_failure_takes_precedence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "books--example.certify.log").write_text("ACL2 !>\n")
            active = root / "books--example.active.json"
            active.write_text(json.dumps({"status": "running", "pid": 12345}))
            with contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(triage.main([directory]), 3)
            self.assertIn("incomplete 1", output.getvalue())
            self.assertNotIn("OTHER books/example", output.getvalue())
            active.write_text(json.dumps({"status": "exited", "exit_code": -15}))
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(triage.main([directory]), 1)


if __name__ == "__main__":
    unittest.main()

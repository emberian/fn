"""Matching-image physical consumer of the captured decision-journal prefix."""
import os
import unittest
from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, EXIT_FAULT, environment, native_image, requires,
    run, scratch)

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")


@requires(DEVELOPER)
class NativeJournalStreamTests(unittest.TestCase):
    def setUp(self):
        self.root = scratch(self, "fn-journal-stream-")
        (self.root / "decisions").mkdir()
        self.journal = self.root / "decisions" / "decisions.fnj"

    def invoke(self, timeout=60):
        return run([DEVELOPER, "--fn", "store", self.root, "journal"],
                   timeout=timeout, env=environment({}))

    def test_large_journal_reports_every_complete_entry(self):
        self.journal.write_bytes(b"0 0 0 0 0 0 0\n" * 160000)
        answer = self.invoke()
        self.assertEqual(answer.returncode, EXIT_OK, answer.stdout + answer.stderr)
        self.assertEqual(answer.stdout,
                         b"journal: entries=160000 segments=160000 status=whole replay=agrees\n")

    def test_symlink_is_rejected(self):
        target = self.root / "target"
        target.write_bytes(b"0 0 0 0 0 0 0\n")
        self.journal.symlink_to(target)
        answer = self.invoke(timeout=5)
        self.assertEqual(answer.returncode, EXIT_FAULT, answer.stdout + answer.stderr)
        self.assertIn(b"non-regular", answer.stderr)
        self.assertFalse(answer.stdout)

    def test_fifo_is_rejected_without_waiting_for_a_writer(self):
        os.mkfifo(self.journal)
        answer = self.invoke(timeout=5)
        self.assertEqual(answer.returncode, EXIT_FAULT, answer.stdout + answer.stderr)
        self.assertIn(b"non-regular", answer.stderr)
        self.assertFalse(answer.stdout)

    def test_absent_journal_is_refused(self):
        answer = self.invoke(timeout=5)
        self.assertEqual(answer.returncode, EXIT_REFUSED, answer.stdout + answer.stderr)
        self.assertIn(b"no decision journal", answer.stderr)

    def test_report_keeps_first_gap_and_counts_later_rejected_segments(self):
        self.journal.write_bytes(
            b"0 0 0 1" + b"0" * 100 + b" 1 0 0\n"
            b"1 5 0 1 2 0 0\n3 5 0 1 2 0 0\n"
            b"999 0 0 0 0 0 0 0 0 0 0\n"
            b"0 0 0 1700000000 1 0 0\n1 5 0 1 2 0 0\n\xff")
        answer = self.invoke()
        self.assertEqual(answer.returncode, 1, answer.stdout + answer.stderr)
        self.assertEqual(
            answer.stdout,
            b"journal: entries=6 segments=3 status=malformed replay=gap-at-2\n")


if __name__ == "__main__":
    unittest.main()

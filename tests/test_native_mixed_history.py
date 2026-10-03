"""Empirical promise-history teeth; these do not run or model a native node."""
import copy
from pathlib import Path
import tempfile
import unittest

from tools.native_mixed_workload import check_history, wire_outcome
from tools.resilience.journal import Journal, TruncatedHistory


def observed():
    recipe = dict(initial=["prior"], writers={"writer": ["new"]},
                  readers={"reader": ["prior"]})
    journal = Journal("mixed-positive")
    for tag, number, digest in (("prior", 1, "a"), ("new", 2, "b")):
        journal.client("post", tag=tag, outcome="accepted")
        journal.client("verified", tag=tag, number=number, served_sha256=digest)
        journal.client("recovered", tag=tag, number=number, served_sha256=digest)
    journal.client("read", actor="reader", tag="prior", result="match")
    return journal, recipe


class MixedHistoryTests(unittest.TestCase):
    def test_complete_observed_promises_check(self):
        journal, recipe = observed()
        check_history(journal, recipe)

    def test_one_acknowledged_article_missing_after_restart_refutes(self):
        journal, recipe = observed()
        journal.records = [r for r in journal.records
                           if not (r.get("event") == "recovered" and r.get("tag") == "new")]
        with self.assertRaisesRegex(AssertionError, "recovered"):
            check_history(journal, recipe)

    def test_exact_served_hash_or_local_number_change_refutes(self):
        for field, value in (("served_sha256", "changed"), ("number", 7)):
            with self.subTest(field=field):
                journal, recipe = observed()
                next(r for r in journal.records if r.get("event") == "recovered")[field] = value
                with self.assertRaisesRegex(AssertionError, "recovered"):
                    check_history(journal, recipe)

    def test_consistently_reused_number_refutes(self):
        journal, recipe = observed()
        for row in journal.records:
            if row.get("tag") == "new" and "number" in row:
                row["number"] = 1
        with self.assertRaisesRegex(AssertionError, "reused"):
            check_history(journal, recipe)

    def test_missing_reader_completion_refutes(self):
        journal, recipe = observed()
        journal.records.pop()
        with self.assertRaisesRegex(AssertionError, "reader history"):
            check_history(journal, recipe)

    def test_lost_seal_never_becomes_shorter_valid_history(self):
        journal, _ = observed()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "journal.jsonl"
            journal.write(path)
            path.write_text("\n".join(path.read_text().splitlines()[:-1]) + "\n")
            with self.assertRaises(TruncatedHistory):
                Journal.read(path)

    def test_uncertain_441_remains_distinct_from_refusal_and_fault(self):
        self.assertEqual(wire_outcome(b"441 uncertain persistence\r\n"), "uncertain")
        self.assertEqual(wire_outcome(b"441 refused capacity\r\n"), "refused")
        self.assertEqual(wire_outcome(b"403 fault\r\n"), "fault")
        self.assertEqual(wire_outcome(b"240 accepted\r\n"), "accepted")


if __name__ == "__main__":
    unittest.main()

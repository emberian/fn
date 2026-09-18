"""Reject malformed host fields before constructing or submitting Lisp forms."""
import tempfile
import unittest
from pathlib import Path
from tools.workflow_bridge import records_form
from tools.workflow_journal import JournalError, WorkflowJournal


class RecordingReplay:
    def __init__(self):
        self.preflight_calls = []

    def __call__(self, records):
        return records

    def preflight(self, record):
        self.preflight_calls.append(record)
        return True


class WorkflowBoundaryTests(unittest.TestCase):
    def test_untrusted_enumeration_never_reaches_acl2_or_disk(self):
        record = {"work-id": "work:a", "attempt-id": "attempt:a",
                  "attempt-generation": 0,
                  "status": "expired) (value :unexpected) ("}
        with self.assertRaises(JournalError):
            records_form((("transport", record),))
        with tempfile.TemporaryDirectory(prefix="fn-workflow-boundary-") as tmp:
            replay = RecordingReplay()
            journal = WorkflowJournal(Path(tmp), replay)
            journal.open()
            try:
                with self.assertRaises(JournalError):
                    journal.publish("transport", record)
                self.assertEqual(replay.preflight_calls, [])
                self.assertEqual(list(journal.records.iterdir()), [])
                self.assertEqual(list(journal.staging.iterdir()), [])
            finally:
                journal.close()

    def test_only_validated_integer_and_enum_fields_enter_generated_forms(self):
        valid = {"txid": 1, "tx-generation": 0,
                 "phase": "ordinary", "result": "durable"}
        for changes in ({"txid": True}, {"txid": -1}, {"txid": 2**64},
                        {"phase": "ordinary) ("}, {"result": "committed"}):
            with self.subTest(changes=changes), self.assertRaises(JournalError):
                records_form((("outcome", {**valid, **changes}),))
        self.assertEqual(records_form((("outcome", valid),)),
                         "(list (list :outcome 1 0 :ordinary :durable))")

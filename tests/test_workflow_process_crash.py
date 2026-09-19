import multiprocessing
from pathlib import Path
import tempfile
import unittest

from tools.run_store import ScriptedFaults
from tools.workflow_journal import WorkflowJournal
from tests.test_workflow_journal import ATTEMPT


def crash_publish(root, point, code):
    # The process death lives in the test-only injector, not in the journal.
    journal=WorkflowJournal(Path(root), lambda records: records,
                            faults=ScriptedFaults(point, exit_code=code))
    journal.open()
    journal.publish("attempt", ATTEMPT)


class WorkflowProcessCrashTests(unittest.TestCase):
    def run_cut(self, point, code):
        with tempfile.TemporaryDirectory(prefix="fn-workflow-crash-") as temp:
            root=Path(temp)/"workflow"
            process=multiprocessing.Process(target=crash_publish, args=(root, point, code))
            process.start(); process.join(10)
            self.assertFalse(process.is_alive())
            records=[]
            reopened=WorkflowJournal(root, lambda replayed: records.extend(replayed) or replayed)
            reopened.open()
            reopened.close()
            return process.exitcode, records

    def test_death_before_publication_has_no_authoritative_record(self):
        code, records=self.run_cut("prepublish", 91)
        self.assertEqual(code, 91)
        self.assertEqual(records, [])

    def test_death_after_link_recovers_attempt_as_acl2_input(self):
        code, records=self.run_cut("postlink", 92)
        self.assertEqual(code, 92)
        self.assertEqual(records, [("attempt", ATTEMPT)])


if __name__ == "__main__": unittest.main()

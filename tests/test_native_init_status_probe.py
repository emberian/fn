"""The initializer-fidelity case asks the verb that opens the log (NATIVE-R2-INIT-FIDELITY-STATUS)."""
import unittest
from pathlib import Path


class StatusVerbTests(unittest.TestCase):
    def test_the_misaligned_case_runs_status_replay(self):
        source = Path(__file__).with_name("test_native_initializer_fidelity.py").read_text()
        self.assertTrue('("status", ("--replay",))' in source,
                        "a misaligned committed segment is refused by status --replay, not bare status")


if __name__ == "__main__":
    unittest.main()

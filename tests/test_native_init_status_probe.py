"""The initializer-fidelity case asks the verb that opens the log (NATIVE-R2-INIT-FIDELITY-STATUS)."""
import re
import unittest
from pathlib import Path


class StatusVerbTests(unittest.TestCase):
    def test_the_misaligned_case_runs_status_replay(self):
        source = Path(__file__).with_name("test_native_initializer_fidelity.py").read_text()
        case = re.search(
            r"def test_committed_segment_at_a_misaligned_length_is_refused_untouched\(self\):"
            r"(.*?)(?=\n    def )", source, re.S)
        self.assertIsNotNone(case, "the misaligned-segment case is missing")
        commands = re.findall(r'"(status[^"]*)"', case.group(1))
        self.assertIn("status --replay", commands,
                      "a misaligned committed segment is refused by status --replay")
        self.assertNotIn("status", commands,
                         "bare status reads the checkpoint header alone and opens no log")


if __name__ == "__main__":
    unittest.main()

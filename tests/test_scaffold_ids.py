"""The scaffold accepts allocator IDs beyond 999 without relaxing validation."""

import json
import re
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from tools import check_scaffold


class ScaffoldIDTests(unittest.TestCase):
    def check_registry(self, prefix, pattern, numbers):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "registry.json"
            ids = [f"{prefix}-{number}" for number in numbers]
            path.write_text(json.dumps({"schema_version": 1,
                                        "entries": [{"id": i} for i in ids]}))
            with mock.patch.object(check_scaffold, "ROOT", root), \
                    mock.patch.object(check_scaffold, "ERRORS", []):
                result = check_scaffold.registry("registry.json", "entries", pattern)
                return result, list(check_scaffold.ERRORS)

    def test_allocator_growth_across_999_is_accepted(self):
        for prefix, pattern in [("STO", check_scaffold.REQUIREMENT_ID),
                                ("PRF", check_scaffold.PROOF_ID),
                                ("SCN", check_scaffold.SCENARIO_ID)]:
            with self.subTest(prefix=prefix):
                result, errors = self.check_registry(prefix, pattern,
                                                     ["001", "999", "1000", "10000"])
                self.assertEqual(errors, [])
                self.assertEqual(len(result), 4)

    def test_malformed_and_duplicate_ids_still_fail(self):
        _, errors = self.check_registry("PRF", check_scaffold.PROOF_ID,
                                        ["99", "1000", "1000", "1000x"])
        self.assertEqual(len(errors), 3)
        self.assertTrue(all("invalid or duplicate ID" in e for e in errors))
        self.assertIsNone(re.fullmatch(check_scaffold.PROOF_ID, "SCN-1000"))

    def test_authoritative_requirement_heading_uses_complete_grown_id(self):
        text = "STO-999: old\nSTO-1000: next\nSTO-10000: later\nSTO-99: invalid\n"
        found = re.findall(rf"(?m)^({check_scaffold.REQUIREMENT_ID}):", text)
        self.assertEqual(found, ["STO-999", "STO-1000", "STO-10000"])


if __name__ == "__main__":
    unittest.main()

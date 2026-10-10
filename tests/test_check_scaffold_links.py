"""tools/check_scaffold.py link(): a missing target is an error unless
planning/retired-paths.json discloses it (removed on purpose, and where its
role went), the same central disclosure tools/cite_check.py reads."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import check_scaffold  # noqa: E402


class RetiredLinkTests(unittest.TestCase):
    def errors_for(self, target: str) -> list[str]:
        del check_scaffold.ERRORS[:]
        check_scaffold.link(target, ROOT / "planning" / "zz-citer.md", "planning/zz-citer.md")
        found = list(check_scaffold.ERRORS)
        del check_scaffold.ERRORS[:]
        return found

    def test_a_retired_target_is_disclosed(self):
        retired = sorted(check_scaffold.retired_paths())
        self.assertIn("planning/how-we-work.md", retired)
        self.assertEqual(self.errors_for("how-we-work.md"), [])

    def test_an_absent_target_nothing_discloses_is_an_error(self):
        found = self.errors_for("zz-never-written.md")
        self.assertEqual(len(found), 1, found)
        self.assertIn("missing target", found[0])


if __name__ == "__main__":
    unittest.main()

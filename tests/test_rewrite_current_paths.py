"""Current allocation callback documentation follows its surviving declaration."""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


class CurrentPaths(unittest.TestCase):
    def test_evidence_instructions_do_not_force_add_ignored_bytes(self):
        for rel in ('.gitignore', 'tests/README.md'):
            with self.subTest(path=rel):
                self.assertNotIn('git add -f', (ROOT / rel).read_text())

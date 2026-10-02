"""Current allocation callback documentation follows its surviving declaration."""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


class CurrentPaths(unittest.TestCase):
    def test_allocation_finish_points_at_current_declaration(self):
        spec = (ROOT / 'specs/allocation-turns.md').read_text()
        self.assertNotIn('`host/allocation-turn-host.lisp`', spec)
        self.assertIn('`host/interfaces.lisp`', spec)
        self.assertIn('(definterface fn-ats-finish-owned',
                      (ROOT / 'host/interfaces.lisp').read_text())

    def test_evidence_instructions_do_not_force_add_ignored_bytes(self):
        for rel in ('.gitignore', 'tests/README.md', 'tools/evidence_manifests.py'):
            with self.subTest(path=rel):
                self.assertNotIn('git add -f', (ROOT / rel).read_text())

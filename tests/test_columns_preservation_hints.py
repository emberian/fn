"""Exercise actual carrier-preservation macro expansion without ACL2."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
class ColumnsPreservationHints(unittest.TestCase):
    def test_actual_generator_fallback_and_explicit_overrides(self):
        result = subprocess.run(
            ['sbcl', '--noinform', '--script', 'tests/columns-preservation-hints-controls.lsp'],
            cwd=ROOT, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('COLUMNS PRESERVATION HINT CONTROLS PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()

"""Exercise actual defcolumns generator source without ACL2/build processes."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
class ColumnsNames(unittest.TestCase):
    def test_emitted_namespace_and_unchanged_valid_output(self):
        result = subprocess.run(
            ['sbcl', '--noinform', '--script', 'tests/columns-name-controls.lsp'],
            cwd=ROOT, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('COLUMNS NAME CONTROLS PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()

"""Compare actual generated factories; no ACL2 or remote work."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '7e0de36f5dceaec83358702ec5dc88261dbf6043'


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
class NumericTheory(unittest.TestCase):
    def test_factory_semantics_and_raw_fallback(self):
        source = subprocess.run(
            ['git', 'show', f'{BASELINE}:books/columns.lisp'], cwd=ROOT,
            check=True, stdout=subprocess.PIPE).stdout
        with tempfile.TemporaryDirectory(prefix='fn-column-numeric-') as tmp:
            path = Path(tmp) / 'before.lisp'
            path.write_bytes(source)
            result = subprocess.run(
                ['sbcl', '--noinform', '--script', 'tests/columns-numeric-theory-controls.lsp'],
                cwd=ROOT, env={**os.environ, 'FN_COLUMNS_BASELINE': str(path)},
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('COLUMNS NUMERIC THEORY CONTROLS PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()

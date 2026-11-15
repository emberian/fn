"""Run shared carrier-generator routing controls without ACL2 or remote work."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
# Last integration before opt-in :type-hints: compare actual source, not a twin.
BASELINE = 'd1e1669996337419b8a8f0e87752a758bad7d12d'


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
class CarrierHints(unittest.TestCase):
    def test_type_wfp_routing_and_formula_identity(self):
        original = subprocess.run(
            ['git', 'show', f'{BASELINE}:books/columns.lisp'], cwd=ROOT,
            check=True, stdout=subprocess.PIPE).stdout
        with tempfile.TemporaryDirectory(prefix='fn-carrier-hints-') as tmp:
            source = Path(tmp) / 'columns-before.lisp'
            source.write_bytes(original)
            result = subprocess.run(
                ['sbcl', '--noinform', '--script', 'tests/columns-carrier-hints-controls.lsp'],
                cwd=ROOT, env={**os.environ, 'FN_COLUMNS_BASELINE': str(source)},
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('COLUMNS CARRIER HINT CONTROLS PASS', result.stdout)


    def test_prior_generator_rejects_absent_wfp_fallback(self):
        original = subprocess.run(
            ['git', 'show', '4f7f05f8fa0ec5f9d7eb8e2594de25f30be355c5:books/columns.lisp'],
            cwd=ROOT, check=True, stdout=subprocess.PIPE).stdout
        baseline = subprocess.run(
            ['git', 'show', f'{BASELINE}:books/columns.lisp'], cwd=ROOT,
            check=True, stdout=subprocess.PIPE).stdout
        with tempfile.TemporaryDirectory(prefix='fn-carrier-absence-') as tmp:
            root = Path(tmp)
            (root / 'books').mkdir()
            (root / 'books/columns.lisp').write_bytes(original)
            before = root / 'baseline.lisp'
            before.write_bytes(baseline)
            result = subprocess.run(
                ['sbcl', '--noinform', '--script', str(ROOT / 'tests/columns-carrier-hints-controls.lsp')],
                cwd=root, env={**os.environ, 'FN_COLUMNS_BASELINE': str(before)},
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('The assertion', result.stdout)
        self.assertNotIn('COLUMNS CARRIER HINT CONTROLS PASS', result.stdout)

    def test_old_generator_rejects_opt_in_control(self):
        original = subprocess.run(
            ['git', 'show', f'{BASELINE}:books/columns.lisp'], cwd=ROOT,
            check=True, stdout=subprocess.PIPE).stdout
        with tempfile.TemporaryDirectory(prefix='fn-carrier-old-control-') as tmp:
            root = Path(tmp)
            (root / 'books').mkdir()
            source = root / 'books/columns.lisp'
            source.write_bytes(original)
            result = subprocess.run(
                ['sbcl', '--noinform', '--script', str(ROOT / 'tests/columns-carrier-hints-controls.lsp')],
                cwd=root, env={**os.environ, 'FN_COLUMNS_BASELINE': str(source)},
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('The assertion', result.stdout)
        self.assertNotIn('COLUMNS CARRIER HINT CONTROLS PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()

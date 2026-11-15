"""Compare actual owning macro output, including explicit hint override semantics."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '4fe56ec3eb575f5c67740e1d56632a00dd471844'


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
class RangeShapeHints(unittest.TestCase):
    def run_control(self, original=False):
        baseline = subprocess.check_output(
            ['git', 'show', f'{BASELINE}:books/range.lisp'], cwd=ROOT)
        with tempfile.TemporaryDirectory(prefix='fn-run-hot-guards-') as tmp:
            path = Path(tmp) / 'baseline.lisp'
            path.write_bytes(baseline)
            env = {**os.environ, 'FN_RA_BASELINE': str(path)}
            if original:
                env['FN_RA_CANDIDATE'] = str(path)
            return subprocess.run(
                ['sbcl', '--noinform', '--script', 'tests/range-shape-hints-controls.lsp'],
                cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=20)

    def test_actual_runtime_guards_formulas_and_legacy_identity(self):
        result = self.run_control()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('RANGE SHAPE CONTROLS PASS', result.stdout)

    def test_original_hot_hints_refused(self):
        result = self.run_control(original=True)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertNotIn('RANGE SHAPE CONTROLS PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()

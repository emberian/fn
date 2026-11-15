"""Compare actual owning macro output, including explicit hint override semantics."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BASELINE = 'db0b44e5ed996e8b42678c29fddd4eab9699d0e3'


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
class RunHotGuardHints(unittest.TestCase):
    def run_control(self, original=False):
        baseline = subprocess.check_output(
            ['git', 'show', f'{BASELINE}:books/runs-assemble.lisp'], cwd=ROOT)
        with tempfile.TemporaryDirectory(prefix='fn-run-hot-guards-') as tmp:
            path = Path(tmp) / 'baseline.lisp'
            path.write_bytes(baseline)
            env = {**os.environ, 'FN_RA_BASELINE': str(path)}
            if original:
                env['FN_RA_CANDIDATE'] = str(path)
            return subprocess.run(
                ['sbcl', '--noinform', '--script', 'tests/run-hot-guards-controls.lsp'],
                cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=20)

    def test_actual_runtime_guards_formulas_and_legacy_identity(self):
        result = self.run_control()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('RUN HOT GUARD CONTROLS PASS', result.stdout)

    def test_original_hot_hints_refused(self):
        result = self.run_control(original=True)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertNotIn('RUN HOT GUARD CONTROLS PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()

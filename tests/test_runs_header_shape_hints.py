"""Check actual generated runtime/guards/formulas, and reject the old proof hint."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '8aa65a677497f07ebdbd4c20a10ae57562b64ccc'


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
class RunsHeaderHints(unittest.TestCase):
    def run_control(self, old_candidate=False):
        original = subprocess.check_output(
            ['git', 'show', f'{BASELINE}:books/runs-assemble.lisp'], cwd=ROOT)
        with tempfile.TemporaryDirectory(prefix='fn-run-header-hints-') as tmp:
            baseline = Path(tmp) / 'baseline.lisp'
            baseline.write_bytes(original)
            env = {**os.environ, 'FN_RA_BASELINE': str(baseline)}
            if old_candidate:
                env['FN_RA_CANDIDATE'] = str(baseline)
            return subprocess.run(
                ['sbcl', '--noinform', '--script', 'tests/runs-header-shape-controls.lsp'],
                cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=20)

    def test_generated_runtime_guards_and_theorems_unchanged(self):
        result = self.run_control()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('RUN HEADER SHAPE CONTROLS PASS', result.stdout)

    def test_unchanged_proof_hint_rejected(self):
        result = self.run_control(old_candidate=True)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertNotIn('RUN HEADER SHAPE CONTROLS PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()

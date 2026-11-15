"""Actual preservation factory and original runtime/hypothesis identity controls."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
BASELINE = '0b84789e4f10349150c002e302bfc476db6b2817'

@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
class QueryMaskForward(unittest.TestCase):
    def control(self, mutation=''):
        baseline = subprocess.check_output(['git', 'show', f'{BASELINE}:books/machines-c-bind.lisp'], cwd=ROOT)
        with tempfile.TemporaryDirectory(prefix='fn-query-mask-') as temp:
            path = Path(temp) / 'baseline.lisp'
            path.write_bytes(baseline)
            return subprocess.run(['sbcl', '--noinform', '--script', 'tests/query-mask-forward-controls.lsp'],
                cwd=ROOT, env={**os.environ, 'FN_BIND_BASELINE': str(path), 'FN_BIND_MUTATION': mutation},
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)

    def test_actual_factory_and_original_source_identity(self):
        result = self.control()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('QUERY MASK FORWARD CONTROLS PASS', result.stdout)

    def test_runtime_mutation_refused(self):
        self.assertNotEqual(self.control('runtime').returncode, 0)

    def test_checked_hypothesis_removal_refused(self):
        self.assertNotEqual(self.control('hyps').returncode, 0)

    def test_wake_guard_width_mutation_refused(self):
        self.assertNotEqual(self.control('wake-width').returncode, 0)

    def test_missing_forward_interface_refused(self):
        self.assertNotEqual(self.control('forward').returncode, 0)

if __name__ == '__main__':
    unittest.main()

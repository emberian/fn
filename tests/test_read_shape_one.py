"""Actual RD/shared-constructor public statement and legacy expansion controls."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
BASELINE = '7115c5f30'
@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
class ReadShapeOne(unittest.TestCase):
    def control(self, mutation=''):
        with tempfile.TemporaryDirectory(prefix='fn-read-shape-') as temp:
            path = Path(temp) / 'baseline.lisp'
            path.write_bytes(subprocess.check_output(['git', 'show', f'{BASELINE}:books/machines-c-read.lisp'], cwd=ROOT))
            return subprocess.run(['sbcl', '--noinform', '--script', 'tests/read_shape_one_controls.lsp'], cwd=ROOT,
                env={**os.environ, 'FN_RD_BASELINE': str(path), 'FN_RD_MUTATION': mutation},
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=20)
    def test_public_statement_rule_classes_legacy_and_source_identity(self):
        r = self.control(); self.assertEqual(r.returncode, 0, r.stdout)
        self.assertIn('READ SHAPE ONE CONTROLS PASS', r.stdout)
    def test_runtime_mutation_refused(self):
        self.assertNotEqual(self.control('runtime').returncode, 0)
    def test_hypothesis_removal_refused(self):
        self.assertNotEqual(self.control('hyps').returncode, 0)
    def test_rule_class_mutation_refused(self):
        self.assertNotEqual(self.control('rules').returncode, 0)
if __name__ == '__main__': unittest.main()

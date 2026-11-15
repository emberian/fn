"""Execute production lowering; old accounting must fail the same controls."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]

@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
class Accounting(unittest.TestCase):
    def run_control(self, cwd):
        return subprocess.run(['sbcl', '--noinform', '--script',
            str(ROOT / 'tests/arm-accounting-controls.lsp')], cwd=cwd,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)

    def test_composed_generated_reports(self):
        result = self.run_control(ROOT)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('ARM ACCOUNTING COMPOSED CONTROLS PASS', result.stdout)

    def test_removed_call_floor_is_detected(self):
        # Remove only the actual runtime floor, preserving metadata and all
        # new helper definitions. This is an executable undercharge mutant.
        source = (ROOT / 'books/machine-arms.lisp').read_text()
        old = '(fn2-arms-account-floor (car xs) cb)'
        self.assertEqual(source.count(old), 1)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'books'
            path.mkdir()
            (path / 'machine-arms.lisp').write_text(source.replace(old, '(car xs)'))
            result = self.run_control(directory)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('4096', result.stdout)

    def test_removed_goto_prefix_is_detected(self):
        source = (ROOT / 'books/machine-arms.lisp').read_text()
        old = 'prefix-bytes prefix-steps env))'
        self.assertEqual(source.count(old), 1)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'books'
            path.mkdir()
            (path / 'machine-arms.lisp').write_text(source.replace(old, '0 0 env))'))
            result = self.run_control(directory)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('12288', result.stdout)

if __name__ == '__main__':
    unittest.main()

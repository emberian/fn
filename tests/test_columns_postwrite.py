"""Narrow shared-hint controls; no ACL2 qualification is inferred."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]

@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
class Postwrite(unittest.TestCase):
    def run_control(self, root):
        return subprocess.run(['sbcl', '--noinform', '--script',
            str(ROOT / 'tests/columns-postwrite-controls.lsp')], cwd=root,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)

    def test_selector_and_integrated_hint(self):
        result = self.run_control(ROOT)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('COLUMNS POSTWRITE SOURCE CONTROLS PASS', result.stdout)

    def mutant(self, old, new):
        source = (ROOT / 'books/columns-call-guards.lisp').read_text()
        self.assertEqual(source.count(old), 1)
        with tempfile.TemporaryDirectory() as directory:
            books = Path(directory) / 'books'
            books.mkdir()
            shutil.copyfile(ROOT / 'books/columns-guard-hints.lisp', books / 'columns-guard-hints.lisp')
            (books / 'columns-call-guards.lisp').write_text(source.replace(old, new))
            result = self.run_control(directory)
            self.assertNotEqual(result.returncode, 0, 'mutation escaped the controls')
            self.assertIn('assertion', result.stdout.lower())

    def test_removing_automatic_hint_connection_fails(self):
        self.mutant('(set-difference-eq (fn2-columns-postwrite-readers name tables world) opaque)', 'nil')

    def test_wrong_table_provenance_is_rejected(self):
        self.mutant('(member-eq (caddr reader) (cadr arguments))', '(cadr arguments)')

if __name__ == '__main__':
    unittest.main()

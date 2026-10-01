"""Actual core diagnostic renderer, ordinary Lisp execution; no authority claim."""
import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import json
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('proof_repl', ROOT/'tools/proof_repl.py')
pr = importlib.util.module_from_spec(spec); spec.loader.exec_module(pr)
def selected(path, names):
    return '\n'.join(f for f in pr.forms(path.read_text())
                     if any((f.lower().startswith('(defun '+n+' ') or f.lower().startswith('(defun '+n+'\n')) for n in names))
class DiagnosticsBoundary(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_scalar_renderer(self):
        self.run_fixture()

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_budget_and_secret_mutations(self):
        for old,new in [('(fn-od-nat-fits-p value budget)','t'),
                        ("(otherwise '(111 116 104 101 114))","(otherwise '(99 114 101 100 101 110 116 105 97 108 45 115 101 99 114 101 116))")]:
            with self.subTest(mutation=old): self.run_fixture((old,new))

    def run_fixture(self, mutation=None):
        source = selected(ROOT/'books/operation-diagnostics.lisp', ['fn-od-word','fn-od-nat-fits-p','fn-od-digits','fn-od-nat','fn-od-value','fn-od-fields','fn-od-report','fn-od-correlated-report'])
        if mutation:
            old,new=mutation; self.assertEqual(source.count(old),1); source=source.replace(old,new,1)
        # Literal ACL2 MBE executes its original :EXEC branch.
        source='(defmacro mbe (&key logic exec) (declare (ignore logic)) exec)\n'+source
        with tempfile.TemporaryDirectory() as d:
            d=Path(d); (d/'source.lisp').write_text(source)
            fixture=(ROOT/'tests/fixtures/operation_diagnostics_boundary.lisp').read_text()
            (d/'driver.lisp').write_text(fixture.replace('__SOURCE_FILE__', str(d/'source.lisp')))
            run=subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'driver.lisp')],capture_output=True,text=True,timeout=30)
        if mutation:
            self.assertNotEqual(run.returncode,0); self.assertIn('assertion',run.stderr.lower())
        else:
            self.assertEqual(run.returncode,0,run.stdout+run.stderr)
            self.assertIn('PASS operation diagnostics',run.stdout)
if __name__=='__main__': unittest.main()

"""Literal actual composed inspect source; modeled qualified factory recording."""
from tests.test_operation_diagnostics_boundary import pr, ROOT
import shutil, subprocess, tempfile, unittest
from pathlib import Path
class InspectOrdering(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_order_and_refusers(self):
        self.run_fixture()
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_lexical_cache_substitution_refuted(self):
        self.run_fixture(('request cached fn-page-read-pool state)', 'cached request fn-page-read-pool state)'))
    def run_fixture(self, mutation=None):
        source='\n'.join(f for f in pr.forms((ROOT/'books/owner-inspect-operation.lisp').read_text()) if f.lower().startswith('(defun '))
        if mutation:
            old,new=mutation; self.assertEqual(source.count(old),1);source=source.replace(old,new)
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);(d/'source.lisp').write_text(source)
            fixture=(ROOT/'tests/fixtures/owner_inspect_operation_boundary.lisp').read_text()
            (d/'driver.lisp').write_text(fixture.replace('__SOURCE_FILE__',str(d/'source.lisp')))
            run=subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'driver.lisp')],capture_output=True,text=True,timeout=30)
        if mutation:
            self.assertNotEqual(run.returncode,0);self.assertIn('assertion',run.stderr.lower())
        else:
            self.assertEqual(run.returncode,0,run.stdout+run.stderr);self.assertIn('PASS actual inspect ordering',run.stdout)

"""Actual sticky STATE custody; genuine runtime issuer deliberately modeled."""
from tests.test_operation_diagnostics_boundary import pr, ROOT
from pathlib import Path
import shutil, subprocess, tempfile, unittest
class ReportCapture(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_sticky_source_and_retained_roots(self): self.run_fixture()
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_nested_writer_and_sticky_mutations(self):
        self.run_fixture(('((zp next) :stable)\n            (t :mutating)', '((zp next) :stable)\n            (t :stable)'))
        self.run_fixture(('(update-nth 7 :invalid job)', '(update-nth 7 :valid job)'))
    def run_fixture(self, mutation=None):
        source='\n'.join(f for f in pr.forms((ROOT/'books/owner-report-capture.lisp').read_text()) if f.lower().startswith('(defun '))
        if mutation:
            old,new=mutation;self.assertGreater(source.count(old),0);source=source.replace(old,new)
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);(d/'source.lisp').write_text(source)
            (d/'driver.lisp').write_text((ROOT/'tests/fixtures/owner_report_capture_boundary.lisp').read_text().replace('__SOURCE_FILE__',str(d/'source.lisp')))
            r=subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'driver.lisp')],capture_output=True,text=True,timeout=30)
        if mutation: self.assertNotEqual(r.returncode,0);self.assertIn('assertion',r.stderr.lower())
        else: self.assertEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('PASS sticky report custody',r.stdout)

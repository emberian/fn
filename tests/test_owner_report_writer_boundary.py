"""Actual selected owner writers invalidate before Cat writes; no native claim."""
from tests.test_operation_diagnostics_boundary import pr, ROOT
from pathlib import Path
import shutil, subprocess, tempfile, unittest
class ReportWriter(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_writers_and_escape(self): self.run_fixture()
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_missing_entry_and_fault_reset_refuted(self):
        self.run_fixture(('(fn-orc-writer-enter state)', 'state'))
        self.run_fixture(('(fn-orc-writer-fault state)', '(fn-orc-writer-leave state)'))
    def run_fixture(self, mutation=None):
        source='\n'.join(f for f in pr.forms((ROOT/'books/owner-report-capture.lisp').read_text()) if f.lower().startswith('(defun '))
        source+='\n'+(ROOT/'planning/evidence/operation-diagnostics-2026-10-01/writer-hooks/source.lisp').read_text()
        if mutation:
            old,new=mutation; self.assertGreater(source.count(old),0); source=source.replace(old,new)
        with tempfile.TemporaryDirectory() as d:
            d=Path(d); (d/'source.lisp').write_text(source)
            (d/'driver.lisp').write_text((ROOT/'tests/fixtures/owner_report_writer_boundary.lisp').read_text().replace('__SOURCE_FILE__',str(d/'source.lisp')))
            r=subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'driver.lisp')],capture_output=True,text=True,timeout=30)
        if mutation: self.assertNotEqual(r.returncode,0); self.assertIn('assertion',r.stderr.lower())
        else: self.assertEqual(r.returncode,0,r.stdout+r.stderr); self.assertIn('PASS actual report writer ordering',r.stdout)

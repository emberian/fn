"""Real PRS issue/actual reservation order, modeled installed recipe only."""
from tests.test_operation_diagnostics_boundary import pr, ROOT
from pathlib import Path
import shutil, subprocess, tempfile, unittest
class ReportReservation(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_real_prs_and_debit_escape_custody(self): self.run_fixture()
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_predebit_intent_removal_refuted(self):
        self.run_fixture(('(list :owner-report-reserving nil kind request cached\n                                   capture cursor :reserving (fn-prl-nth 2 ledger)\n                                   demand)', 'nil'))
    def run_fixture(self, mutation=None):
        names=('page-read-resources','owner-report-capture','owner-report-reservation')
        source='\n'.join(f for name in names for f in pr.forms((ROOT/f'books/{name}.lisp').read_text()) if f.lower().startswith('(defun '))
        if mutation:
            old,new=mutation;self.assertEqual(source.count(old),1);source=source.replace(old,new)
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);(d/'source.lisp').write_text(source)
            (d/'driver.lisp').write_text((ROOT/'tests/fixtures/owner_report_reservation_boundary.lisp').read_text().replace('__SOURCE_FILE__',str(d/'source.lisp')))
            r=subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'driver.lisp')],capture_output=True,text=True,timeout=30)
        if mutation: self.assertNotEqual(r.returncode,0);self.assertIn('assertion',r.stderr.lower())
        else: self.assertEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('PASS actual report PRS reserve',r.stdout)

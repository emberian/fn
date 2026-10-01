"""Actual transport functions with modeled receipt/gate; no native install."""
from tests.test_operation_diagnostics_boundary import pr, ROOT
from pathlib import Path
import shutil,subprocess,tempfile,unittest
class InspectTransport(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_transport(self): self.run_fixture()
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_premature_cache_publication_refuted(self):
        self.run_fixture(('(unless (eq word :yield)', '(unless nil)'))
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_missing_state_retention_refuted(self):
        self.run_fixture(owner_mutation=True)
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_resume_cache_substitution_refuted(self):
        self.run_fixture(('(unless cache-captured', '(when t'))
    def run_fixture(self, mutation=None, owner_mutation=False):
        forms=pr.forms((ROOT/'host/native/control.lisp').read_text())
        source='\n'.join(f for f in forms if f.startswith('(defun fnn-control-publish-inspect-answer ') or f.startswith('(defun fnn-control-live-status-answer '))
        if mutation:
            old,new=mutation;self.assertEqual(source.count(old),1);source=source.replace(old,new,1)
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);(d/'source.lisp').write_text(source)
            owner=ROOT/'planning/evidence/operation-diagnostics-2026-10-01/native-source/serialized.lisp'
            if owner_mutation:
                body=owner.read_text();old='(when next-state (setf *the-live-state* next-state))';self.assertEqual(body.count(old),2);body=body.replace(old,'(when next-state nil)',1);(d/'owner-mutant.lisp').write_text(body);owner=d/'owner-mutant.lisp'
            fixture=(ROOT/'tests/fixtures/inspect_transport_boundary.lisp').read_text().replace('__OWNER_SOURCE__',str(owner)).replace('__CONTROL_SOURCE__',str(d/'source.lisp'))
            (d/'driver.lisp').write_text(fixture)
            run=subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'driver.lisp')],capture_output=True,text=True,timeout=30)
        if mutation or owner_mutation:
            self.assertNotEqual(run.returncode,0)
        else:
            self.assertEqual(run.returncode,0,run.stdout+run.stderr);self.assertIn('PASS actual inspect transport',run.stdout)

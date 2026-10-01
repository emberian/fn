"""Actual recovery reload fence, explicit modeled accessor outputs."""
from tests.test_operation_diagnostics_boundary import pr, ROOT
from pathlib import Path
import re, shutil, subprocess, tempfile, unittest
class RecoveryWriter(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_reload_and_escape(self): self.run_fixture()
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_missing_fence_refuted(self): self.run_fixture(('(fn-orc-writer-enter state)', 'state'))
    def run_fixture(self, mutation=None):
        recovery=(ROOT/'planning/evidence/operation-diagnostics-2026-10-01/recovery-hook/source.lisp').read_text()
        # Only accessors/retained reset helpers are modeled; catalog/hist writer
        # probes, STATE storage and report fence bodies are exercised literally.
        names=set(re.findall(r'\((fn-[a-z0-9-]+)',recovery))
        names-={'fn-owner-install-extended','fn-orc-writer-enter','fn-orc-writer-leave','fn-sca-load-held-rows-keyed','fn-hist-load','fn-onb-open-okp'}
        models='\n'.join('(defun '+n+' (&rest args) (car (last args)))' for n in sorted(names))
        source='\n'.join(f for f in pr.forms((ROOT/'books/owner-report-capture.lisp').read_text()) if f.lower().startswith('(defun '))+'\n'+recovery
        if mutation:
            old,new=mutation;self.assertGreater(source.count(old),0);source=source.replace(old,new)
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);(d/'source.lisp').write_text(source)
            fixture=(ROOT/'tests/fixtures/owner_report_recovery_boundary.lisp').read_text().replace('__MODELED_ACCESSORS__',models).replace('__SOURCE_FILE__',str(d/'source.lisp'))
            (d/'driver.lisp').write_text(fixture)
            r=subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'driver.lisp')],capture_output=True,text=True,timeout=30)
        if mutation:self.assertNotEqual(r.returncode,0);self.assertIn('assertion',r.stderr.lower())
        else:self.assertEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('PASS actual recovery report ordering',r.stdout)

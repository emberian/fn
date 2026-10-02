"""Actual recovery reload fence, explicit modeled accessor outputs."""
from tests.test_operation_diagnostics_boundary import pr, ROOT
from pathlib import Path
import re, shutil, subprocess, tempfile, unittest
class ArenaSeedWriter(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_reload_and_escape(self): self.run_fixture()
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_missing_fence_refuted(self): self.run_fixture(('(fn-orc-writer-enter state)', 'state'))
    def run_fixture(self, mutation=None):
        recovery=(ROOT/'tests/fixtures/evidence/operation-diagnostics-2026-10-01/arena-seed-hook/source.lisp').read_text()
        # Only accessors/retained reset helpers are modeled; catalog/hist writer
        # probes, STATE storage and report fence bodies are exercised literally.
        source='\n'.join(f for f in pr.forms((ROOT/'books/owner-report-capture.lisp').read_text()) if f.lower().startswith('(defun '))+'\n'+recovery
        if mutation:
            old,new=mutation;self.assertGreater(source.count(old),0);source=source.replace(old,new)
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);(d/'source.lisp').write_text(source)
            fixture=(ROOT/'tests/fixtures/owner_report_arena_seed_boundary.lisp').read_text().replace('__SOURCE_FILE__',str(d/'source.lisp'))
            (d/'driver.lisp').write_text(fixture)
            r=subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'driver.lisp')],capture_output=True,text=True,timeout=30)
        if mutation:self.assertNotEqual(r.returncode,0);self.assertIn('assertion',r.stderr.lower())
        else:self.assertEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('PASS actual arena seed report ordering',r.stdout)

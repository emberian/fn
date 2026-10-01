"""Actual native :swap block only; report core wrappers literal, I/O modeled."""
from tests.test_operation_diagnostics_boundary import pr, ROOT
from pathlib import Path
import shutil, subprocess, tempfile, unittest
class SwapWriter(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_swap_and_each_write_escape(self):self.run_fixture()
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_missing_fence_and_error_stability_refuted(self):
        self.run_fixture(("(fnn-owner-core 'fn-owner-report-writer-enter)", 'nil'))
        self.run_fixture(("(fnn-owner-core 'fn-owner-report-writer-fault)", "(fnn-owner-core 'fn-owner-report-writer-leave)"))
    def run_fixture(self, mutation=None):
        source='\n'.join(f for path in ['books/owner-report-capture.lisp','books/owner-report-writer-entry.lisp'] for f in pr.forms((ROOT/path).read_text()) if f.lower().startswith('(defun '))
        swap=(ROOT/'planning/evidence/operation-diagnostics-2026-10-01/native-swap-hook/source.lisp').read_text()
        if mutation:
            old,new=mutation;self.assertEqual(swap.count(old),1);swap=swap.replace(old,new)
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);(d/'source.lisp').write_text(source)
            fixture=(ROOT/'tests/fixtures/owner_report_swap_boundary.lisp').read_text().replace('__SOURCE_FILE__',str(d/'source.lisp')).replace('__SWAP_BODY__',swap)
            (d/'driver.lisp').write_text(fixture)
            r=subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'driver.lisp')],capture_output=True,text=True,timeout=30)
        if mutation:self.assertNotEqual(r.returncode,0);self.assertIn('assertion',r.stderr.lower())
        else:self.assertEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('PASS actual swap report ordering',r.stdout)

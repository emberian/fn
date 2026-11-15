"""Release proof-only hint preserves all source/runtime/guard claims."""
from pathlib import Path
import subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_source as ls
BASE='3da51b9ebc0c9f797950e46fcc4558f43d05bcce'
def check(before,after):
    added='(include-book "columns-call-guards")\n'
    assert after.count(added)==1
    old=ls.forms(before)
    new=ls.forms(after.replace(added,'',1))
    assert len(new)==len(old)
    assert new[:-1]==old[:-1]
    assert new[-1].rsplit('\n :hints ',1)[0]+')'==old[-1]
    ls.read_sexp(new[-1])

class RetentionCallHints(unittest.TestCase):
    def setUp(self):
        self.before=subprocess.check_output(['git','show',BASE+':books/cns-source-retention.lisp'],cwd=ROOT,text=True)
        self.after=(ROOT/'books/cns-source-retention.lisp').read_text()
    def test_actual_source_arguments_runtime_and_guards_exact(self):check(self.before,self.after)
    def test_runtime_or_hypothesis_change_rejected(self):
        with self.assertRaises(AssertionError):check(self.before,self.after.replace('(release-row (+ 1 e))','(release-row (+ 2 e))'))
        with self.assertRaises(AssertionError):check(self.before,self.after.replace(':position 1 :carriers',':position 2 :carriers',1))
if __name__=='__main__':unittest.main()

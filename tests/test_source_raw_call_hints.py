"""The raw caller guard repair changes only its proof hint."""
from pathlib import Path
import subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_rewrite import parse,Lst,Pre,Atom
BASE='6fcbd6dbc0bf0e12d1cc7c935c703ad389959e54'
def canon(n):
    if isinstance(n,Lst):return [canon(x) for x in n.items]
    if isinstance(n,Pre):return (n.prefix,canon(n.node))
    return n.text if n.kind=='string' else n.low

def check(before,after):
    old,new=parse(before).forms,parse(after).forms
    helper=[i for i,n in enumerate(new) if canon(n)==['include-book','"columns-call-guards"']]
    assert len(helper)==1
    new.pop(helper[0])
    fn=[n for n in new if isinstance(n,Lst) and canon(n)[:2]==['defun','fn2-cns-source-issue-children']]
    assert len(fn)==1
    xargs=fn[0].items[3].items[1].items
    assert xargs[-2].low==':guard-hints'
    xargs[-2:]=[]
    assert [canon(n) for n in old]==[canon(n) for n in new]
class SourceRawCallHints(unittest.TestCase):
    def setUp(self):
        self.before=subprocess.check_output(['git','show',BASE+':books/cns-source-raw.lisp'],cwd=ROOT,text=True)
        self.after=(ROOT/'books/cns-source-raw.lisp').read_text()
    def test_all_runtime_guards_and_public_claims_exact(self):check(self.before,self.after)
    def test_guard_and_return_mutation_rejected(self):
        with self.assertRaises(AssertionError):check(self.before,self.after.replace('(fn2-cns-sources-wfp fn2-cns-sources)','t',1))
        with self.assertRaises(AssertionError):check(self.before,self.after.replace('(mv :bad 0 0','(mv :bounds 0 0',1))
if __name__=='__main__':unittest.main()

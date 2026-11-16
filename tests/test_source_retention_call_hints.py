"""Release proof-only hint preserves all source/runtime/guard claims."""
from pathlib import Path
import subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_rewrite import parse, Lst, Pre, Atom
BASE='3da51b9ebc0c9f797950e46fcc4558f43d05bcce'
def canonical(node):
    if isinstance(node,Lst):return [canonical(x) for x in node.items]
    if isinstance(node,Pre):return (node.prefix,canonical(node.node))
    return node.text if node.kind=='string' else node.low

def check(before,after):
    old=parse(before).forms
    new=parse(after).forms
    helper=[i for i,n in enumerate(new) if canonical(n)==['include-book','"columns-call-guards"']]
    assert len(helper)==1
    new.pop(helper[0])
    macro=new[-1].items
    assert macro[-2].low==':hints'
    macro[-2:]=[]
    i=next(i for i,n in enumerate(macro) if isinstance(n,Atom) and n.low==':carriers')
    for carrier in macro[i+1].items:
        assert carrier.items[-2].low==':hints'
        carrier.items[-2:]=[]
    assert [canonical(n) for n in old]==[canonical(n) for n in new]

class RetentionCallHints(unittest.TestCase):
    def setUp(self):
        self.before=subprocess.check_output(['git','show',BASE+':books/cns-source-retention.lisp'],cwd=ROOT,text=True)
        self.after=(ROOT/'books/cns-source-retention.lisp').read_text()
    def test_actual_source_arguments_runtime_and_guards_exact(self):check(self.before,self.after)
    def test_runtime_or_hypothesis_change_rejected(self):
        with self.assertRaises(AssertionError):check(self.before,self.after.replace('(release-row (+ 1 e))','(release-row (+ 2 e))'))
        with self.assertRaises(AssertionError):check(self.before,self.after.replace(':position 1 :carriers',':position 2 :carriers',1))
if __name__=='__main__':unittest.main()

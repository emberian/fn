"""The raw caller guard repair changes only its proof hint."""
from pathlib import Path
import subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_rewrite import parse,Lst,Pre,Atom
from cns_enum_noop import transform
from cns_next_observation_frames import pairs,declaration
BASE='6fcbd6dbc0bf0e12d1cc7c935c703ad389959e54'
def canon(n):
    if isinstance(n,Lst):return [canon(x) for x in n.items]
    if isinstance(n,Pre):return (n.prefix,canon(n.node))
    return n.text if n.kind=='string' else n.low

def check(before,after):
    before, count = transform(before)
    assert count == 4
    old,new=parse(before).forms,parse(after).forms
    helper=[i for i,n in enumerate(new) if canon(n)==['include-book','"columns-call-guards"']]
    assert len(helper)==1
    new.pop(helper[0])
    observer_include=[i for i,n in enumerate(new) if canon(n)==['include-book','"columns-observation-frames"']]
    assert len(observer_include)==1
    new.pop(observer_include[0])
    frame=['defcolumns-observation-frame','fn2-cns-sources-hash-offset-after-unit-hashed','fn2-cns-sources','hash-offset','unit-hashed']
    frame_events=[i for i,n in enumerate(new) if canon(n)==frame]
    assert len(frame_events)==1
    new.pop(frame_events[0])
    requested=[canon(parse(declaration(*pair)).forms[0]) for pair in pairs(after)]
    actual=[canon(n) for n in new if isinstance(n,Lst) and canon(n)[0]=='defcolumns-observation-frame']
    assert actual==requested
    new=[n for n in new if canon(n) not in requested]
    subjects={'fn2-cns-source-issue-children','fn2-cns-source-raw-step-children','fn2-cns-source-next-children'}
    fns=[n for n in new if isinstance(n,Lst) and canon(n)[0]=='defun' and n.items[1].low in subjects]
    assert len(fns)==3
    for fn in fns:
        xargs=fn.items[3].items[1].items
        assert xargs[-2].low==':guard-hints'
        xargs[-2:]=[]
    for n in new:
        if isinstance(n,Lst) and canon(n)[0]=='fn2-cns-source-frames':
            assert len(n.items)==6
            n.items.pop()
    assert [canon(n) for n in old]==[canon(n) for n in new]
class SourceRawCallHints(unittest.TestCase):
    def setUp(self):
        self.before=subprocess.check_output(['git','show',BASE+':books/cns-source-raw.lisp'],cwd=ROOT,text=True)
        self.after=(ROOT/'books/cns-source-raw.lisp').read_text()
    def test_only_declared_noop_lowering_and_guard_hint_change(self):check(self.before,self.after)
    def test_guard_and_return_mutation_rejected(self):
        with self.assertRaises(AssertionError):check(self.before,self.after.replace('(fn2-cns-sources-wfp fn2-cns-sources)','t',1))
        with self.assertRaises(AssertionError):check(self.before,self.after.replace('(mv :bad 0 0','(mv :bounds 0 0',1))
        with self.assertRaises(AssertionError):check(self.before,self.after.replace('hash-offset unit-hashed)','hash-offset phase)',1))
if __name__=='__main__':unittest.main()

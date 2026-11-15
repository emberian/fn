"""Four actual sites, identity on other forms, and fail-closed alias handling."""
from pathlib import Path
import subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from cns_enum_noop import transform
from lisp_rewrite import parse,match,Lst,Atom,Pre
BASE='4c46607449f33dc604d944d81ea614661eba04e3'
def runtime_forms(text):
    parsed=parse(text)
    for found in match(None,parsed,deep=False,head='defun'):
        if found.node.items[1].low in ('fn2-cns-source-issue-children','fn2-cns-source-raw-step-children'):
            xs=found.node.items[3].items[1].items
            positions=[i for i,n in enumerate(xs) if isinstance(n,Atom) and n.low==':guard-hints']
            if positions:
                i=positions[0]
                del xs[i:i+2]
    def canonical(n):
        if isinstance(n,Lst):return [canonical(x) for x in n.items]
        if isinstance(n,Pre):return (n.prefix,canonical(n.node))
        return n.text if n.kind=='string' else n.low
    return [canonical(n) for n in parsed.forms]

class EnumNoopLowering(unittest.TestCase):
    def setUp(self):
        self.before=subprocess.check_output(['git','show',BASE+':books/cns-source-raw.lisp'],cwd=ROOT,text=True)
    def test_four_actual_sites_and_idempotence(self):
        after,count=transform(self.before)
        self.assertEqual(count,4)
        actual=(ROOT/'books/cns-source-raw.lisp').read_text()
        self.assertEqual(runtime_forms(after),runtime_forms(actual))
        self.assertEqual(transform(actual),(actual,0))
        self.assertEqual(transform(after),(after,0))
    def test_cached_stage_must_be_actual_getter(self):
        with self.assertRaises(ValueError):
            transform(self.before.replace('(stage (fn2-cns-sources-manifest-stage s fn2-cns-sources))','(stage 255)',1))
    def test_unchanged_assignment_runs_stay_grouped(self):
        after,_=transform(self.before)
        puts=match(None,parse(after),deep=True,head='fn2-cns-sources-put')
        groups=[[a.items[0].low for a in p.node.items[2:]] for p in puts]
        self.assertIn(['pending','op-slot','op-gen','unit-length','unit-copied','unit-hashed','phase'],groups)
        self.assertIn(['pending','result-kind','result-outcome','result-reason','result-count'],groups)
        self.assertIn(['offset','unit-copied','unit-index','manifest-index'],groups)
    def test_issue_phase_assignment_is_not_omitted(self):
        after,_=transform(self.before)
        self.assertIn('(phase (if raw *fn2-cns-source-phase-raw-wait* phase))',after)
if __name__=='__main__':unittest.main()

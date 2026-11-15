"""Identity/refusal fixtures for the structural active/pending parameterization."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import checkpoint_summary_rows_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
BEFORE=ROOT/'tools/fixtures/checkpoint-summary-authority-active0-before.lisp'
def canon(node, before=False):
    if hasattr(node,'low'):
        if node.low=='r':return '0'
        return node.low
    values=[canon(x,before) for x in node.items]
    if not values:return ()
    name=values[0]
    if before and isinstance(name,str) and name.startswith(rw.PREFIX+'-') and name[len(rw.PREFIX)+1:] in rw.NAMES:
        values=[rw.PREFIX+'-'+rw.NAMES[name[len(rw.PREFIX)+1:]],'0']+values[1:]
        name=values[0]
    if name=='*' and '0' in values[1:]:return '0'
    if name=='+':
        values=[name]+[x for x in values[1:] if x!='0']
        if len(values)==1:return '0'
        if len(values)==2:return values[1]
    if name=='natp' and values[1:] == ['0']:return 't'
    if name=='<' and values[1:]==['0','2']:return 't'
    if name=='and':
        vals=[]
        for v in values[1:]:
            if v!='t' and v not in vals: vals.append(v)
        values=[name]+vals
    return tuple(values)
def body(source,name):return lr.match(f'(defun {rw.PREFIX}-{name} ?*body)',lr.parse(source).forms,deep=False)[0].node.items[-1]
class Rewrite(unittest.TestCase):
    def test_actual_class_matches_rewriter(self):
        actual=(ROOT/'books/checkpoint-summary-authority-state.lisp').read_text()
        self.assertEqual(actual,rw.rewrite_state(BEFORE.read_text()))
    def test_active_zero_identity(self):
        before=BEFORE.read_text();after=rw.rewrite_state(before)
        for old,new in rw.NAMES.items():
            self.assertEqual(canon(body(before,old),True),canon(body(after,new)),old)
    def test_pending_regions_disjoint(self):
        source=(ROOT/'books/checkpoint-summary-authority-live.lisp').read_text()
        forms=lr.parse(source).forms
        for name in ['descriptori','frontieri','cut-seali']:
            writes=lr.match(f'(update-{rw.PREFIX}-{name} ?index ?*args)',forms)
            self.assertEqual(len(writes),1)
            self.assertTrue(lr.match(f'(+ {rw.ARRAYS[name]} ?i)',[writes[0].captures['index']]))
        for put in lr.match(f'({rw.PREFIX}-put ?row ?*args)',forms):self.assertEqual(put.captures['row'].low,'1')
        begin=lr.match(f'(defun {rw.PREFIX}-live-begin ?*body)',forms)[0].node
        self.assertTrue(lr.match(f'({rw.PREFIX}-live-descriptor 0 c fn2-checkpoint-bytes {rw.PREFIX})',[begin]))
        fixture=f'({rw.PREFIX}-live-descriptor 0 c fn2-checkpoint-bytes {rw.PREFIX})'
        self.assertEqual(rw.pending_live(fixture),fixture)
    def test_missing_reader_refused(self):
        with self.assertRaises(ValueError):rw.parameterize_reader('(defun other () nil)','current-p')
if __name__=='__main__':unittest.main()

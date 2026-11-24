from pathlib import Path
import subprocess,sys,tempfile,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
from lisp_rewrite import parse,match,write,flat
BASE='51770a8bb82257da5363786f41e99ea4a2967fa8'
def baseline(path):return subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT,text=True)
def strip_call_hints(text):
 p=parse(text);ed=[]
 for m in match(None,p,deep=False,head='fn2-cns-source-frames'):
  n=m.node;assert len(n.items)==6
  ed.append((n.items[4].end,n.items[5].end,''))
 assert len(ed)==4
 return [flat(n) for n in parse(write(text,ed)).forms]
class Controls(unittest.TestCase):
 def test_actual_declarations_only_hints(self):
  old=baseline('books/cns-source-raw.lisp');new=(ROOT/'books/cns-source-raw.lisp').read_text()
  self.assertEqual([flat(n) for n in parse(old).forms],strip_call_hints(new))
 def run_control(self,candidate=None):
  with tempfile.NamedTemporaryFile(mode='w',suffix='.lisp') as f:
   f.write(baseline('books/cns-source-state.lisp'));f.flush()
   cmd=['sbcl','--noinform','--script','tests/cns-source-frame-hint-controls.lsp',f.name]
   if candidate:cmd.append(str(candidate))
   return subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=20)
 def test_actual_call_boundaries_cover_custom_contracts(self):
  text=(ROOT/'books/cns-source-raw.lisp').read_text();forms=parse(text).forms
  calls={m.node.items[1].low:m.node for m in match(None,forms,deep=False,head='fn2-cns-source-frames')}
  required={'fn2-cns-source-issue-children':{'fn2-block-read-children','fn2-pool-truncate','fn2-cns-source-heldp'},
            'fn2-cns-source-harvest':set(),
            'fn2-cns-source-raw-step-children':{'fn2-cns-source-hash-begin','fn2-cns-source-hash-update','fn2-cns-source-hash-finish','fn2-block-read-commitment-children'},
            'fn2-cns-source-next-children':{'fn2-rd-copy'}}
  for name,expected in required.items():
   call=calls[name];hint=flat(call.items[5])
   for fn in expected:self.assertIn(fn,hint)
   self.assertIn("'("+name+")",hint)
   self.assertNotIn('fn2-cns-source-ownerp',hint)
  helper=(ROOT/'books/columns-call-guards.lisp').read_text()
  self.assertIn('"-PRESERVES-TYPE"',helper)
  for name in required['fn2-cns-source-raw-step-children']:
   producer='books/block-integrity.lisp' if name=='fn2-block-read-commitment-children' else 'books/cns-source-hash.lisp'
   contract=(ROOT/producer).read_text()
   self.assertIn(name+'-shape',contract)
   self.assertNotIn(name+'-preserves-type',contract)
 def test_actual_legacy_and_supplied_expansions(self):
  r=self.run_control();self.assertEqual(r.returncode,0,r.stdout)
 def test_changed_hyp_or_spec_rejected(self):
  src=(ROOT/'books/cns-source-state.lisp').read_text()
  for old,new in [('"-WFP"','"-ROWS"'),('position :frame child','position :frame nil')]:
   with tempfile.NamedTemporaryFile(mode='w',suffix='.lisp') as f:
    self.assertIn(old,src);f.write(src.replace(old,new,1));f.flush()
    self.assertNotEqual(self.run_control(f.name).returncode,0)
if __name__=='__main__':unittest.main()

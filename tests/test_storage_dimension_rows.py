from pathlib import Path
import subprocess,tempfile,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
from lisp_rewrite import parse,match,flat,Lst
BASE='d7973ce449dfaa3ff4e5c45864a24d3f534018ca'
def baseline(path):return subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT,text=True)
def is_dimension(n):return isinstance(n,Lst) and len(n.items)>3 and flat(n.items[0])=='fn2-pool-preserves' and ':specs' in [flat(x) for x in n.items] and '"-DIMENSION-ROWS"' in flat(n)
def abi_check(n):return isinstance(n,Lst) and flat(n).startswith("(assert-event (eq (nth 3 (getpropc")
def canonical(n):
 if not isinstance(n,Lst):return flat(n)
 return tuple(canonical(x) for x in n.items if not is_dimension(x) and not abi_check(x))
class Rows(unittest.TestCase):
 def test_all_original_storage_forms_exact(self):
  old=parse(baseline('books/storage-block-io.lisp')).forms;new=parse(ROOT/'books/storage-block-io.lisp').forms
  self.assertEqual([canonical(x) for x in old],[canonical(x) for x in new if not is_dimension(x) and not abi_check(x)])
  facts=match(None,new,deep=True,head='fn2-pool-preserves')
  added=[m.node for m in facts if is_dimension(m.node)]
  self.assertEqual({flat(n.items[1]) for n in added},{'fn2-pinned-block-io-children','fn2-block-read-children','fn2-block-write-children'})
  for n in added:
   self.assertIn('(("-DIMENSION-ROWS" fn2-pool-rows 3 :frame fn2-pool))',flat(n))
 def test_primitive_runtime_guards_and_old_contract_exact(self):
  old=parse(baseline('books/arm-children.lisp')).forms;new=parse(ROOT/'books/arm-children.lisp').forms
  for head in ('defun','fn2-pool-preserves'):
   a=[flat(m.node) for m in match(None,old,deep=False,head=head)]
   b=[flat(m.node) for m in match(None,new,deep=False,head=head) if not is_dimension(m.node)]
   self.assertEqual(a,b)
 def test_actual_wrapper_factory_and_unconditional_statement(self):
  with tempfile.NamedTemporaryFile(mode='w',suffix='.lisp') as f:
   f.write(baseline('books/arm-children.lisp'));f.flush()
   r=subprocess.run(['sbcl','--noinform','--script','tests/storage-dimension-row-controls.lsp',f.name],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=20)
   self.assertEqual(r.returncode,0,r.stdout)
 def test_wrong_projection_frame_and_runtime_mutants_rejected(self):
  source=(ROOT/'books/arm-children.lisp').read_text()
  mutations=[('"-DIMENSION-ROWS" fn2-pool-rows 3','"-DIMENSION-ROWS" fn2-pool-rows 4'),(':frame fn2-pool',':frame nil'),('(fn2-issue-children ,kind','(fn2-core-lease ,kind')]
  with tempfile.NamedTemporaryFile(mode='w',suffix='.lisp') as old:
   old.write(baseline('books/arm-children.lisp'));old.flush()
   for a,b in mutations:
    self.assertIn(a,source)
    with tempfile.NamedTemporaryFile(mode='w',suffix='.lisp') as changed:
     changed.write(source.replace(a,b));changed.flush()
     r=subprocess.run(['sbcl','--noinform','--script','tests/storage-dimension-row-controls.lsp',old.name,changed.name],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=20)
     self.assertNotEqual(r.returncode,0,(a,r.stdout))
if __name__=='__main__':unittest.main()

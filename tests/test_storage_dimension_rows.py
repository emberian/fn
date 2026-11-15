from pathlib import Path
import subprocess,tempfile,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
from lisp_rewrite import parse,match,flat,Lst
from add_pool_dimension_interfaces import transform
BASE='d7973ce449dfaa3ff4e5c45864a24d3f534018ca'
def baseline(path,commit=BASE):return subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT,text=True)
def dimension(n):return isinstance(n,Lst) and bool(n.items) and (flat(n.items[0])=='fn2-pool-dimensions' or flat(n)=='(include-book "pool-dimensions")')
def canonical(n):
 if not isinstance(n,Lst):return flat(n)
 return tuple(canonical(x) for x in n.items if not dimension(x))
class Dimensions(unittest.TestCase):
 def test_all_original_storage_forms_exact(self):
  old=parse(baseline('books/storage-block-io.lisp')).forms;new=parse(ROOT/'books/storage-block-io.lisp').forms
  self.assertEqual([canonical(x) for x in old],[canonical(x) for x in new if not dimension(x)])
  added=match(None,new,deep=True,head='fn2-pool-dimensions')
  self.assertEqual({flat(m.node.items[1]) for m in added},{'fn2-pinned-block-io-children','fn2-block-read-children','fn2-block-write-children'})
 def test_primitive_runtime_guards_and_old_contract_exact(self):
  old=parse(baseline('books/arm-children.lisp')).forms;new=parse(ROOT/'books/arm-children.lisp').forms
  for head in ('defun','fn2-pool-preserves'):
   self.assertEqual([flat(m.node) for m in match(None,old,deep=False,head=head)], [flat(m.node) for m in match(None,new,deep=False,head=head)])
 def control(self,arm=None,helper=None):
  with tempfile.NamedTemporaryFile(mode='w',suffix='.lisp') as old:
   old.write(baseline('books/arm-children.lisp'));old.flush()
   return subprocess.run(['sbcl','--noinform','--script','tests/storage-dimension-row-controls.lsp',old.name,str(arm or ROOT/'books/arm-children.lisp'),str(helper or ROOT/'books/pool-dimensions.lisp')],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=20)
 def test_actual_wrapper_factory_unconditional_statement_and_invalid_requests(self):
  r=self.control();self.assertEqual(r.returncode,0,r.stdout)
 def test_frame_and_runtime_mutants_rejected(self):
  for file,changes in [('books/arm-children.lisp',[('(fn2-issue-children ,kind','(fn2-core-lease ,kind')]),('books/pool-dimensions.lisp',[(':frame \'fn2-pool',':frame \'nil'),('position :frame','(+ 1 position) :frame')])]:
   source=(ROOT/file).read_text()
   for a,b in changes:
    self.assertIn(a,source)
    with tempfile.NamedTemporaryFile(mode='w',suffix='.lisp') as changed:
     changed.write(source.replace(a,b));changed.flush()
     r=self.control(**({'arm':changed.name} if file.endswith('arm-children.lisp') else {'helper':changed.name}))
     self.assertNotEqual(r.returncode,0,(a,r.stdout))
 def test_named_transform_identity_completeness_and_idempotence(self):
  for name,count in [('arm-children',5),('storage-block-io',3)]:
   old=baseline('books/'+name+'.lisp','31635689e152fa20aa3e9eb18ae456ebe2397b64')
   out,n=transform(old,name);self.assertEqual(n,count)
   self.assertEqual([flat(x) for x in parse(out).forms],[flat(x) for x in parse(ROOT/'books'/(name+'.lisp')).forms])
   self.assertEqual(transform(out,name),(out,0))
   removed=out.replace('(fn2-pool-dimensions fn2-core-lease :opaque (fn2-pool-lease-in fn2-pool-lease-out))','') if name=='arm-children' else out.replace('(fn2-pool-dimensions fn2-block-read-children :opaque (fn2-pinned-block-io-children))','')
   self.assertNotEqual(out,removed)
   with self.assertRaises(AssertionError):transform(removed,name)
if __name__=='__main__':unittest.main()

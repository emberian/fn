#!/usr/bin/env python3
"""Current ROOT preservation controls; no ACL2 evaluation or cache qualification."""
from pathlib import Path
import hashlib,subprocess,unittest
import lisp_rewrite as lr
import run_bound_root_projection as rw
import storage_block_io_lower as io_lower
ROOT=Path(__file__).resolve().parents[1]
BASE='0234c0de23a19ca446b8764bdfb2bb35462c80a2'
def read(p):return (ROOT/p).read_text()
def tree(n):
 if isinstance(n,lr.Pre):return (n.prefix,tree(n.node))
 return tuple(tree(x) for x in n.items) if hasattr(n,'items') else n.low
def table(s):return rw.one(s,'(defcolumns fn2-boot-config ?*b)')
def fields(n):
 xs=list(n.items);at=next(i for i,x in enumerate(xs) if x.low==':extra-fields');return xs[at+1].items
def named(s):
 return {n.items[1].low:tree(n) for n in lr.parse(s).forms if hasattr(n,'items') and len(n.items)>1 and n.items[0].low.startswith('def') and not hasattr(n.items[1],'items')}
class RootProjection(unittest.TestCase):
 def test_old_root_fields_and_actual_provider_fields_are_exact(self):
  old=read('tools/fixtures/run-bound-root/boot-before.lisp');provider=read('tools/fixtures/run-bound-root/boot-provider-fields.lisp')
  after,lower=rw.boot(old,provider)
  a,b=fields(table(old)),fields(table(lower))
  self.assertEqual([tree(x) for x in a],[tree(x) for x in b[2:]])
  self.assertEqual([tree(x) for x in b[:2]],[tree(x) for x in lr.parse(provider).forms])
  self.assertEqual(tree(table(lower)),tree(table(read('books/boot-config-state.lisp'))))
  self.assertIn('(defun untouched () 42)',after)
 def test_current_root_boot_operations_and_guards_are_preserved(self):
  before=named(subprocess.check_output(['git','show',BASE+':books/boot-kind.lisp'],cwd=ROOT,text=True));after=named(read('books/boot-kind.lisp'))
  for excluded in ('fn2-boot-config','*fn2-boot-group-entry-bytes*'):before.pop(excluded)
  self.assertEqual(before,after)
 def test_current_foundations_are_retained(self):
  for p in ('books/alloc.lisp','books/columns.lisp','books/machines.lisp','books/runs-schema.lisp','books/runs-assemble.lisp'):
   self.assertEqual((ROOT/p).read_bytes(),subprocess.check_output(['git','show',BASE+':'+p],cwd=ROOT),p)
  before_b=subprocess.check_output(['git','show',BASE+':books/machines-b.lisp'],cwd=ROOT,text=True)
  before_resources=subprocess.check_output(['git','show','de31cba77741e057b78e00faa33539346340d3d8:books/run-physical-resources.lisp'],cwd=ROOT,text=True)
  expected_b,_,_=io_lower.transform(before_b,before_resources)
  self.assertEqual(read('books/machines-b.lisp'),expected_b)
  self.assertEqual(hashlib.sha256((ROOT/'books/pool.lisp').read_bytes()).hexdigest(),'3ef26f41207ee64f6121621cc24d7100936e364b5224a4be8ae28292aa4d7fa7')
  for name in ('fn2-pool-query-acquire','fn2-pool-query-heldp','fn2-pool-query-release'):self.assertIn(name,named(read('books/pool.lisp')))
 def test_resource_leaf_has_no_profile_constructor_requirement(self):
  s=read('books/run-physical-resources.lisp')
  self.assertNotIn('fn2-b-run-cursor-rows',s);self.assertNotIn('defun fn2-run-load-profile-init',s)
  self.assertIn('(include-book "storage-block-io")',s)
 def test_replay_retains_future_root_fields_and_rejects_duplicates(self):
  s=read('tools/fixtures/run-bound-root/boot-before.lisp').replace('((fn2-boot-config-groups','((root-future-flag :type (unsigned-byte 1) :initially 0) (fn2-boot-config-groups')
  _,lower=rw.boot(s,read('tools/fixtures/run-bound-root/boot-provider-fields.lisp'))
  self.assertIn('root-future-flag',lower)
  with self.assertRaises(ValueError):rw.boot(lower,read('tools/fixtures/run-bound-root/boot-provider-fields.lisp'))
if __name__=='__main__':unittest.main()

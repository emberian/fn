"""Actual C-slot provider/consumer checks; not ACL2 execution evidence."""
from pathlib import Path
import json,hashlib,unittest
import lisp_rewrite as lr
import identity_arena_thread as thread
ROOT=Path(__file__).resolve().parents[1]
class Arena(unittest.TestCase):
 def test_programmed_class_and_real_call_arities(self):
  receipt=json.loads((ROOT/'tools/fixtures/identity-arena-thread.json').read_text())
  for row in receipt:
   self.assertEqual(hashlib.sha256(row['original'].encode()).hexdigest(),row['sha256'])
   first,n=thread.transform(row['original'],row['file'].startswith('tests/'),set(row['targets']))
   self.assertEqual(n,row['edits'])
   # Frame dependency lists remain data; only true applications get a count.
   for top in lr.parse(first).forms:
    for node in thread.walk(top):
     if isinstance(node,lr.Lst) and len(node.items)>2 and thread.atom(node.items[0]) in thread.FRAMES:
      if thread.atom(node.items[1]) in set(row['targets']):
       self.assertEqual(thread.atom(node.items[2].items[0]),'commitrows')
  definitions={}
  for f in ['books/machines-c-stage.lisp','books/machines-c-bind.lisp','books/machines-c-groups.lisp','books/sealer.lisp']:
   for top in lr.parse((ROOT/f).read_text()).forms:
    for n in thread.walk(top):
     if isinstance(n,lr.Lst) and len(n.items)>2 and thread.atom(n.items[0])=='defun' and thread.atom(n.items[1]) in thread.TARGETS:
      definitions[thread.atom(n.items[1])]=len(n.items[2].items)
  for row in receipt:
   for top in lr.parse((ROOT/row['file']).read_text()).forms:
    for n in thread.walk(top):
     if isinstance(n,lr.Lst) and n.items and thread.atom(n.items[0]) in definitions:
      self.assertEqual(len(n.items)-1,definitions[thread.atom(n.items[0])],row['file'])
 def test_exact_geometry_no_suffix_guess_or_partial_fallback(self):
  s=(ROOT/'books/identity-arena-credit.lisp').read_text()
  self.assertIn('(equal (fn2-pool-credit-group-count fn2-pool)\n              (fn2-idc-arena-credit-total commitrows (fn2-overlays-rows fn2-overlays)))',s)
  self.assertIn('(equal (fn2-pool-credit-configured fn2-pool) 0)',s)
  self.assertNotIn('(- (fn2-pool-credit-group-count',s)
  self.assertIn('(fn2-idc-arena-credit-quota-p 0 group class fn2-pool)',s)
  self.assertIn('(fn2-pool-credit-abort-empty',s)
 def test_connected_actual_reserve_return_and_no_double_arena_count(self):
  stage=(ROOT/'books/machines-c-stage.lisp').read_text()
  self.assertIn('(fn2-idc-arena-start o commitrows arena (* o icap) icap',stage)
  for f in ['books/machines-c-bind.lisp','books/sealer.lisp']:
   self.assertIn('(fn2-idc-arena-return o commitrows fn2-overlays fn2-pool)',(ROOT/f).read_text())
  service=(ROOT/'books/checkpoint-service-geometry.lisp').read_text()
  self.assertNotIn('(* (len *fn2-checkpoint-post-schema-ids*) arenas)',service)
  self.assertNotIn('(* names arenas)',service)
  config=(ROOT/'books/checkpoint-working-credit.lisp').read_text()
  self.assertIn('(fn2-idc-arena-credit-groups overlayrows arenas)',config)
  self.assertIn('(fn2-overlays-rows fn2-overlays)',(ROOT/'books/checkpoint-working-credit-init.lisp').read_text())
 def test_controls_use_real_lifecycle(self):
  s=(ROOT/'tests/identity-arena-credit-unit.lisp').read_text()
  for x in ['fn2-idc-add-spare','fn2-idc-arena-start','fn2-seal-retire','fn2-pool-query-acquire','fn2-pool-query-release',
            'stale-refused','wrong-refused','unwound','depleted','(fn2-iacu-run nil)','(fn2-iacu-run t)']:
   self.assertIn(x,s)
  self.assertNotIn('fn2-pool-set-gen',s)
 def test_all_actual_arena_producers_and_bound_geometry_scope(self):
  source=(ROOT/'books/machines-c-groups.lisp').read_text()
  self.assertIn('(fn2-idc-arena-create o commitrows sid arena (* o icap) icap',source)
  self.assertNotIn('(fn2-pool-reserve class *fn2-idc-owner-kind*',source)
  bind=(ROOT/'books/machines-c-bind.lisp').read_text()
  self.assertIn('(fn2-succ-replay (fn2-commit-rows fn2-commit)',bind)
  for file in ['books/machines-c-stage.lisp','books/machines-c-bind.lisp','books/machines-c-groups.lisp','books/sealer.lisp']:
   text=(ROOT/file).read_text()
   for hit in lr.match('_',lr.parse(text).forms,deep=True,head='defun'):
    node=hit.node
    uses=any(isinstance(x,lr.Atom) and x.text=='commitrows' for part in node.items[3:] for x in thread.walk(part))
    if uses:self.assertIn('commitrows',[getattr(x,'text','') for x in node.items[2].items],(file,getattr(node.items[1],'text','')))

if __name__=='__main__':unittest.main()

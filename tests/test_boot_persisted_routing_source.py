"""Actual BOOT source composition controls; not execution/certification."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import boot_persisted_routing_rewrite as rw
class BootRouting(unittest.TestCase):
 def test_named_actual_projection(self):
  for n,fn in [('executor',rw.constructor),('boot-kind',rw.kind),('boot',rw.arms)]:
   self.assertEqual(fn(rw.BEFORE[n]),(ROOT/'books'/(n+'.lisp')).read_text(),n)
 def test_constructor_canonical_layout_and_two_actual_classes(self):
  s=rw.constructor(rw.BEFORE['executor'])
  self.assertIn('(fn2-checkpoint-image-sizep size extents groups)',s)
  self.assertNotIn('12288',s)
  self.assertIn('(fn2-pool-class-for *fn2-format-page-size*',s)
  self.assertIn('(fn2-pool-class-for *fn2-format-sector-size*',s)
  self.assertIn('(fn2-core-reserve rxclass *fn2-boot-kind* id gen',s)
  self.assertIn('(fn2-core-release slot sgen *fn2-boot-kind* id gen',s)
  # Refusal has no caller-visible success or READY transition.
  start=s.index('((unless (and (eq code :ok) (unsigned-byte-p 32 rx)')
  self.assertLess(start,s.index('(fn2-boot-put-core id'))
 def test_phase_append_and_holds_preserve_old_numbers(self):
  old=rw.BEFORE['boot-kind'];new=rw.kind(old)
  def machine(s):
   return next(x for x in lr.parse(s).forms if isinstance(x,lr.Lst) and len(x.items)>1 and getattr(x.items[1],'low','')=='fn2-boot')
  def value(m,k):
   return next(m.items[i+1] for i,x in enumerate(m.items[:-1]) if getattr(x,'low','')==k)
  a=value(machine(old),':states').items;b=value(machine(new),':states').items
  self.assertEqual([x.low for x in a],[x.low for x in b[:len(a)]])
  self.assertEqual(set(x.low for x in b[len(a):]),{':'+x for x in rw.PHASES})
 def test_result_ack_and_parser_progress_are_distinct(self):
  s=rw.arms(rw.BEFORE['boot'])
  for prefix in ['bootstrap','checkpoint-anchor','checkpoint-descriptor']:
   self.assertIn('(:'+prefix+'-result :on-refusal',s)
   self.assertIn('(:next :'+prefix+'-step)' if prefix!='bootstrap' else '(:next :bootstrap-verify)',s)
  self.assertIn('(fn2-boot-checkpoint-anchor-step id row-generation 4096)',s)
  self.assertIn('(fn2-boot-checkpoint-descriptor-check row-checkpoint-index row-rx-slot row-rx-gen id row-generation 4096)',s)
  self.assertIn('(pending 0)',s)
 def test_nonempty_descriptor_cannot_fall_through_to_serving(self):
  s=(ROOT/'tools/boot_persisted_routing_arms.lisp').read_text()
  self.assertIn('(:checkpoint-restore (:idle))',s)
  descriptor=s[s.index('(:checkpoint-descriptor-step'):]
  self.assertNotIn('(:next :recover)',descriptor)
  self.assertNotIn('(:next :ready)',descriptor)
  self.assertIn('(checkpoint-invalid (if (eq code :invalid) 1 row-checkpoint-invalid))',s)
 def test_projection_rejects_missing_constructor_authority(self):
  with self.assertRaises(ValueError):rw.constructor(rw.BEFORE['executor'].replace('(fn2-core-reserve class *fn2-boot-kind* id gen fn2-core)','(other-reserve)'))
if __name__=='__main__':unittest.main()

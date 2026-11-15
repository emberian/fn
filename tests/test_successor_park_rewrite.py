"""Exact CLOSE carrier transformation controls; no Lisp evaluation."""
from pathlib import Path
import sys,unittest,re
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from successor_park_rewrite import transform,ADDED
import lisp_rewrite as lr
def walk(n):
 yield n
 if isinstance(n,lr.Pre):yield from walk(n.node)
 if isinstance(n,lr.Lst):
  for x in n.items:yield from walk(x)
def valuewalk(n):
 yield n
 if isinstance(n,lr.Pre):yield from valuewalk(n.node)
 if isinstance(n,lr.Lst):
  if words(n)[:1]==["b*"]:
   for binding in n.items[1].items:
    if isinstance(binding,lr.Lst) and len(binding.items)==2:yield from valuewalk(binding.items[1])
   for x in n.items[2:]:yield from valuewalk(x)
  else:
   for x in n.items:yield from valuewalk(x)
def words(n):return [x.low for x in n.items if isinstance(x,lr.Atom)]
def definition(name):
 forms=[]
 for p in ("machines-c-successor.lisp","machines-c-bind.lisp"):
  forms.extend(lr.parse((ROOT/"books"/p).read_text()).forms)
 return next(n for n in forms if isinstance(n,lr.Lst) and words(n)[:2]==["defun",name])
class Rewrite(unittest.TestCase):
 def test_mutable_outputs_and_readonly_pool_are_distinct(self):
  old='(defun fn2-succ-source-close (tx fn2-c-source-control fn2-c-source-readers) (declare (xargs :stobjs (fn2-c-source-control fn2-c-source-readers))) (mv :ok fn2-succ-txns fn2-c-source-control fn2-c-source-readers))'
  new,n=transform(old);self.assertGreater(n,0)
  self.assertEqual(transform(new),(new,0))
  self.assertEqual(new.split('(mv',1)[1].count('fn2-pool'),0)
  for child in ADDED:self.assertIn(child,new)
 def test_existing_pool_and_acquire_api_are_preserved(self):
  untouched='(defun fn2-succ-source-acquire (tx ctrl readers) (mv :ok fn2-succ-txns fn2-c-source-control fn2-c-source-readers))'
  self.assertEqual(transform(untouched),(untouched,0))
  old='(defun fn2-succ-resolve-observed (tx fn2-pool) (declare (xargs :stobjs (fn2-pool))) (mv :ok fn2-succ-txns fn2-c-source-control fn2-c-source-readers))'
  new,n=transform(old);self.assertEqual(new.count('fn2-pool'),2)
 def test_actual_class_is_idempotent(self):
  for p in ('machines-c-successor.lisp','machines-c-bind.lisp','machines-c-groups.lisp'):
   text=(ROOT/'books'/p).read_text();self.assertEqual(transform(text),(text,0))
 def test_close_orders_exact_receipt_then_park_then_single_clear_then_release(self):
  n=definition('fn2-succ-source-close');text=(ROOT/'books/machines-c-successor.lisp').read_text()[n.start:n.end]
  expected=['fn2-c-source-reader-current-p','fn2-run-load-region-park','fn2-succ-clear-ref-rows','fn2-c-source-reader-release']
  offsets=[text.index(x) for x in expected];self.assertEqual(offsets,sorted(offsets))
  self.assertEqual(text.count('fn2-succ-clear-ref-rows'),1)
  self.assertIn('(equal (fn2-c-source-readers-live endpoint fn2-c-source-readers) 0)',text)
  for x in ('kind','owner','generation'):self.assertIn('(fn2-run-loads-'+x+' tx fn2-run-loads)',text)
  self.assertNotIn('fn2-pool-release',text)
 def test_actual_lower_calls_and_output_counts(self):
  arities={name:len(definition(name).items[2].items) for name in ('fn2-succ-source-close','fn2-succ-resolve-observed','fn2-succ-release-observed')}
  for path in ('machines-c-successor.lisp','machines-c-bind.lisp','machines-c-groups.lisp'):
   for f in lr.parse((ROOT/'books'/path).read_text()).forms:
    for n in walk(f):
     if not isinstance(n,lr.Lst) or not n.items:continue
     h=n.items[0].low if isinstance(n.items[0],lr.Atom) else ''
     if h in arities and len(n.items)>1 and isinstance(n.items[1],lr.Atom) and n.items[1].low=="tx":self.assertEqual(len(n.items)-1,arities[h],(path,h))
  for name,count in (('fn2-succ-source-close',9),('fn2-succ-resolve-observed',11),('fn2-succ-release-observed',11)):
   n=definition(name);self.assertEqual(len(words(n.items[2])),len(set(words(n.items[2]))))
   results=[x for x in valuewalk(n) if isinstance(x,lr.Lst) and words(x)[:1]==['mv'] and 'fn2-succ-txns' in words(x)]
   self.assertTrue(results)
   for result in results:
    self.assertEqual(len(result.items)-1,count);self.assertNotIn('fn2-pool',words(result));self.assertLessEqual(count,32)
 def test_lower_include_dag_has_no_c_read_or_successor_backedge(self):
  pending=['run-physical-park-region'];seen=set()
  while pending:
   name=pending.pop()
   if name in seen:continue
   seen.add(name);p=ROOT/'books'/(name+'.lisp')
   if not p.exists():continue
   for child in re.findall(r'\(include-book "([^"]+)"',p.read_text()):
    target=(p.parent/child).resolve()
    try:relative=target.relative_to(ROOT/'books').as_posix()
    except ValueError:continue
    pending.append(relative)
  for name in ('machines-c-read','machines-c-successor','machines-c-bind','machines-c-groups'):self.assertNotIn(name,seen)
 def test_canonical_guard_and_prepared_controls_have_teeth(self):
  body=(ROOT/'books/run-physical-release.lisp').read_text().split('(defun fn2-run-load-parkable-p',1)[1]
  self.assertIn('(equal (fn2-run-loads-pending c fn2-run-loads) 0)',body)
  fixture=(ROOT/'tests/successor-park-close-unit.lisp').read_text()
  for mode in (':ok',':owner',':hand'):self.assertIn('(assert-event (fn2-spc-test '+mode+'))',fixture)
  for call in ('fn2-run-load-reserve','fn2-checkpoint-summary-acquire','fn2-pool-hand','fn2-pool-accept-hand','fn2-succ-source-close'):self.assertIn('('+call,fixture)
  self.assertNotIn('set-pending',fixture);self.assertNotIn('phase-ready',fixture)
if __name__=='__main__':unittest.main()

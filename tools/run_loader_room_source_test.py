from pathlib import Path
import unittest
import lisp_rewrite as lr
from run_loader_room_rewrite import project
ROOT=Path(__file__).resolve().parents[1]
class Room(unittest.TestCase):
 def test_exact_three_counter_projection(self):
  before=(ROOT/'tools/fixtures/run-physical-park/room-before.lisp').read_text()
  actual=(ROOT/'books/run-physical-resources.lisp').read_text()
  self.assertEqual(project(before),actual)
  with self.assertRaises(ValueError):project(actual)
 def test_alias_sums_actual_reservable_demand(self):
  s=(ROOT/'books/run-physical-resources.lisp').read_text()
  fn=lr.match('(defun fn2-run-load-roomp ?*body)',lr.parse(s).forms)[0]
  t=s[fn.start:fn.end]
  self.assertIn('(<= (* 2 n) (fn2-pool-reservable-count pc fn2-pool))',t)
  self.assertIn('(<= n (fn2-pool-reservable-count pc fn2-pool))',t)
  self.assertIn('(<= n (fn2-pool-reservable-count sc fn2-pool))',t)
  self.assertNotIn('credit-protected',t)
  p=(ROOT/'books/pool.lisp').read_text()
  reserve=lr.match('(defun fn2-pool-reserve ?*body)',lr.parse(p).forms)[0]
  self.assertIn('(fn2-pool-reservable-count class fn2-pool)',p[reserve.start:reserve.end])
 def test_actual_shortage_release_progress_control(self):
  s=(ROOT/'tests/run-loader-reservable-room-unit.lisp').read_text()
  for name in ('fn2-pool-credit-configure','fn2-pool-reserve','fn2-run-load-region-reserve','fn2-pool-release','fn2-run-load-region-clean'):
   self.assertIn('('+name+' ',s)
  self.assertIn('*fn2-b-query-loader-jobs*',s)
  self.assertIn('(equal before after-refusal)',s)
  self.assertIn('(not (fn2-run-load-roomp jobs fn2-pool))',s)
  self.assertNotIn('update-fn2-pool-class-counts',s)
if __name__=='__main__':unittest.main()

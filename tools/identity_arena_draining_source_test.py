"""C-slot composition preserves the actual DRAINING state machine exactly."""
from pathlib import Path
import json,unittest
import lisp_rewrite as lr
import identity_arena_draining_projection as p
ROOT=Path(__file__).resolve().parents[1]
class Composition(unittest.TestCase):
 def test_program_replays_every_changed_draining_consumer(self):
  rows=json.loads(p.RECORD.read_text())
  self.assertGreaterEqual(len(rows),5)
  for row in rows:
   self.assertEqual(p.project(row),(ROOT/row['file']).read_text(),row['file'])
 def test_inverse_rejects_a_state_machine_mutation(self):
  s=(ROOT/'books/sealer.lisp').read_text()
  self.assertIn('*fn2-overlay-phase-draining*',s)
  bad=s.replace('*fn2-overlay-phase-draining*','*fn2-overlay-phase-free*',1)
  with self.assertRaises(AssertionError):p.before_current('books/sealer.lisp',bad)
 def test_install_does_not_gain_unused_credit_parameter(self):
  s=(ROOT/'books/sealer.lisp').read_text();n=p.one(s,'fn2-seal-install')
  self.assertNotIn('commitrows',s[n.start:n.end])
  self.assertTrue(lr.match('(fn2-overlays-set-phase o *fn2-overlay-phase-draining* fn2-overlays)',[n]))
 def test_real_return_provider_keeps_draining_gate(self):
  s=(ROOT/'books/sealer.lisp').read_text();n=p.one(s,'fn2-seal-overlay-return')
  self.assertTrue(lr.match('(equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-draining*)',[n]))
  self.assertTrue(lr.match('(fn2-seal-retire commitrows o fn2-overlays fn2-pool)',[n]))
  n=p.one(s,'fn2-seal-retire')
  self.assertTrue(lr.match('(fn2-idc-arena-return o commitrows fn2-overlays fn2-pool)',[n]))
if __name__=='__main__':unittest.main()

from pathlib import Path
import subprocess,sys,unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
class OwnedControl(unittest.TestCase):
 def setUp(self):
  self.path=ROOT/'tests/checkpoint-projection-identity-unit.lisp';self.text=self.path.read_text();self.forms=lr.parse(self.text).forms
 def test_generated_from_actual_owned_signature(self):
  subprocess.run([sys.executable,'tools/checkpoint_projection_owned_control.py'],cwd=ROOT,check=True)
  self.assertEqual(self.path.read_text(),self.text)
  runtime=lr.match('(defun fn2-checkpoint-projection-owned-step ?*body)',lr.parse((ROOT/'books/checkpoint-owned-projection.lisp').read_text()).forms,deep=False)[0].node
  call=lr.match('(fn2-checkpoint-projection-owned-step ?*args)',self.forms)[0].node
  self.assertEqual([lr.flat(x) for x in runtime.items[2].items],[lr.flat(x) for x in call.items[1:]])
 def test_every_owned_turn_observes_actual_loop_and_guards(self):
  drive=lr.match('(defun fn2-cpi-owned-drive ?*body)',self.forms,deep=False)[0].node
  self.assertEqual(len(lr.match('(fn2-checkpoint-projection-index-loop-p ?*args)',[drive])),2)
  self.assertEqual(len(lr.match('(fn2-checkpoint-projection-index-carriers ?*args)',[drive])),2)
  self.assertFalse(lr.match('(fn2-alloc-identity-ready ?*args)',[drive]))
  self.assertFalse(lr.match('(update-fn2-alloc-identity-phase ?*args)',[drive]))
 def test_owner_corruption_only_after_observed_probe_or_ready(self):
  drive=lr.match('(defun fn2-cpi-owned-drive ?*body)',self.forms,deep=False)[0].node
  self.assertTrue(lr.match('(and (eq mode :probe-owner) (= phase *fn2-alloc-identity-phase-probe*))',[drive]))
  self.assertTrue(lr.match('(and (eq mode :ready-owner) (= phase *fn2-alloc-identity-phase-ready*))',[drive]))
  self.assertTrue(lr.match('(equal before (fn2-cpi-snapshot ?*args))',[drive]))
  for mode in ('nil',':probe-owner',':ready-owner'):
   self.assertTrue(lr.match(f'(assert-event (fn2-cpi-run {mode}))',self.forms))
if __name__=='__main__':unittest.main()

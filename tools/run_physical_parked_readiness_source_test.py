"""Source checks for actual-owned parked readiness; no ACL2 claim."""
from pathlib import Path
import json
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def fn(source,name):
 m=lr.match('(defun '+name+' ?*body)',lr.parse(source).forms)
 assert len(m)==1,(name,len(m))
 return m[0]
class ParkedReadiness(unittest.TestCase):
 def setUp(self):
  self.s=(ROOT/'books/run-physical-readiness.lisp').read_text()
  self.core=(ROOT/'books/run-physical-readiness-core.lisp').read_text()
 def test_exact_stripe_extraction(self):
  saved=json.loads((ROOT/'tools/fixtures/run-physical-park/readiness-stripe.json').read_text())
  helper=fn(self.s,'fn2-run-load-readiness-stripe-p').node.items[-1]
  self.assertEqual(self.s[helper.start:helper.end],saved['stripe'])
  old=fn(self.s,'fn2-run-load-readiness-one-row-p')
  call=lr.match('(fn2-run-load-readiness-stripe-p ?*args)',[old.node])[0]
  text=self.s[old.start:old.end]
  restored=lr.write(text,[(call.start-old.start,call.end-old.start,saved['stripe'])])
  self.assertEqual(restored,saved['original'])
 def test_one_transition_implementation(self):
  saved=json.loads((ROOT/'tools/fixtures/run-physical-park/readiness-step.json').read_text())['original']
  m=fn(self.s,'fn2-run-load-readiness-step-with-owner');f=m.node
  gate=lr.match('(or (fn2-run-load-readiness-one-row-p ?*args) ?other)',[f])[0]
  strict=gate.node.items[1]
  text=self.s[m.start:m.end]
  changes=[(f.items[1].start-m.start,f.items[1].end-m.start,'fn2-run-load-readiness-step'),
   (f.items[2].items[1].start-m.start,f.items[2].items[4].start-m.start,''),
   (gate.start-m.start,gate.end-m.start,self.s[strict.start:strict.end])]
  self.assertEqual(lr.write(text,changes),saved)
  public=fn(self.s,'fn2-run-load-readiness-step')
  text=self.s[public.start:public.end]
  self.assertIn('(fn2-run-load-readiness-step-with-owner budget 0 0 0 ',text)
  self.assertNotIn('set-',text)
 def test_parked_checks_actual_resources(self):
  m=fn(self.s,'fn2-run-load-readiness-parked-row-p');text=self.s[m.start:m.end]
  for fragment in ('fn2-run-load-parkable-p','*fn2-run-load-phase-reserved*','(source ',):
   if fragment=='(source ':continue
   self.assertIn(fragment,text)
  for f in ('source','tag','physical','live'):
   self.assertIn('-'+f+' c ',text)
  self.assertIn('(<= *fn2-format-page-size* (fn2-pool-cap',text)
  self.assertIn('(<= *fn2-commit-unit-bytes* (fn2-pool-cap',text)
  self.assertIn('fn2-run-load-readiness-stripe-p',text)
 def test_actual_machine_not_caller_ready(self):
  for required in ('fn2-machine-idp owner','fn2-machine-generation-read-code owner',
   '(equal generation (fn2-machine-generation owner','(equal kind (fn2-machine-kind owner',
   'fn2-c-actor-loader-plan owner generation','fn2-cursor-snapshot-read-code owner',
   'fn2-sealer-snapshot-read-code owner','fn2-run-load-region-member-p'):
   self.assertIn(required,self.core)
  m=fn(self.core,'fn2-run-load-readiness-owned-step');text=self.core[m.start:m.end]
  self.assertEqual([x.text for x in m.node.items[2].items],['budget','fn2-core'])
  self.assertLess(text.index('(fn2-run-load-parked-machine-current-p c fn2-core)'),text.index('(fn2-run-load-readiness-step-with-owner'))
  self.assertNotIn('ready-p',text)
  self.assertNotIn('fn2-checkpoint-summary-set-phase',self.core)
 def test_resource_owner_control_uses_real_constructors(self):
  s=(ROOT/'tests/run-physical-parked-owner-unit.lisp').read_text()
  for name in ('fn2-core-init','fn2-machine-take-fn2-auth','fn2-c-actor-loader-plan','fn2-run-load-region-reserve','fn2-run-load-region-park','fn2-rpo-ready-p'):
   self.assertIn('('+name+' ',s)
  self.assertIn('(and H refused)',s)
  self.assertIn('(fn2-run-loads-set-generation b0 (+ 1 gen)',s)
  self.assertNotIn('summary-set-phase',s)
  self.assertNotIn('phase-applied',s)
if __name__=='__main__':unittest.main()

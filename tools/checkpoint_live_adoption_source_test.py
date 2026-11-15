"""Actual handoff source/caller controls; no ACL2/runtime qualification."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import checkpoint_live_adoption_wire_rewrite as wire
import checkpoint_live_consume_rewrite as consume
import checkpoint_summary_install_source_rewrite as install
R=Path(__file__).resolve().parents[1];B=R/'books';F=R/'tools/fixtures'
def one(s,p):return lr.match(p,lr.parse(s).forms)[0].node
def op(s,name):return one(s,f'(fn2-live-adoption-operation fn2-checkpoint-live-adoption-{name} ?*body)')
def req(n,p):
 if not lr.match(p,[n]):raise ValueError(p)
def guards(source):
 n=op(source,'open')
 for p in ['(fn2-live-adoption-source)','(fn2-c-source-writer-ownerp writer-token ?*args)','(= (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-exclusive*)','(= (fn2-c-source-control-readers 0 fn2-c-source-control) 0)','(= (fn2-checkpoint-summary-lease-count 0 fn2-checkpoint-summary) 0)','(= (fn2-checkpoint-summary-lease-count 1 fn2-checkpoint-summary) 0)']:req(n,p)
 sourcep=one(source,'(fn2-live-adoption-predicate fn2-live-adoption-source-p ?*body)')
 for p in ['(fn2-checkpoint-summary-authority-row-complete-p 1 ?*args)','(fn2-checkpoint-cbase-row-held-p s fn2-checkpoint-summary fn2-checkpoint-cbase-holds)','(fn2-live-adoption-descriptor-p 0 s ?*args)','(fn2-live-adoption-exclusive-p fn2-checkpoint-live-adoption fn2-c-source-control)']:req(sourcep,p)
def graph(source):
 n=one(source,'(defmachine-arms fn2-checkpoint-master ?*body)')
 arms=wire.value(n,':arms')
 return {a.items[0].low:{m.node.items[1].low for m in lr.match('(:next ?phase)',[a])} for a in arms.items}
def reaches(g,start,end,removed=None):
 todo=[start];seen=set()
 while todo:
  n=todo.pop()
  if n==removed or n in seen:continue
  if n==end:return True
  seen.add(n);todo.extend(g.get(n,()))
 return False
class Handoff(unittest.TestCase):
 def setUp(self):self.s=(B/'checkpoint-live-adoption.lisp').read_text()
 def test_actual_master_fixed_source_wire(self):
  a,b=wire.rewrite((F/'checkpoint-live-wire-state-before.lisp').read_text(),(F/'checkpoint-live-wire-arms-before.lisp').read_text())
  self.assertEqual(a,(B/'checkpoint-master-state.lisp').read_text());self.assertEqual(b,(B/'checkpoint-master-arms.lisp').read_text())
 def test_every_success_path_has_real_handoff(self):
  g=graph((B/'checkpoint-master-arms.lisp').read_text());start=':publish-wait';end=':snapshot-release'
  self.assertTrue(reaches(g,start,end))
  for phase in [':summary-authority-copy',':live-catalog-close',':live-hold',':rebase-archive',':live-preflight',':live-writer-begin',':live-open',':live-install',':live-versions',':live-retire-runs',':live-retire-overlays',':live-swap',':rebase-consume',':live-release-old',':release-complete',':thaw',':event-rearm',':rearm']:
   self.assertFalse(reaches(g,start,end,phase),phase)
 def test_actual_owner_publication_hold_and_exclusion(self):guards(self.s)
 def test_missing_writer_or_actual_hold_gate_refused(self):
  for old in ['(= (fn2-c-source-control-readers 0 fn2-c-source-control) 0)','(fn2-checkpoint-cbase-row-held-p s fn2-checkpoint-summary fn2-checkpoint-cbase-holds)']:
   self.assertIn(old,self.s)
   with self.assertRaises(ValueError):guards(self.s.replace(old,'t'))
 def test_generation_capacity_checked_before_writer_or_old_sources(self):
  n=op(self.s,'preflight')
  for p in ['(unsigned-byte-p 60 next)','(<= (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary) (fn2-checkpoint-live-adoption-free 0 fn2-checkpoint-live-adoption))','(fn2-run-installed-run r fn2-run-installed)','(fn2-overlays-seq o fn2-overlays)']:req(n,p)
  for p in ['(fn2-run-retire ?*args)','(fn2-seal-release-row ?*args)','(fn2-c-source-writer-begin-raw ?*args)']:self.assertFalse(lr.match(p,[n]))
 def test_same_shared_cold_and_live_installer(self):
  before=(F/'checkpoint-summary-install-source-before.lisp').read_text();a,b=install.extract(before)
  self.assertEqual(a,(B/'checkpoint-summary-apply.lisp').read_text());self.assertEqual(b,(B/'checkpoint-summary-install-source.lisp').read_text())
  req(op(self.s,'install'),'(fn2-checkpoint-summary-install-source 1 e r fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-run-installed)')
 def test_every_free_after_versions_and_full_new_source_install(self):
  n=op(self.s,'versions')
  req(n,'(= (fn2-checkpoint-summary-installed 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary))')
  req(n,'(fn2-run-version-floor-advance next fn2-run-installed)')
  req(n,'(fn2-id-engine-set-seq 0 next fn2-id-engine)');req(n,'(fn2-seals-set-runs 0 next fn2-seals)')
  for name in ['retire-runs','retire-overlays']:
   req(op(self.s,name),'(= (fn2-run-installed-version-floor fn2-run-installed) (fn2-checkpoint-live-adoption-version 0 fn2-checkpoint-live-adoption))')
  self.assertNotIn('fn2-id-engine-set-published',self.s)
 def test_old_retirement_uses_actual_shared_owner_primitives(self):
  req(op(self.s,'retire-runs'),'(fn2-seal-release-row r fn2-run-installed fn2-run-cache fn2-pool)')
  req(op(self.s,'retire-runs'),'(fn2-checkpoint-summary-row-retire-row 0 r ?*args)')
  req(op(self.s,'retire-overlays'),'(fn2-seal-retire o fn2-overlays fn2-pool)')
  self.assertFalse(lr.match('(fn2-pool-release ?*args)',lr.parse(self.s).forms))
 def test_swap_is_exact_terminal_with_no_held_restoration(self):
  n=op(self.s,'swap')
  for p in ['(fn2-checkpoint-summary-swap-rows 0 1 fn2-checkpoint-summary)','(fn2-live-adoption-swap-descriptors 0 fn2-checkpoint-summary)','(fn2-csnapshot-set-phase 0 *fn2-csnapshot-phase-adopted* fn2-csnapshot)','(= (fn2-checkpoint-summary-installed 0 fn2-checkpoint-summary) 0)']:req(n,p)
  self.assertFalse(lr.match('(fn2-csnapshot-set-phase 0 *fn2-csnapshot-phase-held* ?x)',lr.parse(self.s).forms))
 def test_real_consumed_join_before_old_promise_drop(self):
  n=one(self.s,'(fn2-live-adoption-predicate fn2-checkpoint-live-adoption-consumed-p ?*body)')
  for p in ['(fn2-checkpoint-summary-authority-row-complete-p 0 ?*args)','(= (fn2-checkpoint-summary-authority-phase 1 fn2-checkpoint-summary-authority) *fn2-checkpoint-summary-authority-phase-idle*)','(= (fn2-commit-root-base-batch 0 fn2-commit-root) (fn2-checkpoint-live-adoption-cut-commit 0 fn2-checkpoint-live-adoption))']:req(n,p)
  req(op(self.s,'release-old'),'(fn2-live-adoption-consumed)');req(op(self.s,'release-old'),'(fn2-checkpoint-cbase-row-release-step budget 1 ?*args)')
 def test_consume_actual_readonly_operand_class(self):
  actual=(B/'checkpoint-directory-consume.lisp').read_text()
  self.assertEqual(actual,consume.rewrite((F/'checkpoint-live-consume-before.lisp').read_text(),self.s))
  n=one(actual,'(defun fn2-directory-rebase-consume ?*body)')
  req(n,'(= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-adopted*)');req(n,'(fn2-checkpoint-live-adoption-adopted-p ?*args)')
 def test_only_complete_real_terminal_opens_writer(self):
  calls=lr.match('(fn2-c-source-writer-end-raw ?*args)',lr.parse(self.s).forms);self.assertEqual(len(calls),1)
  n=op(self.s,'finish');req(n,'(fn2-live-adoption-consumed)');req(n,'(= (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-idle*)')
  req(n,'(= (fn2-checkpoint-live-adoption-phase 0 fn2-checkpoint-live-adoption) *fn2-checkpoint-live-adoption-phase-old-released*)')
  req(n,'(fn2-alloc-snapshot-release token kind owner generation fn2-extents)')
 def test_no_cold_fresh_idle_gate_or_free_activation(self):
  self.assertNotIn('fn2-run-load-readiness-complete-current-p',self.s)
  self.assertIn('fn2-run-load-geometry-current-p',self.s)
  for p in ['(fn2-alloc-release ?*args)','(fn2-alloc-retire ?*args)']:self.assertFalse(lr.match(p,lr.parse(self.s).forms))
  self.assertIn('(defconst *fn2-checkpoint-activation-qualified* nil)',(B/'checkpoint-master-state.lisp').read_text())
 def test_late_rearm_materialization_and_constant_phase(self):
  names=[x.items[0].low for x in lr.parse(B/'assembly-callbacks-c.lisp').forms if hasattr(x,'items') and x.items and hasattr(x.items[0],'low')]
  order=['fn2-event-producer-rearm-events','fn2-checkpoint-live-adoption-rearm-events','fn2-checkpoint-master-events'];self.assertEqual([x for x in names if x in order],order)
  s=(B/'checkpoint-live-adoption-rearm.lisp').read_text();self.assertIn('(fn2-live-adoption-consumed)',s)
  for name in ['fn2-checkpoint-master-release-complete-children-at-phase','fn2-event-producer-rearm-at-phase','fn2-checkpoint-master-rearm-children-at-phase']:
   self.assertTrue(lr.match(f'({name} *fn2-csnapshot-phase-adopted* ?*args)',lr.parse(s).forms))
if __name__=='__main__':unittest.main()

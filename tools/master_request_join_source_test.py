"""Source-only actual MASTER join controls; no macroexecution/runtime claim."""
from pathlib import Path
import hashlib,json,subprocess,unittest
import lisp_rewrite as lr
import master_request_join_rewrite as port
ROOT=Path(__file__).resolve().parents[1]
def raw(s,pat):n=port.one(s,pat);return s[n.start:n.end]
def require(book,s):port.validate(book,s)
class MasterJoin(unittest.TestCase):
 def test_actual_sources_are_named_projections(self):
  for b in port.EXPECTED:require(b,(ROOT/'books'/(b+'.lisp')).read_text())
 def test_all_original_pressure_common_gates_preserved(self):
  before=raw(port.CONTROL,'(defun fn2-checkpoint-master-pressure-children ?*body)')
  after=port.EXPECTED['checkpoint-master-pressure']
  a=port.one(before,'(and (equal (fn2-boot-config-checkpoint-layout-ready ?*args) 1) ?*body)')
  old=[lr.emit(n,drop_comments=True) for n in a.items[1:]]
  n=port.one(after,'(and (equal (fn2-boot-config-checkpoint-layout-ready ?*args) 1) ?*body)')
  new=[lr.emit(x,drop_comments=True) for x in n.items[1:]]
  debt=['(< 0 (fn2-alloc-blocked fn2-extents))','(< seen (fn2-alloc-last-retirement fn2-extents))']
  self.assertEqual([x for x in old if x not in debt],[x for x in new if not x.startswith('(or ')])
  requested=[x for x in new if x.startswith('(or ')];self.assertEqual(len(requested),1)
  for x in debt:self.assertIn(x,requested[0])
  self.assertTrue(requested[0].endswith('requested)'))
 def test_pressure_only_from_actual_pending_in_both_consumers(self):
  arms=port.EXPECTED['checkpoint-master-arms'];events=port.EXPECTED['checkpoint-master-events']
  idle=raw(arms,'(:idle :on-refusal ?*body)')
  self.assertLess(idle.index('fn2-sealer-checkpoint-pending-op'),idle.index('fn2-checkpoint-master-pressure-op'))
  self.assertIn('row-retirement-seen (if requested t nil)',idle)
  self.assertIn('(if (mv-nth 1 (fn2-sealer-checkpoint-pending-op fn2-core)) t nil)',events)
 def test_bounded_inventory_route_holds_actual_working_bundle(self):
  s=port.EXPECTED['checkpoint-master-arms'];source=raw(s,'(:root1-source :on-refusal ?*body)')
  self.assertIn('((:inventory) (:next :root1-inventory)',source)
  inv=raw(s,'(:root1-inventory :on-refusal ?*body)')
  self.assertIn('fn2-checkpoint-root1-inventory-op *fn2-checkpoint-master-pure-byte-quantum*',inv)
  self.assertNotIn('fn2-checkpoint-root1-inventory-op budget',inv)
  self.assertIn('((:more) (:next :root1-source)',inv)
  self.assertIn('(:root1-inventory :storage-window :storage-window)',port.EXPECTED['checkpoint-master-state'])
 def test_wake_only_after_real_reopen_release_and_cut_release(self):
  s=port.EXPECTED['checkpoint-master-arms']
  reopened=raw(s,'(:live-reopen :on-refusal ?*body)')
  self.assertIn('fn2-checkpoint-live-replace-reopen-op',reopened)
  self.assertIn('((:applied) (:next :release)',reopened)
  snapshot=raw(s,'(:snapshot-release :on-refusal ?*body)')
  self.assertLess(snapshot.index('fn2-csnapshot-release'),snapshot.index('(:next :sealer-resume-wake)'))
  wake=raw(s,'(:sealer-resume-wake :on-refusal ?*body)')
  self.assertIn('fn2-sealer-checkpoint-wake-target',wake)
  self.assertIn('(not (= target *fn2-none*))',wake)
  self.assertIn('(:wake-row target)',wake)
  self.assertIn('(:next :teardown-transfer-begin)',wake)
  before=port.bank.project_arms(port.BEFORE['checkpoint-master-arms'])
  for phase in ('live-promote','live-reopen','rearm','release','thaw'):
   self.assertEqual(raw(s,'(:'+phase+' :on-refusal ?*body)'),raw(before,'(:'+phase+' :on-refusal ?*body)'))
 def test_late_canonical_materialization_preserves_existing_cns(self):
  s=port.EXPECTED['assembly-callbacks-e-cns'];before=(port.FIX/'late-current-before.lisp').read_text()
  self.assertIn('(fn2-checkpoint-master-events)',s)
  self.assertIn('fn2-run-loader-core-face-events',s)
  self.assertIn('fn2-checkpoint-bank-admission-begin-op',s)
  self.assertTrue(s.endswith('(fn2-auth-read-events)\n(fn2-cns-events)\n'))
  for f in lr.parse(before).forms:self.assertIn(before[f.start:f.end],s)
 def test_lower_pressure_has_one_implementation(self):
  control=port.EXPECTED['checkpoint-master-control'];leaf=port.EXPECTED['checkpoint-master-pressure']
  self.assertNotIn('(defun fn2-checkpoint-master-pressure-children',control)
  self.assertIn('(include-book "checkpoint-master-pressure")',control)
  for f in lr.match('(defun ?name ?*body)',lr.parse(port.CONTROL).forms,deep=True):
   n=f.node;name=lr.emit(n.items[1],drop_comments=True)
   if name!='fn2-checkpoint-master-pressure-children':self.assertIn(port.CONTROL[n.start:n.end],control)
  self.assertEqual(leaf.count('(defun fn2-checkpoint-master-pressure-children'),1)
 def test_nil_activation_and_actual_binary_max(self):
  s=port.EXPECTED['checkpoint-master-state']
  self.assertIn('(defconst *fn2-checkpoint-activation-qualified* nil)',s)
  for m in lr.match('(max ?*args)',lr.parse(s).forms,deep=True):self.assertEqual(len(m.node.items),3)
 def test_canonical_coordinators_untouched(self):
  files=json.loads((port.FIX/'canonical-source-hashes.json').read_text())
  for p,want in files.items():self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(),want,p)
 def test_negative_resource_bypass_inventory_skip_earlywake_refused(self):
  for book,a,b in [('checkpoint-master-pressure','(fn2-checkpoint-admission-roomp 0 fn2-pool)','requested'),
                  ('checkpoint-master-pressure','(fn2-checkpoint-directory-roomp fn2-extents fn2-commit-root)','t'),
                  ('checkpoint-master-pressure','(equal (fn2-alloc-freeze-token fn2-extents) 0)','t'),
                  ('checkpoint-master-arms','((:inventory) (:next :root1-inventory)','((:inventory) (:next :events-begin)'),
                  ('checkpoint-master-arms','fn2-sealer-checkpoint-wake-target','fn2-sealer-checkpoint-pending-op')]:
   self.assertIn(a,port.EXPECTED[book])
   with self.assertRaises(ValueError):require(book,port.EXPECTED[book].replace(a,b,1))
 def test_prepared_fixture_uses_actual_transport_and_explicit_test_entry(self):
  s=(ROOT/'tests/checkpoint-master-sealer-request-unit.lisp').read_text()
  for call in ('fn2-cln-register-append','fn2-msrq-requested-drive','fn2-sealer-checkpoint-resume',
               'fn2-sealer-checkpoint-wake-target','fn2-ccp-maintenance-entry','fn2-sad-adopt','fn2-msrq-returned-drive'):
   self.assertIn('('+call,s)
  self.assertNotIn('fn2-checkpoint-summary-put',s)
  self.assertNotIn('fn2-checkpoint-predecessor-control-put',s)
  self.assertIn('Activation remains NIL',s)
if __name__=='__main__':unittest.main()

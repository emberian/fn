"""Configured R+2E constructor/source controls. No ACL2/runtime execution."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from replacement_bank_c_rewrite import DATA,project,event

def body(text,name):
 n=event(text,'defun',name);return text[n.items[-1].start:n.items[-1].end]
class ReplacementBank(unittest.TestCase):
 def test_projection_and_idempotence(self):
  for b in ('runs','machines-c','sealer'):
   actual=(ROOT/'books'/(b+'.lisp')).read_text()
   self.assertEqual(project(b,DATA['before'][b]),actual)
   self.assertEqual(project(b,actual),actual)
 def test_no_wfp_scan_or_inferred_resident_region(self):
  t=(ROOT/'books/runs.lisp').read_text();p=body(t,'fn2-run-installed-bank-geometry-p')
  self.assertNotIn('wfp',p);self.assertNotIn('from',p)
  self.assertIn('bank-configured',p);self.assertIn('resident-limit',p);self.assertIn('(fn2-run-installed-row-count ',p)
  init=body(t,'fn2-run-installed-init-configured')
  self.assertIn('(fn2-run-installed-init (fn2-run-installed-row-count resident capacity)',init)
  for f in ('resident-limit','bank-capacity','bank-configured'):self.assertIn('update-fn2-run-installed-'+f,init)
 def test_constructor_regions_and_guard_hints_preserved(self):
  t=(ROOT/'books/runs.lisp').read_text()
  for n in ('fn2-run-install','fn2-run-install-filter','fn2-run-install-units','fn2-run-retired-next'):
   self.assertIn('(< r (fn2-run-installed-resident-limit fn2-run-installed))',body(t,n))
  for n in ('fn2-run-install-physical','fn2-run-free-physical'):
   for b in (0,1):self.assertIn('(fn2-run-installed-bank-row-p '+str(b)+' r fn2-run-installed)',body(t,n))
  for b in ('runs','sealer'):
   t=(ROOT/'books'/(b+'.lisp')).read_text();old=DATA['before'][b]
   for f in lr.parse(old).forms:
    if isinstance(f,lr.Lst) and len(f.items)>4 and getattr(f.items[0],'low','')=='defun':
     n=event(t,'defun',f.items[1].low)
     self.assertEqual(old[f.items[3].start:f.items[3].end],t[n.items[3].start:n.items[3].end])
 def test_resident_sealer_never_counts_or_allocates_bank_free_cells(self):
  t=(ROOT/'books/sealer.lisp').read_text()
  for n in ('fn2-seal-free-row','fn2-seal-free-rows','fn2-seal-retired-row'):
   s=body(t,n);self.assertIn('resident-limit',s);self.assertIn('(< r (fn2-run-installed-rows',s)
  self.assertIn('(rows (fn2-run-installed-resident-limit',body(t,'fn2-seal-install-run'))
 def test_actual_profile_initializes_two_banks(self):
  t=(ROOT/'books/machines-c.lisp').read_text()
  self.assertIn('(fn2-run-installed-init-configured (fn2-b-capacity :identity-runs 64 profile) (fn2-b-capacity :extent-slots 16 profile)',t)
  self.assertIn('(fn2-run-installed-row-count (fn2-b-capacity :identity-runs 64 profile) (fn2-b-capacity :extent-slots 16 profile))',t)
 def test_cold_named_projection_is_bank_zero_only(self):
  s=project('checkpoint-summary-apply',DATA['cold-source'])
  self.assertIn('(fn2-run-installed-bank-start 0 fn2-run-installed)',s)
  self.assertIn('(= (fn2-checkpoint-summary-bank 0 fn2-checkpoint-summary) 0)',s)
  self.assertIn('(fn2-run-installed-bank-capacity fn2-run-installed)',s)
  self.assertEqual(project('checkpoint-summary-apply',s),s)
 def test_shared_row_count_stage_preserves_frozen_bank_inputs(self):
  from replacement_bank_c_rewrite import _project_banks,project_row_count
  for b in ('runs','machines-c'):
   self.assertEqual(project(b,DATA['before'][b]),project_row_count(b,_project_banks(b,DATA['before'][b])))
  t=(ROOT/'books/run-installed-geometry.lisp').read_text()
  self.assertIn('(fn2-book-layer :b)',t)
  self.assertEqual(body(t,'fn2-run-installed-row-count'),'(+ resident (* 2 capacity))')
  t=(ROOT/'books/run-geometry.lisp').read_text()
  self.assertEqual(project('run-geometry',DATA['row-helper-stage-before']['run-geometry']),t)
  self.assertEqual(project('run-geometry',t),t)
 def test_bare_initializer_census(self):
  calls=[]
  for directory in ('books','tests'):
   for p in (ROOT/directory).glob('*.lisp'):
    text=p.read_text()
    if 'fn2-run-installed-init ' not in text:continue
    for m in lr.match('(fn2-run-installed-init ?*args)',lr.parse(text).forms,deep=True):calls.append(p.relative_to(ROOT).as_posix())
  self.assertEqual(sorted(calls),['books/runs.lisp','tests/replacement-bank-constructor-unit.lisp'])
  for b,where in (('range','books'),('sealer-unit','tests')):
   text=(ROOT/where/(b+'.lisp')).read_text()
   self.assertEqual(project(b,DATA['before'][b]),text)
   self.assertEqual(project(b,text),text)
 def test_prepared_constructor_control_uses_real_methods(self):
  t=(ROOT/'tests/replacement-bank-constructor-unit.lisp').read_text()
  for method in ('fn2-run-installed-init-configured','fn2-run-install','fn2-run-install-physical','fn2-seal-free-rows','fn2-seal-free-row'):
   self.assertIn('('+method+' ',t)
  self.assertIn('(eq blocked :state)',t);self.assertIn('(equal free 0)',t)
  self.assertNotIn('set-state',t);self.assertNotIn('update-fn2-run-installed-',t)
  runs=(ROOT/'books/runs.lisp').read_text()
  for name in ('fn2-run-install','fn2-run-install-physical','fn2-run-installed-init-configured'):
   argc=len(event(runs,'defun',name).items[2].items)
   for m in lr.match('('+name+' ?*args)',lr.parse(t).forms,deep=True):self.assertEqual(len(m.captures['args']),argc)
if __name__=='__main__':unittest.main()

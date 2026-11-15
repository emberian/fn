"""Verbatim scan extraction and current cold-source preservation controls."""
from pathlib import Path
import re,unittest
import lisp_rewrite as lr
import readiness_slice_rewrite as rw
import boot_geometry_lower_rewrite as boot
import commit_root_lower_rewrite as lower
import release_core_rewrite as release
ROOT=Path(__file__).resolve().parents[1];B=ROOT/'books';F=ROOT/'tools/fixtures'
def canon(n):return n.low if hasattr(n,'low') else tuple(canon(x) for x in n.items)
def same(a,b):return canon(lr.parse(a).forms[0])==canon(lr.parse(b).forms[0])
class Slice(unittest.TestCase):
 def test_current_b_and_c_replay(self):
  for name,fn in [('machines-b.lisp',rw.machines_b),('machines-c.lisp',rw.machines_c)]:
   expected=fn((F/('readiness-slice-before-'+name)).read_text(),(F/('readiness-slice-provider-'+name)).read_text())
   if name=='machines-b.lisp':
    expected=lower.transform(expected,(F/'readiness-slice-before-commit-directory.lisp').read_text())[0]
    # Subsequent physical-anchor protection reserves a disjoint region using
    # the same declared physical-anchor count; old geometry remains exact.
    expected=expected.replace('(include-book "checkpoint-cbase-state")', '(include-book "checkpoint-cbase-state")\n(include-book "checkpoint-geometry")')
    expected=expected.replace('    (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile)) (fn2-b-checkpoint-capacity profile))))', '    (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile)) (fn2-b-checkpoint-capacity profile))\n    ; Four independent physical anchors cannot alias canonical source holds.\n    (* *fn2-checkpoint-anchor-slots* (nfix (fn2-b-capacity :extent-slots 16 profile)))))')
    expected=expected.replace('(rc-frontier-first :u60) (rc-frontier-last :u60) (rc-frontier-started :bool)', '(rc-frontier-first :u60) (rc-frontier-last :u60) (rc-frontier-started :bool)\n          (rc-own-token :u32) (rc-own-left :u32)')
    expected=release.transform(expected,(F/'release-core-registration.lisp').read_text())
   self.assertEqual((B/name).read_text(),expected)
 def test_same_actual_scan_provider_forms(self):
  for name in ['run-physical-state.lisp','run-physical-resources.lisp','run-physical-geometry.lisp','run-physical-readiness.lisp']:
   provider=(F/('readiness-slice-provider-'+name)).read_text()
   # Shared lower state imports runs directly, as exact later ea0 lowering;
   # every declaration, guard and decision body remains the original form.
   if name=='run-physical-state.lisp':provider=provider.replace('(include-book "checkpoint-summary-leases")','(include-book "runs")')
   self.assertEqual((B/name).read_text(),provider)
 def test_same_cursor_declaration(self):
  p='(defcolumns fn2-run-cursors ?*body)'
  self.assertTrue(same(rw.form((B/'runs.lisp').read_text(),p),rw.form((F/'readiness-slice-provider-runs.lisp').read_text(),p)))
 def test_geometry_move_preserves_current_boot_fields_and_phases(self):
  for old,new,fn in [('boot-kind.lisp','boot-config-state.lisp',boot.kind),('checkpoint-boot.lisp','boot-geometry-state.lisp',boot.geometry)]:
   rewritten,lower=fn((F/('readiness-slice-before-'+old)).read_text())
   # The consumer subsequently appends exactly two scan states; the lower
   # extraction must still preserve every preexisting field/state/hold/arm.
   if old=='boot-kind.lisp':
    rewritten=rewritten.replace(':genesis-begin :genesis-step)', ':genesis-begin :genesis-step :checkpoint-loader-begin :checkpoint-loader-step :checkpoint-bank-protect)')
    rewritten=rewritten.replace('         (:checkpoint-cbase-acquire :storage-window)', '         (:checkpoint-cbase-acquire :storage-window)\n         (:checkpoint-loader-begin :storage-window)\n         (:checkpoint-loader-step :storage-window)')
    rewritten=rewritten.replace('         (:checkpoint-cbase-acquire)\n', '         (:checkpoint-cbase-acquire)\n         (:checkpoint-loader-begin)\n         (:checkpoint-loader-step)\n')
    rewritten=rewritten.replace('         (:checkpoint-bank-bind :storage-window)', '         (:checkpoint-bank-bind :storage-window)\n         (:checkpoint-bank-protect :storage-window)')
    rewritten=rewritten.replace('(:checkpoint-directory-install) (:checkpoint-bank-bind)', '(:checkpoint-directory-install) (:checkpoint-bank-bind) (:checkpoint-bank-protect)')
   self.assertEqual((B/old).read_text(),rewritten);self.assertEqual((B/new).read_text(),lower)
 def test_harvest_same_actual_observer_no_issuer(self):
  exports=(F/'readiness-slice-provider-harvest.lisp').read_text();s=(B/'run-physical-harvest.lisp').read_text()
  for f in lr.parse(exports).forms:self.assertIn(exports[f.start:f.end],s)
  self.assertNotIn('fn2-block-read-children',s)
 def test_source_include_closure_is_acyclic_and_has_no_engine(self):
  visited=set();active=[]
  def visit(n):
   self.assertNotIn(n,active,'cycle '+str(active+[n]))
   if n in visited:return
   p=B/(n+'.lisp');self.assertTrue(p.exists(),n);active.append(n)
   for x in re.findall(r'\(include-book "([^"/]+)"\)',p.read_text()):visit(x)
   active.pop();visited.add(n)
  visit('checkpoint-summary-loader-readiness')
  self.assertNotIn('run-physical-io',visited);self.assertNotIn('run-physical-bound-step',visited)
 def test_no_archive_cursor_in_canonical_profile_count(self):
  s=(B/'machines-b.lisp').read_text();f=rw.form(s,'(defun fn2-b-run-cursor-rows ?*body)')
  self.assertNotIn('archive',f)
  self.assertIn('*fn2-b-seal-source-cursors* 1',f)
  scan=(B/'run-physical-readiness.lisp').read_text()
  self.assertTrue(lr.match('(equal (fn2-run-load-geometry-cursors 0 fn2-run-load-geometry) (+ (fn2-id-decides-rows fn2-id-decides) (* (+ 1 *fn2-b-range-source-cursors*) (fn2-reads-rows fn2-reads)) *fn2-b-seal-source-cursors* 1))',lr.parse(scan).forms))
 def test_actual_refusal_and_serial_boundaries(self):
  s=(B/'run-physical-readiness.lisp').read_text()
  self.assertIn('(mv :row fn2-run-load-readiness)',s);self.assertIn('*fn2-run-load-readiness-phase-refused*',s)
  self.assertIn('(equal (fn2-run-load-readiness-admissions 0 fn2-run-load-readiness) (fn2-run-loads-admissions fn2-run-loads))',s)
  resource=(B/'run-physical-resources.lisp').read_text()
  self.assertLess(resource.index('(fn2-run-load-admission-begin fn2-run-loads)'),resource.index('(fn2-pool-reserve pc'))
if __name__=='__main__':unittest.main()

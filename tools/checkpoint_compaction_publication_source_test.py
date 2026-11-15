"""Exact carrier migration controls; source shape, not ACL2 qualification."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
from checkpoint_compaction_manifest_port import project as manifest_port, BEFORE
from checkpoint_compaction_live_port import project_all, FIXTURES, NAMES
from checkpoint_live_retire_emit import emit
from lisp_source import forms, read_sexp
ROOT=Path(__file__).resolve().parents[1]

def defs(text):
 return {lr.emit(m.node.items[1],drop_comments=True):text[m.start:m.end]
         for m in lr.match('(defun ?name ?*body)',lr.parse(text).forms,deep=True)}

def expected_live():return project_all({n:(FIXTURES/(n+'.lisp')).read_text() for n in NAMES})
def require_live(candidate):
 if candidate!=expected_live():raise ValueError('changed outside exact live carrier migration')
def require_manifest(candidate):
 if candidate!=manifest_port(BEFORE.read_text()):raise ValueError('changed outside exact manifest carrier migration')

class PublicationPort(unittest.TestCase):
 def test_actual_manifest_is_exact_declared_transformation(self):
  require_manifest((ROOT/'books/checkpoint-metadata-manifest.lisp').read_text())
 def test_unchanged_physical_codec_and_page_algorithms(self):
  before=defs(BEFORE.read_text());after=defs((ROOT/'books/checkpoint-metadata-manifest.lisp').read_text())
  for suffix in ('ownerp','hash','page','root-hash'):
   name='fn2-checkpoint-metadata-manifest-'+suffix
   self.assertEqual(before[name],after[name])
  actual=(ROOT/'books/checkpoint-metadata-manifest.lisp').read_text()
  for clause in ('fn2-checkpoint-metadata-page-complete-p','fn2-checkpoint-page-completed-extent-p','fn2-checkpoint-source-claim'):
   self.assertEqual([lr.emit(m.node,drop_comments=True) for m in lr.match('('+clause+' ?*args)',lr.parse(BEFORE.read_text()).forms,deep=True)],
                    [lr.emit(m.node,drop_comments=True) for m in lr.match('('+clause+' ?*args)',lr.parse(actual).forms,deep=True)])
 def test_no_nominal_original_identity_is_captured_as_merged_origin(self):
  actual=(ROOT/'books/checkpoint-metadata-manifest.lisp').read_text()
  body=defs(actual)['fn2-checkpoint-metadata-manifest-emit']
  self.assertIn('(catalog-source-kind 2)',body)
  self.assertNotIn('fn2-checkpoint-metadata-old-',body)
  self.assertNotIn('fn2-checkpoint-source-selectedp',body)
  self.assertIn('fn2-checkpoint-compaction-schema-drained-p',body)
  self.assertIn('fn2-checkpoint-predecessor-ready-p',body)
 def test_actual_live_family_is_exact_readonly_carrier_port(self):
  require_live({n:(ROOT/'books'/str(n+'.lisp')).read_text() for n in NAMES})
 def test_existing_retire_generator_is_the_only_retirement_recipe(self):
  self.assertEqual(emit((FIXTURES/'checkpoint-live-install.lisp').read_text()),(FIXTURES/'checkpoint-live-retire.lisp').read_text())
  self.assertEqual(emit((ROOT/'books/checkpoint-live-install.lisp').read_text()),(ROOT/'books/checkpoint-live-retire.lisp').read_text())
 def test_other_post_fence_and_identity_gates_are_preserved(self):
  after=(ROOT/'books/checkpoint-summary-authority-live.lisp').read_text()
  before=(FIXTURES/'checkpoint-summary-authority-live.lisp').read_text()
  for head in ('fn2-checkpoint-summary-live-published-hash-p','fn2-event-producer-donep','fn2-checkpoint-production-roots-p',
               'fn2-checkpoint-lifecycle-ownerp','fn2-event-producer-writer-request-p'):
   def count(s):return len(lr.match('('+head+' ?*args)',lr.parse(s).forms,deep=True))
   self.assertEqual(count(after),count(before),head)
   self.assertGreater(count(after),0)
  self.assertIn('*fn2-checkpoint-state-installed*',after)
  self.assertIn('*fn2-checkpoint-publication-phase-complete*',after)
  self.assertIn('fn2-checkpoint-compaction-produced-p',after)
  self.assertNotIn('fn2-checkpoint-source-rank',after)
 def test_negative_manifest_guard_hash_and_reference_changes_refused(self):
  actual=(ROOT/'books/checkpoint-metadata-manifest.lisp').read_text()
  for a,b in [('fn2-checkpoint-predecessor-complete-p','fn2-checkpoint-predecessor-bound-p'),
              ('fn2-checkpoint-page-completed-extent-p','fn2-checkpoint-source-overlayp'),
              ('(catalog-source-kind 2)','(catalog-source-kind 0)'),
              ('(root-source-complete 1)','(root-source-complete 0)')]:
   self.assertIn(a,actual)
   with self.assertRaises(ValueError):require_manifest(actual.replace(a,b,1))
 def test_negative_live_gate_removal_and_extra_namespace_changes_refused(self):
  actual={n:(ROOT/'books'/str(n+'.lisp')).read_text() for n in NAMES}
  name='checkpoint-summary-authority-live'
  for a,b in [('fn2-checkpoint-compaction-produced-p','fn2-checkpoint-compaction-cut-ownerp'),
              ('fn2-checkpoint-summary-live-published-hash-p','fn2-checkpoint-source-overlayp'),
              ('*fn2-checkpoint-state-installed*','*fn2-checkpoint-state-free*')]:
   self.assertIn(a,actual[name]);bad=dict(actual);bad[name]=bad[name].replace(a,b,1)
   with self.assertRaises(ValueError):require_live(bad)
 def test_carried_completed_count_does_not_revalidate_freed_original_rows(self):
  s=(ROOT/'books/checkpoint-compaction-production.lisp').read_text()
  self.assertIn('fn2-checkpoint-predecessor-control-completed-originals',s)
  for phase in ('complete','mapping','retiring','done'):
   self.assertIn('*fn2-checkpoint-predecessor-phase-'+phase+'*',s)
  self.assertIn('fn2-checkpoint-compaction-cut-ownerp',s)
  self.assertNotIn('fn2-checkpoint-compaction-ownerp ',s)
  self.assertNotIn('fn2-checkpoint-predecessor-identity-p',s)
  self.assertNotIn('fn2-checkpoint-predecessor-ready-p',s)
  self.assertNotIn('fn2-checkpoint-source-runp',s)

if __name__=='__main__':unittest.main()

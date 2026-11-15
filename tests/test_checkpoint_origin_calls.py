"""Actual source-call controls; these do not qualify ACL2 guards or execution."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import lisp_source as ls
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
APIS={
 'fn2-checkpoint-build-begin','fn2-checkpoint-map-build-begin','fn2-checkpoint-descriptor-pack-page',
 'fn2-checkpoint-metadata-overlay-begin','fn2-checkpoint-metadata-run-begin',
 'fn2-checkpoint-recovery-census-bound-p','fn2-checkpoint-recovery-census-step',
 'fn2-checkpoint-recovery-evidence-physical','fn2-checkpoint-recovery-evidence-record',
 'fn2-boot-scan-checkpoint-pool-inner',
 'fn2-boot-scan-checkpoint-pool','fn2-event-read-open','fn2-event-producer-auth-step',
 'fn2-event-producer-step','fn2-rec-context','fn2-rec-header-check','fn2-rec-seal-check',
}

def nodes(tree):
 if isinstance(tree,list):
  yield tree
  for child in tree:yield from nodes(child)

def trees(text):
 return [ls.read_sexp(form) for form in ls.forms(text)]

def inventory():
 result={}
 for directory in ('books','tests'):
  for path in (ROOT/directory).glob('*.lisp'):
   text=path.read_text()
   if any(name in text for name in APIS):result[str(path.relative_to(ROOT))]=text
 return result

def arity_errors(sources):
 defs={}
 for text in sources.values():
  for tree in trees(text):
   for node in nodes(tree):
    if len(node)>2 and node[0]=='defun' and isinstance(node[1],str) and node[1] in APIS:
     defs[node[1]]=len(node[2])
 errors=[];count=0
 for path,text in sources.items():
  for tree in trees(text):
   for node in nodes(tree):
    if node and isinstance(node[0],str) and node[0] in APIS:
     count+=1
     if len(node)-1!=defs[node[0]]:errors.append((path,node[0],len(node)-1,defs[node[0]]))
 return errors,count

class CheckpointOriginCalls(unittest.TestCase):
 def test_actual_source_call_class_matches_actual_definitions(self):
  errors,count=arity_errors(inventory())
  self.assertGreater(count,20)
  self.assertEqual(errors,[])
 def test_old_recovery_context_arity_is_detected(self):
  sources=inventory();path='books/checkpoint-recovery-evidence.lisp';text=sources[path]
  match=lr.match('(?*xs)',lr.parse(text).forms,head='fn2-rec-context')[0]
  arg=match.node.items[10]
  sources[path]=lr.write(text,[(arg.start,arg.end,'')])
  errors,_=arity_errors(sources)
  self.assertTrue(any(name=='fn2-rec-context' for _,name,_,_ in errors))
 def test_actual_recovery_context_pair_uses_the_physical_carrier(self):
  for file,stem in [('event-read-verify','fn2-event-read')]:
   text=(ROOT/'books'/f'{file}.lisp').read_text()
   calls=lr.match('(?*xs)',lr.parse(text).forms,head='fn2-rec-context')
   self.assertTrue(calls)
   for match in calls:
    self.assertEqual(match.node.items[10].items[0].low,stem+'-history')
    self.assertEqual(match.node.items[11].items[0].low,stem+'-history-incarnation')

 def test_historical_evidence_pair_is_retained_from_decoded_frame(self):
  text=(ROOT/'books/checkpoint-recovery-evidence.lisp').read_text()
  for name,slots in [('fn2-rec-context',(10,11)),('fn2-rec-header-check',(2,3)),('fn2-rec-seal-check',(5,6))]:
   calls=lr.match('(?*xs)',lr.parse(text).forms,head=name)
   self.assertTrue(calls)
   for match in calls:
    self.assertEqual(match.node.items[slots[0]].low,'history')
    self.assertEqual(match.node.items[slots[1]].low,'incarnation')
  for source in ('(history (fn2-cpe-f *fn2-format-frame-header-field-history*))',
                 '(incarnation (fn2-cpe-f *fn2-format-frame-header-field-incarnation*))',
                 '(history (fn2-cpe journal-history))', '(incarnation (fn2-cpe journal-incarnation))',
                 '(journal-history history) (journal-incarnation incarnation)'):
   self.assertIn(source,text)

 def test_record_envelope_uses_complete_semantic_tuple(self):
  text=(ROOT/'books/checkpoint-recovery-evidence-records.lisp').read_text()
  for field in ('lineage','domain','incarnation'):
   self.assertIn('(= (fn2-cpe-f *fn2-format-record-header-field-'+field+'*) (fn2-origin-'+field+' fn2-origin))',text)
  self.assertNotIn('(fn2-checkpoints-incarnation c fn2-checkpoints)',text)

if __name__=='__main__':unittest.main()

"""CNS source continuation controls; no ACL2 execution/admission claim."""
from pathlib import Path
import copy
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for a in x: yield from walk(a)
def definitions():
 return {x[1]:x for raw in forms((ROOT/'books/cns.lisp').read_text()) for x in walk(read_sexp(raw))
         if x and x[0]=='defun'}
def calls(f,name):return [x for x in walk(f[3:]) if x and x[0]==name]
def progress_before_release(f,status):
 binds=f[4][1] if f[3][0]=='declare' and f[4][0]=='b*' else None
 if binds is None:return False
 for b in binds:
  if isinstance(b[0],list) and b[0] and b[0][0]=='when' and status in str(b[0]):return True
  if isinstance(b[1],list) and b[1] and b[1][0]=='fn2-read-release':return False
 return False
class CNSContinuationSource(unittest.TestCase):
 def setUp(self):self.d=definitions()
 def test_actual_request_generation_and_partition(self):
  src=str(self.d['fn2-cns-read-owner'])
  for term in ('fn2-machines-kind-basesi','fn2-cns-snapshot-read-code','fn2-cns-row-xrow','fn2-machine-generation','fn2-machine-slot'):
   self.assertIn(term,src)
  for term in ('fn2-cns-read-work-owner','fn2-cns-read-work-generation','fn2-cns-read-work-a','fn2-cns-read-work-f'):
   self.assertIn(term,str(self.d['fn2-cns-work-open']))
 def test_frontier_retains_miss_before_release(self):
  f=self.d['fn2-cns-stream-frontier']
  self.assertEqual(len(calls(f,'fn2-read-seek-step')),1)
  self.assertEqual(calls(f,'fn2-read-seek-step')[0][2],'1')
  self.assertTrue(progress_before_release(f,':miss'))
  self.assertFalse(calls(f,'fn2-cns-seek-loop'))
  bad=copy.deepcopy(f)
  for x in walk(bad):
   if x and x[0]=='member-eq' and ':miss' in str(x):x[0]='DROPPED-progress'
  self.assertNotEqual(bad,f)
 def test_lookup_carries_scalars_into_frontier(self):
  f=self.d['fn2-cns-lookup-cursor']
  self.assertEqual(len(calls(f,'fn2-read-lookup')),1)
  self.assertFalse(calls(f,'fn2-cns-lookup-loop'))
  self.assertTrue(any(x[3]=='3' for x in calls(f,'fn2-cns-work-save')))
  self.assertEqual(len(calls(f,'fn2-cns-stream-frontier')),1)
  self.assertNotIn('fn2-cns-pf-merge',str(f))
 def test_item_keeps_selected_addr_during_article_wait(self):
  f=self.d['fn2-cns-item-next'];src=str(f)
  saves=calls(f,'fn2-cns-work-save')
  self.assertTrue(any(x[3]=='3' and 'stream' in str(x) for x in saves))
  self.assertEqual(len(calls(f,'fn2-cns-first-entry')),1)
  self.assertEqual(calls(f,'fn2-cns-first-entry')[0][1],'1')
  self.assertEqual(len(calls(f,'fn2-cns-article-row')),1)
  self.assertIn(':miss',src)
  self.assertFalse(calls(f,'fn2-cns-lookup-loop'))
 def test_article_retry_cannot_change_query_identity(self):
  f=self.d['fn2-cns-article-query'];src=str(f)
  for term in ('*fn2-read-op-idle*','*fn2-read-op-lookup*','*fn2-article-sid*','fn2-fields-value','nfix'):
   self.assertIn(term,src)
  f=self.d['fn2-cns-article-row']
  self.assertEqual(len(calls(f,'fn2-cns-article-query')),1)
  self.assertEqual(len(calls(f,'fn2-read-lookup')),1)
if __name__=='__main__':unittest.main()

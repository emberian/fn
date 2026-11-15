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
  if isinstance(b[0],list) and b[0] and b[0][0]=='when' and any(y and y[0]=='member-eq' and status in str(y) for y in walk(b[0])):return True
  if isinstance(b[1],list) and b[1] and b[1][0]=='fn2-read-release':return False
 return False
class CNSContinuationSource(unittest.TestCase):
 def setUp(self):self.d=definitions()
 def test_actual_request_generation_and_partition(self):
  src=str(self.d['fn2-cns-read-owner'])
  for term in ('fn2-machine-kind-base','fn2-cns-snapshot-read-code','fn2-cns-row-xrow','fn2-machine-generation','fn2-machine-slot'):
   self.assertIn(term,src)
  self.assertIn('*fn2-cns-state-free*',src)
  self.assertIn('*fn2-cns-state-retired*',src)
  for term in ('fn2-cns-read-work-owner','fn2-cns-read-work-generation','fn2-cns-read-work-a','fn2-cns-read-work-f'):
   self.assertIn(term,(ROOT/'books/cns-read-state.lisp').read_text())
 def test_exact_fingerprint_guard_and_mutation_control(self):
  raw=(ROOT/'books/cns-read-state.lisp').read_text()
  d={x[1]:x for f in forms(raw) for x in walk(read_sexp(f)) if x and x[0]=='defun'}
  f=d['fn2-cns-read-work-open']
  expected=[['equal',n,['fn2-cns-read-work-'+n,'w','fn2-cns-read-work']] for n in 'abcdef']
  def complete(node):return all(term in list(walk(node)) for term in expected)
  self.assertTrue(complete(f))
  bad=copy.deepcopy(f)
  for x in walk(bad):
   if x==expected[2]:x[0]='DROPPED-input-c'
  self.assertFalse(complete(bad))
  f=d['fn2-cns-read-work-save']
  for name,param in [('owner','owner'),('generation','gen')]:
   self.assertIn(['equal',param,['fn2-cns-read-work-'+name,'w','fn2-cns-read-work']],list(walk(f)))
  f=self.d['fn2-cns-work-open']
  self.assertEqual(len(calls(f,'fn2-cns-read-owner')),1)
  self.assertEqual(calls(f,'fn2-cns-read-work-open')[0][1:5],['x','op','owner','gen'])
 def test_frontier_retains_miss_before_release(self):
  f=self.d['fn2-cns-stream-frontier']
  self.assertEqual(len(calls(f,'fn2-read-seek-step')),1)
  self.assertEqual(calls(f,'fn2-read-seek-step')[0][2],'1')
  self.assertTrue(progress_before_release(f,':miss'))
  self.assertFalse(calls(f,'fn2-cns-seek-loop'))
  bad=copy.deepcopy(f)
  for x in walk(bad):
   if x and x[0]=='member-eq' and ':miss' in str(x):x[0]='DROPPED-progress'
  self.assertFalse(progress_before_release(bad,':miss'))
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
 def test_mid_reauthenticates_same_selection_before_copy(self):
  f=self.d['fn2-cns-entry-mid'];src=str(f)
  self.assertTrue(calls(f,'fn2-cns-mid-window-p'))
  self.assertEqual(len(calls(f,'fn2-read-seek-step')),1)
  self.assertEqual(len(calls(f,'fn2-read-lookup')),1)
  self.assertFalse(calls(f,'fn2-cns-seek-loop'))
  self.assertFalse(calls(f,'fn2-cns-lookup-loop'))
  self.assertEqual(len(calls(f,'fn2-successor-published')),2)
  self.assertIn(['equal','stamp',['nfix','published']],list(walk(f)))
  self.assertIn(['<=',['+','ms','ml'],'fill'],list(walk(f)))
  self.assertIn(['unsigned-byte-p','32','ms'],list(walk(f)))
  self.assertIn(['if','terminal',':more',':fault'],list(walk(f)))
  bad=copy.deepcopy(f)
  for x in walk(bad):
   if x==['if','terminal',':more',':fault']:x[2]=':ok'
  self.assertNotIn(['if','terminal',':more',':fault'],list(walk(bad)))
  self.assertIn(['if',['equal','absent','1'],':absent',':ok'],list(walk(f)))
  for term in ('opos','oart','*fn2-cns-read-work-done*','fn2-cns-core-mid-span'):
   self.assertIn(term,src)
 def test_actual_reply_callbacks_do_not_encode_on_miss(self):
  for name in ('fn2-cns-put-item','fn2-cns-put-article'):
   f=self.d[name]
   self.assertTrue(calls(f,'fn2-cns-entry-mid'))
   self.assertIn(":miss",str(f))
   self.assertTrue(calls(f,'fn2-cns-work-save'))
  f=self.d['fn2-cns-put-item']
  self.assertFalse(calls(f,'fn2-cns-lookup-loop'))
  self.assertTrue(calls(f,'fn2-cns-article-query'))
  self.assertIn(':miss',str(self.d['fn2-cns-decode-port']))
 def test_legacy_frontier_probe_uses_actual_taken_request(self):
  src=(ROOT/'tests/consumer-commit-unit.lisp').read_text()
  self.assertNotIn('(fn2-cns-stream-frontier 0 0 fn2-core)',src)
  self.assertNotIn('(fn2-cns-stream-frontier 1 0 fn2-core)',src)
  ds={x[1]:x for f in forms(src) for x in walk(read_sexp(f)) if x and x[0]=='defun'}
  f=ds['fn2-ccu-frontier-probe']
  for name in ('fn2-machine-take-fn2-cns','fn2-cns-read-row','fn2-ccu-frontier-drive','fn2-cw-loop'):
   self.assertEqual(len(calls(f,name)),1)
  self.assertIn('*fn2-cns-state-draining*',str(f))
  self.assertIn('*fn2-cns-state-free*',str(f))
 def test_public_callbacks_use_shared_codec_byte_bound(self):
  src=(ROOT/'books/cns.lisp').read_text()
  for name in ('lookup-cursor','decode-port','item-next','put-item','put-article'):
   start=src.index('(defcost fn2-cns-'+name+' ')
   end=src.index('\n :tables',start)
   self.assertIn(':bytes *fn2-c-read-callback-bytes*',src[start:end])
if __name__=='__main__':unittest.main()

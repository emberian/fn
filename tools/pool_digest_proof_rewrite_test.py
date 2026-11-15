"""Source-only proof-subject controls; these do not admit the ACL2 claims."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import pool_digest_budget_rewrite as base
import pool_digest_proof_rewrite as proof
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def one(s,p):return lr.match(p,lr.parse(s).forms,deep=False)[0].node
def text(s,n):return s[n.start:n.end]
class Proof(unittest.TestCase):
 def test_replay_leaves_every_runtime_function_and_legacy_formula_identical(self):
  before=base.rewrite(read('tools/fixtures/pool-digest-budget-before.lisp'));after=proof.rewrite(before)
  self.assertEqual(after,read('books/pool-digest.lisp'));self.assertEqual(after,proof.rewrite(after))
  old={m.captures['name'].low:text(before,m.node) for m in lr.match('(defun ?name ?*body)',lr.parse(before).forms,deep=False)}
  new={m.captures['name'].low:text(after,m.node) for m in lr.match('(defun ?name ?*body)',lr.parse(after).forms,deep=False)}
  worker=one(after,'(defun fn2-rec-fetch-bytes ?*body)')
  xargs=lr.match('(xargs ?*body)',[worker])[0].node
  for i,n in enumerate(xargs.items[:-1]):
   if getattr(n,'low',None)==':hints':
    cleaned=lr.write(after,[(n.start,xargs.items[i+1].end,'')])
    new['fn2-rec-fetch-bytes']=text(cleaned,one(cleaned,'(defun fn2-rec-fetch-bytes ?*body)'))
    break
  self.assertEqual({k:v for k,v in old.items() if k!='fn2-rec-fetch-bytes'},
                   {k:v for k,v in new.items() if k!='fn2-rec-fetch-bytes'})
  import re
  self.assertEqual(re.sub(r'\s+','',old['fn2-rec-fetch-bytes']),
                   re.sub(r'\s+','',new['fn2-rec-fetch-bytes']))
  prior=one(before,'(defun fn2-rec-fetch-bytes ?*body)')
  self.assertEqual(text(before,prior.items[-1]),text(after,worker.items[-1]))
  for name in ['fn2-rec-fetch-step-progress-bound','fn2-rec-fetch-step-result-state','fn2-rec-fetch-step-zero','fn2-rec-fetch-step-shape','fn2-rec-fetch-exec-refines','fn2-rec-fetch-shape']:
   a=one(before,'(defthm '+name+' ?*body)');b=one(after,'(defthm '+name+' ?*body)')
   self.assertEqual(text(before,a.items[2]),text(after,b.items[2]),name)
 def test_word_proof_uses_original_reads_and_original_store_expression(self):
  source=read('books/pool-digest.lisp');rhs=proof.four_rhs(source)
  fn=one(source,'(defun fn2-rec-fetch ?*body)');logic=fn.items[-1]
  bindings=lr.match('(b* ?bindings ?*body)',[logic])[0].captures['bindings'].items
  for n in bindings[:5]:self.assertIn(text(source,n),rhs)
  for n in bindings:
   if isinstance(n,lr.Lst) and getattr(n.items[0],'low',None) in ('word','fn2-digests'):
    self.assertIn(text(source,n),rhs)
  self.assertIn('(mv-nth 1 (fn2-layout-byte :u32',rhs)
  self.assertIn('(if (= k 7) :ok :more)',rhs)
  self.assertNotIn('(defun',rhs)
 def test_termination_uses_only_natural_measure_fact(self):
  s=read('books/pool-digest.lisp');worker=one(s,'(defun fn2-rec-fetch-bytes ?*body)')
  self.assertIn(':use ((:instance fn2-rec-fetch-left-measure))',text(s,worker))
  self.assertIn(":in-theory (theory 'minimal-theory)",text(s,worker))
  lemma=lr.match('(defthm fn2-rec-fetch-left-measure ?*body)',lr.parse(s).forms)[0].node
  self.assertTrue(lr.match('(and (o-p (nfix left)) (implies (not (zp left)) (o< (nfix (- left 1)) (nfix left))))',[lemma]))
  self.assertNotIn('fn2-pool',text(s,lemma));self.assertNotIn('fn2-layout',text(s,lemma))
 def test_structural_shape_keeps_codec_state_and_width_opaque(self):
  s=read('books/pool-digest.lisp')
  n=lr.match('(defthm fn2-rec-fetch-bytes-shape ?*body)',lr.parse(s).forms)[0].node
  self.assertIn('(e/d (fn2-rec-fetch-bytes fn2-digest-rowp)',text(s,n))
  self.assertIn('(fn2-rec-fetch-state-p unsigned-byte-p)',text(s,n))
  self.assertTrue(lr.match('(implies (and (fn2-digestsp fn2-digests) (fn2-digest-rowp dst fn2-digests)) (and (fn2-digestsp (mv-nth 3 ?call)) (fn2-digests-wfp (mv-nth 3 ?call)) (equal (fn2-digests-rows (mv-nth 3 ?call)) (fn2-digests-rows fn2-digests))))',[n]))
 def test_exported_result_state_requires_valid_input(self):
  s=read('books/pool-digest.lisp');n=one(s,'(defthm fn2-rec-fetch-step-result-state ?*body)')
  self.assertTrue(lr.match('(implies (and (natp budget) (natp off) (fn2-rec-fetch-state-p next acc)) (fn2-rec-fetch-state-p (mv-nth 1 ?call) (mv-nth 2 ?call)))',[n]))
  self.assertIn(':use ((:instance fn2-rec-fetch-bytes-bound',text(s,n))
 def test_compose_is_full_tuple_and_full_refinement_is_whole_carrier(self):
  s=read('books/pool-digest.lisp');forms=lr.parse(s).forms
  compose=lr.match('(defthm fn2-rec-fetch-bytes-compose ?*body)',forms)[0].node
  self.assertTrue(lr.match('(equal (mv-list 4 ?left) (mv-list 4 ?right))',[compose]))
  self.assertTrue(lr.match('(if (eq code :more) ?resume (mv code after partial fn2-digests))',[compose]))
  full=one(s,'(defthm fn2-rec-fetch-exec-refines ?*body)')
  self.assertTrue(lr.match('(equal (mv-list 2 ?left) (mv-list 2 ?right))',[full]))
  self.assertTrue(lr.match('(fn2-rec-fetch k dst ?*args)',[full]))
  self.assertTrue(lr.match('(fn2-rec-fetch-step (- 32 (* 4 k)) (* 4 k) 0 dst ?*args)',[full]))
  self.assertIn(':induct (fn2-rec-fetch k',text(s,full))
  for name in ['fn2-rec-fetch-four-code','fn2-rec-fetch-four-next','fn2-rec-fetch-four-acc','fn2-rec-fetch-four-digests','fn2-rec-fetch-remaining-code','fn2-rec-fetch-remaining-digests']:
   n=lr.match('(defthm '+name+' ?*body)',forms)[0].node
   self.assertNotIn(':rule-classes nil',text(s,n),name)
if __name__=='__main__':unittest.main()

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
  self.assertEqual(old,new)
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

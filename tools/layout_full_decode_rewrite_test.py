"""Complete generated entry decoder uses declared work; streaming remains quota-bound."""
from pathlib import Path
import hashlib,unittest
import lisp_rewrite as lr
import layout_full_decode_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
def form(s,p):
 n=calls(s,p)[0].node
 return s[n.start:n.end]
class Full(unittest.TestCase):
 def test_exact_current_canonical_replay_and_idempotence(self):
  old=read('tools/fixtures/layout-full-decode-before.lisp')
  self.assertEqual(hashlib.sha256(old.encode()).hexdigest(),'2060684efd33bb23e0c426275edc9a3dc6c47b50ceda0b80207c84ec7fd89d48')
  after=rw.rewrite(old);self.assertEqual(after,read('books/layout.lisp'));self.assertEqual(rw.rewrite(after),after)
  for p in ['(defthm fn2-layoutp-head ?*body)','(verify-guards fn2-layout-scan ?*body)','(defun fn2-layout-emit ?*body)']:
   self.assertEqual(form(old,p),form(after,p))
  self.assertEqual(old.count('(local (in-theory *fn2-codec-proof-runes*))'),after.count('(local (in-theory *fn2-codec-proof-runes*))'))
 def test_one_derived_transition_budget_for_full_callers(self):
  s=read('books/layout.lisp')
  self.assertTrue(calls(s,'(max 1 (+ (nfix (fn2-layout-max-size layout)) (len layout)))'))
  model=form(s,'(defun fn2-layout-decode ?*body)');self.assertNotIn('4096',model)
  self.assertTrue(calls(model,'(fn2-layout-decode-transition-bound layout)'))
  encoder=form(s,'(defun fn2-layout-encode ?*body)');self.assertNotIn('4096',encoder)
  self.assertTrue(calls(encoder,'(fn2-layout-emit layout (fn2-layout-decode-transition-bound layout) ?*args)'))
  generated=form(s,'(defun fn2-codec-events ?*body)')
  self.assertIn('(defconst ,transitions-name ,(fn2-layout-decode-transition-bound layout))',generated)
  self.assertIn(':decode-transitions ,transitions-name',generated)
  self.assertIn('(,scan ,transitions-name base',generated)
 def test_actual_step_keeps_explicit_quota_and_full_does_not_silently_yield(self):
  s=read('books/layout.lisp')
  self.assertTrue(calls(s,'(or (not resume) (<= budget 4096))'))
  self.assertIn('(posp budget) (<= budget 4096)',s)
  self.assertEqual(len(calls(s,'(if (eq code :more) :oversized code)')),2)
  hyp=form(s,'(defun fn2-codec-spec-events ?*body)')
  self.assertNotIn('(<= (+ (- end off)',hyp)
  self.assertIn('(eq (,check base slot off end okind oslot ogen fn2-fields fn2-pool) :ok)',hyp)
 def test_near_max_actual_codec_builder_and_budget1_witness(self):
  s=read('tests/event-archive-entry-size-unit.lisp')
  for p in ['(fn2-event-archive-member-entry-roundtrip-hyps ?*args)','(fn2-layout-roundtrip-resultp ?*args)',
            '(fn2-run-lookup-image 20 *fn2-event-archive-member-entry* ?*args)',
            '(fn2-event-archive-member-entry-decode-step 0 slot gen 0 end 9 0 1 1 fn2-fields fn2-pool)',
            '(> end 4096)','(eq old-quota :more)','(< old-next end)','(not (eq wrong-owner :ok))',
            '(<= (- next before) 1)']:
   self.assertTrue(calls(s,p),p)
if __name__=='__main__':unittest.main()

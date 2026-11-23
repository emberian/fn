"""Actual declaration/consumer controls; no runtime qualification claim."""
from pathlib import Path
import subprocess
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
BASE='885e36e807daca0027c974109758e3ddee19c700'
def form(s,name):
 m=lr.match('(defun '+name+' ?*body)',lr.parse(s).forms,deep=False)
 assert len(m)==1,name
 return s[m[0].start:m[0].end]
class AtomicPage(unittest.TestCase):
 def test_same_reserve_body_and_default_template(self):
  old=subprocess.check_output(['git','show',BASE+':books/machine-arms.lisp'],cwd=ROOT,text=True)
  new=(ROOT/'books/machine-arms.lisp').read_text()
  self.assertEqual(form(old,'fn2-arms-registry-reserves'),form(new,'fn2-arms-registry-reserves'))
  actual=form(new,'fn2-arms-registry-events')
  inverse=[
   ('         (inputs (fn2-machine-range-inputs specs))\n',''),
   ("copies '(ordinal kind) tuple inputs))","copies '(ordinal kind) tuple))"),
   ('                ,@(fn2-arm-get :set spec)\n',''),
   ('      (if (fn2-machine-range-provider-problem specs world)\n          (er hard \'defmachine-registry "~@0" (fn2-machine-range-provider-problem specs world))\n',''),
   (':stobjs ,(append tuple inputs)',':stobjs ,tuple'),
   ('                                      ,@(fn2-arms-child-shape-hyps inputs)\n',''),
   ('tuple (append tuple inputs)','tuple tuple'),
   ('*fn2-arms-registry-callees* t world))))))','*fn2-arms-registry-callees* t world)))))')]
  for a,b in inverse:
   self.assertEqual(actual.count(a),1,a);actual=actual.replace(a,b)
  self.assertEqual(actual,form(old,'fn2-arms-registry-events'))
 def test_typed_actual_child_not_eval_or_accessor_guess(self):
  s=(ROOT/'books/machines.lisp').read_text()
  for token in ["'stobjs-in", "'stobjs-out", "'(nil)", '(fn2-decl-rows :core-child world)',
                '(fn2-machine-range-provider-problem specs world)']:
   self.assertIn(token,s if 'provider-problem specs' not in token else (ROOT/'books/machine-arms.lisp').read_text())
  self.assertNotIn('subseq',form(s,'fn2-machine-range-input-bindings'))
  self.assertNotIn('eval',form(s,'fn2-machine-class-bytes-form'))
  access=(ROOT/'books/machines-a-access.lisp').read_text()
  self.assertIn('(fn2-machine-partition-runtime-classes o fn2-core)',access)
  self.assertIn('(fn2-machine-partition-runtime-class-event (w state))',access)
 def test_three_ranges_atomic_marker_and_no_clear(self):
  s=(ROOT/'books/upload-kind.lisp').read_text()
  machine=lr.match('(defmachine fn2-upload ?*fields)',lr.parse(s).forms)[0].node
  pos=next(i for i,x in enumerate(machine.items) if getattr(x,'text','')==':taken')
  take=machine.items[pos+1]
  text=s[take.start:take.end]
  self.assertEqual(text.count(':class'),3)
  self.assertIn(':class (:bytes (:from fn2-input-config fn2-upload-stream-request-bytes))',text)
  self.assertIn(':set ((lease *fn2-upload-lease-held*))',text)
  pos=next(i for i,x in enumerate(take.items) if getattr(x,'text','')==':clear')
  names=[getattr(x,'text','') for x in take.items[pos+1].items]
  self.assertNotIn('lease',names);self.assertNotIn('lgen',names)
  for phase in ['head','identity','receiving','validating','discard']:
   self.assertIn(f'(:{phase} :upload-row :chunk-window (:storage-window :while (lease :held)))',s)
 def test_no_page_wait_and_ordered_early_cleanup(self):
  s=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  init=lr.match('(:stream-init ?*body)',lr.parse(s).forms)[0]
  t=s[init.start:init.end]
  self.assertNotIn('fn2-core-reserve',t);self.assertNotIn(':park :pool',t)
  self.assertIn('fn2-upload-stream-page-ready-p',t)
  abort=lr.match('(:aborting ?*body)',lr.parse(s).forms)[0];t=s[abort.start:abort.end]
  self.assertLess(t.index('row-pending'),t.index('row-stream-active'))
  self.assertLess(t.index(':live child-txn'),t.index('row-stream-active'))
  drain=lr.match('(:draining :on-refusal ?ref ?*body)',lr.parse(s).forms)[0]
  branch=lr.match('((and (equal row-lease *fn2-upload-lease-held*) (equal row-stream-active 0)) ?*body)',[drain.node])[0]
  t=s[branch.start:branch.end]
  self.assertIn('fn2-upload-page-release',t);self.assertNotIn('settle',t);self.assertNotIn('extents-close',t)
  self.assertEqual(len(lr.match('(:uncertain (:stop :upload-uncertain))',lr.parse(s).forms)),1)
 def test_input_init_precedes_f_and_take_atomic_marker(self):
  k=(ROOT/'books/upload-kind.lisp').read_text()
  self.assertIn('(defcorechild fn2-core-input-config fn2-input-config',k)
  self.assertIn(':init (fn2-input-config-from profile fn2-input-config)',k)
  core=(ROOT/'books/core.lisp').read_text()
  self.assertIn('(let* ,(fn2-core-init-child-chain *fn2-core-children*) fn2-core)',core)
  self.assertIn('(fn2-core-registered-inits (fn2-core-child-registry (w state)))',core)
  e=form((ROOT/'books/executor.lisp').read_text(),'fn2-init-executor')
  body=e[e.index('  (b*'):]
  self.assertLess(body.index('(fn2-core-init profile fn2-core)'),body.index('(fn2-init-credit-boundary profile fn2-core)'))
  self.assertLess(body.index('(fn2-init-credit-boundary profile fn2-core)'),body.index('(fn2-init-engine profile fn2-core)'))
  g=form((ROOT/'books/machine-arms.lisp').read_text(),'fn2-arms-registry-events')
  self.assertLess(g.index(',@(fn2-machine-range-puts specs 0)'),g.index(',@(fn2-arm-get :set spec)'))
  self.assertIn('(fn2-arms-registry-reserves specs 0 install fail)',g)
  self.assertIn('(mv-let (,kind fn2-machines fn2-control) ,put',g)
  # No row installation occurs in the pool-only reserve/unwind producer.
  reserve=form((ROOT/'books/machine-arms.lisp').read_text(),'fn2-arms-registry-reserves')
  self.assertNotIn('fn2-machines-partition-install',reserve)
  self.assertNotIn('fn2-upload-put',reserve)
 def test_same_f_input_and_no_double_count(self):
  s=(ROOT/'books/checkpoint-working-credit-init.lisp').read_text()
  self.assertIn('(fn2-input-config (fn2-core-input-config fn2-core))',s)
  self.assertIn('(fn2-checkpoint-service-upload-classes fn2-input-config fn2-pool)',s)
  g=(ROOT/'books/checkpoint-service-geometry.lisp').read_text()
  self.assertIn('(equal (len uploads) 3)',g)
  self.assertIn('(equal page-class (caddr uploads))',g)
  self.assertNotIn('(if (equal class page-class) 1 0)',g)
  fixture=(ROOT/'tests/upload-page-take-unit.lisp').read_text()
  for call in ['fn2-machine-take-fn2-upload','fn2-turn','fn2-upt-leave-one','fn2-upt-owned',
               '(fn2-upt-case nil nil)','(fn2-upt-case t nil)','(fn2-upt-case nil t)','(fn2-upt-case t t)']:
   self.assertIn(call,fixture)
if __name__=='__main__':unittest.main()

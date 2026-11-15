#!/usr/bin/env python3
"""Source rejection controls for the actual bounded unpublished abort."""
from pathlib import Path
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def definition(source,name):
 for text in forms(source):
  for f in walk(read_sexp(text)):
   if f[:2]==['defun',name]:return f
 raise AssertionError(name)
def check(source,state):
 owner=list(walk(definition(source,'fn2-checkpoint-build-abort-ownerp')[-1]))
 assert ['equal',['fn2-checkpoint-planning-phase','0','fn2-checkpoint-planning'],'*fn2-checkpoint-planning-phase-cancel-empty*'] in owner
 assert ['<=',['fn2-checkpoint-construction-rows','fn2-checkpoint-construction'],['fn2-checkpoint-planning-abort-row','0','fn2-checkpoint-planning']] in owner
 assert ['fn2-checkpoint-planning-cancel-ownerp','c','token','kind','owner','gen','fn2-checkpoint-planning','fn2-extents'] in owner
 assert ['fn2-checkpoint-builder-ownerp','c','token','kind','owner','gen','fn2-checkpoints'] in owner
 for f in ['installation-commit','anchor-mask']:
  assert ['equal',[f'fn2-checkpoints-{f}','c','fn2-checkpoints'],'0'] in owner
 assert ['equal',['fn2-checkpoints-history','c','fn2-checkpoints'],['fn2-checkpoint-build-history','0','fn2-checkpoint-build']] in owner
 assert ['equal',['fn2-checkpoints-incarnation','c','fn2-checkpoints'],['fn2-checkpoint-build-history-incarnation','0','fn2-checkpoint-build']] in owner
 roots=list(walk(definition(source,'fn2-checkpoint-build-abort-roots-p')[-1]))
 for f in ['retained','root-source-complete','root-completed-bytes']:
  assert ['equal',[f'fn2-checkpoint-refs-{f}','r','fn2-checkpoint-refs'],'0'] in roots
 step=definition(source,'fn2-checkpoint-build-abort-step')[-1]
 assert step[1][0] == [['unless',['and',['natp','budget'],['<','0','budget']]],['mv',':yield','fn2-checkpoint-build','fn2-checkpoint-refs','fn2-checkpoint-bytes','fn2-extents','fn2-alloc-edges']]
 nodes=list(walk(step))
 assert ['fn2-alloc-edge-drop','edge',['fn2-checkpoints-checkpoint','c','fn2-checkpoints'],'i',['fn2-alloc-edges-epoch','edge','fn2-alloc-edges'],['fn2-alloc-edges-counter','edge','fn2-alloc-edges'],':prepared-successor','fn2-extents','fn2-alloc-edges'] in nodes
 assert ['fn2-alloc-edge-matchesp','edge',['fn2-checkpoints-checkpoint','c','fn2-checkpoints'],'i',['fn2-alloc-edges-epoch','edge','fn2-alloc-edges'],['fn2-alloc-edges-counter','edge','fn2-alloc-edges'],':prepared-successor','fn2-alloc-edges'] in nodes
 assert ['fn2-checkpoint-bytes-set-value',['+',['*','192','c'],['-','i','n','6']],'0','fn2-checkpoint-bytes'] in nodes
 assert ['equal','i',['+','n','6','192']] in nodes
 assert not any(n and n[0] in ('fn2-checkpoints-put','fn2-checkpoints-set-state','fn2-alloc-planning-end','fn2-alloc-retire') for n in nodes)
 assert '(:idle :await-roots :pack :page :bound :ready :uncertain :cancelling :cancelled)' in state
 assert '(abort-row :u32)' in state
def check_finish(source,arms,state):
 f=definition(source,'fn2-checkpoint-build-abort-finish')
 assert f[2][:5] == ['budget','token','kind','owner','gen']
 body=f[-1];nodes=list(walk(body))
 assert ['equal',['fn2-checkpoint-build-phase','0','fn2-checkpoint-build'],'*fn2-checkpoint-build-phase-cancelled*'] in nodes
 assert ['equal',['fn2-checkpoint-build-abort-row','0','fn2-checkpoint-build'],['+',['fn2-extents-rows','fn2-extents'],'6','192']] in nodes
 assert ['fn2-checkpoint-root1-abort-reset-p','c','token','kind','owner','gen','fn2-checkpoint-root1-abort'] in nodes
 assert ['fn2-checkpoint-future-no-loansp','0','*fn2-checkpoint-future-window-count*','fn2-checkpoint-future-windows'] in nodes
 assert ['equal',['fn2-checkpoint-root1-token','0','fn2-checkpoint-root1'],'0'] in nodes
 assert ['equal',['fn2-checkpoint-future-token','0','fn2-checkpoint-future'],'0'] in nodes
 assert ['fn2-alloc-planning-end','token','kind','owner','gen',['fn2-alloc-free-head','fn2-extents'],['fn2-alloc-current-epoch','fn2-extents'],['fn2-alloc-next-counter','fn2-extents'],'fn2-extents'] in nodes
 bindings=body[1]
 end=next(i for i,b in enumerate(bindings) if isinstance(b[0],list) and b[0][:2]==['mv','code'])
 clear=next(i for i,b in enumerate(bindings) if b[0]=='fn2-checkpoints')
 assert end<clear and bindings[end+1][0] == ['unless',['eq','code',':ok']]
 assert not any(n and n[0] in ('fn2-csnapshot-release','fn2-core-release','fn2-checkpoint-publication-put','fn2-alloc-release') for n in nodes)
 form=next(read_sexp(t) for t in forms(arms) if read_sexp(t)[:2]==['defmachine-arms','fn2-checkpoint-master'])
 amap={a[0]:a for a in form[form.index(':arms')+1]}
 expected={':cancel-ledger':'fn2-checkpoint-root1-planning-cancel-op',':cancel-candidate':'fn2-checkpoint-build-abort-step-op',':cancel-reset':'fn2-checkpoint-root1-abort-reset-op',':cancel-finish':'fn2-checkpoint-build-abort-finish-op'}
 for tag,call in expected.items():
  assert any(n and n[0]==call for n in walk(amap[tag]))
  assert not any(n and n[0]=='fn2-csnapshot-release' for n in walk(amap[tag]))
 assert [':next',':cancel-candidate'] in list(walk(amap[':cancel-ledger']))
 assert [':next',':cancel-reset'] in list(walk(amap[':cancel-candidate']))
 assert [':next',':cancel-finish'] in list(walk(amap[':cancel-reset']))
 assert [':next',':abort-snapshot'] in list(walk(amap[':cancel-finish']))
 machine=next(read_sexp(t) for t in forms(state) if read_sexp(t)[:2]==['defmachine','fn2-checkpoint-master'])
 holds={h[0]:h[1:] for h in machine[machine.index(':holds')+1]}
 for tag in expected:assert holds[tag]==[':storage-window',':storage-window']

if __name__=='__main__':
 p=(ROOT/'books/checkpoint-build-abort.lisp').read_text();state=(ROOT/'books/checkpoint-build-state.lisp').read_text();check(p,state)
 muts=[]
 for f in ('installation-commit','anchor-mask'):
  muts.append(p.replace(f'(equal (fn2-checkpoints-{f} c fn2-checkpoints) 0)','t',1))
 for f in ('retained','root-source-complete','root-completed-bytes'):
  muts.append(p.replace(f'(equal (fn2-checkpoint-refs-{f} r fn2-checkpoint-refs) 0)','t',1))
 muts += [p.replace('(equal (fn2-checkpoint-planning-phase 0 fn2-checkpoint-planning) *fn2-checkpoint-planning-phase-cancel-empty*)','t',1),
          p.replace('(<= (fn2-checkpoint-construction-rows fn2-checkpoint-construction) (fn2-checkpoint-planning-abort-row 0 fn2-checkpoint-planning))','t',1),
          p.replace('(equal i (+ n 6 192))','t',1),
          p.replace('(fn2-alloc-edge-drop edge (fn2-checkpoints-checkpoint c fn2-checkpoints) i','(fn2-alloc-edge-drop edge 0 i',1)]
 for m in muts:
  try:check(m,state)
  except AssertionError:pass
  else:raise AssertionError('mutation survived')
 print(f'build abort source controls: {len(muts)} rejected mutations; no runtime claim')

 finish=(ROOT/'books/checkpoint-build-abort-finish.lisp').read_text()
 arms=(ROOT/'books/checkpoint-master-arms.lisp').read_text()
 master=(ROOT/'books/checkpoint-master-state.lisp').read_text()
 check_finish(finish,arms,master)
 mutations=[finish.replace('(equal (fn2-checkpoint-build-abort-row 0 fn2-checkpoint-build) (+ (fn2-extents-rows fn2-extents) 6 192))','t',1),
   finish.replace('(fn2-checkpoint-root1-abort-reset-p c token kind owner gen fn2-checkpoint-root1-abort)','t',1),
   finish.replace('(fn2-alloc-free-head fn2-extents)','0',1)]
 for bad in mutations:
  try:check_finish(bad,arms,master)
  except AssertionError:pass
  else:raise AssertionError('unsafe finish mutation survived')
 print('build abort finish/master controls: 3 rejected mutations; no runtime claim')

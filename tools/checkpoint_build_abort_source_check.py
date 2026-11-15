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

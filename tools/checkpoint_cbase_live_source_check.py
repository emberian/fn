#!/usr/bin/env python3
"""Actual live C promise source controls; no execution/admission claim."""
from pathlib import Path
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def definition(s,name):return next(n for t in forms(s) for n in walk(read_sexp(t)) if n[:2]==['defun',name])
def check(s):
 source=list(walk(definition(s,'fn2-checkpoint-cbase-live-source-p')))
 for term in [
  ['fn2-checkpoint-summary-authority-row-complete-p','1','fn2-checkpoint-summary-authority','fn2-checkpoints','fn2-checkpoint-refs','fn2-checkpoint-bytes'],
  ['=',['fn2-checkpoint-summary-authority-origin','1','fn2-checkpoint-summary-authority'],'*fn2-checkpoint-summary-authority-origin-live*'],
  ['=',['fn2-checkpoint-summary-phase','1','fn2-checkpoint-summary'],'*fn2-checkpoint-summary-phase-captured*'],
  ['=',['fn2-checkpoint-lifecycle-phase','0','fn2-checkpoint-lifecycle'],'*fn2-checkpoint-lifecycle-phase-publication*'],
  ['=',['fn2-checkpoint-publication-phase','0','fn2-checkpoint-publication'],'*fn2-checkpoint-publication-phase-complete*'],
  ['=',['fn2-alloc-freeze-phase','fn2-extents'],'2'],
  ['fn2-checkpoint-cbase-live-descriptor-p','0','c','fn2-checkpoint-summary','fn2-checkpoint-bytes']]:assert term in source
 for fn in ['fn2-checkpoint-builder-claimp','fn2-checkpoint-lifecycle-ownerp']:assert any(n and n[0]==fn for n in source)
 step=definition(s,'fn2-checkpoint-cbase-live-acquire-step');nodes=list(walk(step))
 assert not any(x in step[2] for x in ['r','c','e','epoch','allocation','complete','ready'])
 assert ['unless',['and',['natp','budget'],['<','0','budget']]] in nodes
 for term in [
  ['fn2-checkpoint-cbase-start','1','fn2-checkpoint-summary','fn2-ops','fn2-checkpoints','fn2-extents','fn2-checkpoint-cbase-holds'],
  ['fn2-checkpoint-cbase-row-identity-p','1','fn2-checkpoint-summary','fn2-checkpoint-cbase-holds'],
  ['fn2-alloc-edge-matchesp','source','checkpoint','e','epoch','allocation',':selectable-checkpoint','fn2-alloc-edges'],
  ['=',['fn2-extents-release-pending','e','fn2-extents'],'0'],
  ['fn2-alloc-edge-add','edge','tag','e','epoch','allocation',':promised-read','fn2-extents','fn2-alloc-edges']]:assert term in nodes
 assert not any(n and n[0] in ['fn2-alloc-edge-drop','fn2-alloc-release','fn2-checkpoint-restore-reach-row-p'] for n in nodes)
if __name__=='__main__':
 s=(ROOT/'books/checkpoint-cbase-live-acquire.lisp').read_text();check(s)
 mutations=[('(= (fn2-alloc-freeze-phase fn2-extents) 2)','t'),
  ('(= (fn2-extents-release-pending e fn2-extents) 0)','t'),
  ('(fn2-checkpoint-cbase-start 1 ','(fn2-checkpoint-cbase-start 0 '),
  ('(fn2-checkpoint-builder-claimp ','(missing-claim '),
  ('(fn2-checkpoint-lifecycle-ownerp ','(missing-owner '),
  ('(fn2-checkpoint-cbase-live-descriptor-p 0 ','(missing-descriptor 0 '),
  ('(fn2-checkpoint-summary-authority-row-complete-p 1 ','(missing-authority 1 '),
  (':selectable-checkpoint fn2-alloc-edges)',':recovery-base fn2-alloc-edges)'),
  ('(fn2-alloc-edge-add edge tag e epoch allocation :promised-read','(fn2-alloc-edge-add-transition edge tag e epoch allocation :promised-read')]
 for old,new in mutations:
  assert old in s
  try:check(s.replace(old,new,1))
  except (AssertionError,StopIteration):continue
  raise AssertionError('weakened live promise survived:'+old)
 print(f'live C-base source controls: {len(mutations)} rejected mutations; no execution/admission claim')

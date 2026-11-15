#!/usr/bin/env python3
"""Shared bounded insertion source controls; not runtime/proof admission."""
from pathlib import Path
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def definition(src,name):
 return next(n for f in forms(src) for n in walk(read_sexp(f)) if n[:2]==['defun',name])
def check(pipeline,leaf,assembly):
 step=definition(pipeline,'fn2-ov-insert-step');nodes=list(walk(step))
 assert ['unless',['and',['natp','budget'],['<','0','budget']]] in nodes
 for fn in ['fn2-ov-order','fn2-run-layout-encode','fn2-ov-insertion-step']:
  assert sum(bool(n) and n[0]==fn for n in nodes)==1
 for fn in ['fn2-ov-search','fn2-ov-insert','fn2-ov-insert-step','fn2-ov-insert-at']:
  assert not any(n and n[0]==fn for n in walk(step[4:]))
 assert ['phase','*fn2-ov-insertion-phase-order*'] in nodes
 assert ['phase','*fn2-ov-insertion-phase-shift*'] in nodes
 low=definition(leaf,'fn2-ov-insertion-step');ln=list(walk(low))
 assert ['unless',['and',['natp','budget'],['<','0','budget']]] in ln
 assert ['remaining',['-','n','1']] not in ln # actual specialized setter below
 assert ['fn2-ov-insertion-set-remaining','0',['-','n','1'],'fn2-ov-insertion'] in ln
 assert sum(bool(n) and n[0]=='fn2-overlay-index-set-off' for n in ln)==2 # move OR terminal
 assert '(fn2-ra-insertion-events)' in assembly
 assert '(fn2-ov-search *fn2-ov-search-limit* 0' in assembly
if __name__=='__main__':
 p=(ROOT/'books/runs-insertion.lisp').read_text();l=(ROOT/'books/overlay-insertion.lisp').read_text();a=(ROOT/'books/runs-assemble.lisp').read_text();check(p,l,a)
 mutations=[(p.replace('(natp budget) (< 0 budget)','t'),l,a),
  (p.replace('(fn2-ov-order o pos','(fn2-ov-search o pos'),l,a),
  (p.replace('(phase *fn2-ov-insertion-phase-order*)','(phase *fn2-ov-insertion-phase-shift*)'),l,a),
  (p,l.replace('(natp budget) (< 0 budget)','t'),a),
  (p,l.replace('(- n 1)','n'),a),
  (p,l,a.replace('   (fn2-ra-insertion-events)\n',''))]
 for args in mutations:
  try:check(*args)
  except (AssertionError,StopIteration):continue
  raise AssertionError('weakened bounded insertion survived')
 print(f'overlay insertion source: {len(mutations)} mutations rejected; executable fixtures unrun')

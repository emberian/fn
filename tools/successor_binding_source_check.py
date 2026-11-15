#!/usr/bin/env python3
"""Ownership/progress source controls; executable C/B fixture remains unrun."""
from pathlib import Path
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def definition(src,name):return next(n for f in forms(src) for n in walk(read_sexp(f)) if n[:2]==['defun',name])
def calls(form):return [n[0] for n in walk(form) if n and isinstance(n[0],str)]
def check(kernel,bind,stage,snapshot):
 begin=definition(kernel,'fn2-succ-bind-begin');bn=list(walk(begin))
 step=definition(kernel,'fn2-succ-bind-step');sn=list(walk(step))
 for ns in [bn,sn]:assert ['unless',['and',['natp','budget'],['<','0','budget']]] in ns
 assert 'fn2-successor-emit-claim-current-p' in calls(begin)
 assert 'fn2-succ-binder-pending-code' in calls(begin) and 'fn2-succ-binder-pending-code' in calls(step)
 assert ['phase','*fn2-succ-phase-binding*'] in bn
 assert ['binding-target-cursor',['+','1','row']] in sn
 assert ['fn2-id-engine-set-binding-scan','0',['+','1','row'],'fn2-id-engine'] in sn
 assert ['unless',['=','i','*fn2-succ-slots*']] in sn
 assert ['bind-phase','*fn2-succ-bind-phase-complete*'] in sn
 for forbidden in ['fn2-succ-bind','fn2-succ-bind-slots','fn2-succ-target','fn2-succ-newest-private','fn2-succ-unstage','fn2-ov-insert','fn2-ov-locate','fn2-ov-search','fn2-pool-release']:
  assert forbidden not in calls(step)
 prep=definition(bind,'fn2-succ-bind-slot-prepare')
 for forbidden in ['fn2-succ-target','fn2-ov-insert']:assert forbidden not in calls(prep)
 pending=definition(kernel,'fn2-succ-binder-pending-code')
 assert 'fn2-commit-successor-bind-pending-p' in calls(pending)
 assert 'fn2-commit-phase' not in calls(pending) # volatile work continues through B failure
 assert 'fn2-successor-binder-idle-p' in calls(definition(stage,'fn2-idc-scratch'))
 assert 'fn2-successor-binder-idle-p' in calls(definition(stage,'fn2-succ-stage-raw'))
 assert '*fn2-succ-phase-binding*' in calls(definition(bind,'fn2-succ-release')) or '*fn2-succ-phase-binding*' in str(definition(bind,'fn2-succ-release'))
 assert '(= phase *fn2-succ-phase-binding*)' in snapshot
if __name__=='__main__':
 k=(ROOT/'books/successor-binding.lisp').read_text();b=(ROOT/'books/machines-c-bind.lisp').read_text();s=(ROOT/'books/machines-c-stage.lisp').read_text();c=(ROOT/'books/c-snapshot.lisp').read_text();check(k,b,s,c)
 mutations=[(k.replace('(natp budget) (< 0 budget)','t'),b,s,c),
  (k.replace('(binding-target-cursor (+ 1 row))','(binding-target-cursor row)'),b,s,c),
  (k.replace('(fn2-id-engine-set-binding-scan 0 (+ 1 row)','(fn2-id-engine-set-binding-scan 0 row'),b,s,c),
  (k.replace('((unless (= i *fn2-succ-slots*))','((unless t)'),b,s,c),
  (k,b,s.replace('(fn2-successor-binder-idle-p fn2-id-engine)','t'),c),
  (k,b,s,c.replace('(= phase *fn2-succ-phase-binding*)','nil'))]
 for args in mutations:
  try:check(*args)
  except (AssertionError,StopIteration):continue
  raise AssertionError('weakened binder source survived')
 print(f'successor binder source: {len(mutations)} mutations rejected; no runtime/admission claim')

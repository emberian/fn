#!/usr/bin/env python3
"""Source controls for declaration-derived workspace; no admission claim."""
from pathlib import Path
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def definition(s,kind,name):return next(n for t in forms(s) for n in walk(read_sexp(t)) if n[:2]==[kind,name])
def check(g,c,pure):
 for name,expr in [('*fn2-succ-raw*','*fn2-succ-fields-max*'),
  ('*fn2-succ-eval*',['+','*fn2-succ-raw*','*fn2-succ-fields-max*']),
  ('*fn2-succ-res*',['+','*fn2-succ-eval*','*fn2-succ-fields-max*']),
  ('*fn2-succ-fresh*',['+','*fn2-succ-res*','*fn2-succ-values-max*']),
  ('*fn2-succ-block*',['fn2-successor-block-fields','*fn2-succ-fields-max*','*fn2-succ-values-max*']),
  ('*fn2-idc-scratch-bytes*',['fn2-successor-scratch-bytes','*fn2-succ-octets-max*'])]:assert definition(g,'defconst',name)[2]==expr
 nodes=list(walk(definition(g,'defun','fn2-successor-schema-bounds')))
 for fn in ['fn2-run-layout-fields','fn2-run-layout-keys','fn2-successor-fold-args-max','fn2-succ-octets-total']:assert any(n and n[0]==fn for n in nodes)
 allg=[n for t in forms(g) for n in walk(read_sexp(t))]
 assert ['fn2-successor-schema-bounds','ids'] in allg
 assert ['fn2-successor-declared-schema-ids',['fn2-decl-rows',':schema',['w','state']],'*fn2-run-assembled-ids*'] in allg
 declared=list(walk(definition(g,'defun','fn2-successor-declared-schema-ids')))
 assert ['not',['fn2-decl-get',':internal','row']] in declared
 assert ['member-equal',['fn2-decl-get',':id','row'],'assembled'] in declared
 assert ['<=','*fn2-succ-fields-max*','32'] in allg and ['<','*fn2-succ-fresh*','256'] in allg
 allc=[n for t in forms(c) for n in walk(read_sexp(t))]
 assert ['<=','*fn2-idc-required-fields*','*fn2-idc-stride*'] in allc
 assert definition(c,'defconst','*fn2-idc-stride*')[2]=='*fn2-b-txn-field-rows*'
 assert definition(c,'defconst','*fn2-idc-required-fields*')[2]==['fn2-successor-required-fields','*fn2-succ-fields-max*','*fn2-succ-values-max*','*fn2-succ-slots*','*fn2-run-entry-rows*','*fn2-run-reader-fields*']
 required=list(walk(definition(pure,'defun','fn2-successor-required-fields')))
 assert ['nfix','entry-guard'] in required and any(n and n[0]=='max' for n in required)
 assert any(n and n[0]=='ceiling' for n in walk(definition(pure,'defun','fn2-successor-scratch-bytes')))
if __name__=='__main__':
 g=(ROOT/'books/successor-schema-geometry.lisp').read_text();c=(ROOT/'books/machines-c.lisp').read_text();p=(ROOT/'books/successor-workspace-geometry.lisp').read_text();check(g,c,p)
 mutations=[(g.replace('(not (fn2-decl-get :internal row))','t'),c,p),
  (g.replace('(member-equal (fn2-decl-get :id row) assembled)','t'),c,p),(g.replace('(defconst *fn2-succ-raw* *fn2-succ-fields-max*)','(defconst *fn2-succ-raw* 12)'),c,p),
  (g.replace('(fn2-run-layout-fields sid 0)','13',1),c,p),
  (g.replace('(fn2-succ-octets-total sid 0 nf)','0',1),c,p),
  (g.replace('(<= *fn2-succ-fields-max* 32)','t'),c,p),
  (g.replace('(< *fn2-succ-fresh* 256)','t'),c,p),
  (g,c.replace('(<= *fn2-idc-required-fields* *fn2-idc-stride*)','t'),p),
  (g,c.replace('*fn2-run-reader-fields*))','0))',1),p),
  (g,c,p.replace('(ceiling (nfix octets) *fn2-format-sector-size*)','1'))]
 for args in mutations:
  try:check(*args)
  except (AssertionError,StopIteration):continue
  raise AssertionError('weakened workspace survived')
 print(f'successor geometry source controls: {len(mutations)} rejected mutations; no execution/admission claim')

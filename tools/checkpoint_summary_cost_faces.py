#!/usr/bin/env python3
"""Declare exact existing cold primitive faces from their actual stobj ABI."""
from pathlib import Path
import lisp_rewrite as lr
TARGETS={
 'checkpoint-summary-adoption.lisp':[
  ('fn2-checkpoint-summary-apply-begin',32,':source :more'),
  ('fn2-checkpoint-summary-apply-preflight',0,':source :copy :occupied :bounds :more')],
 'checkpoint-summary-apply.lisp':[
  ('fn2-checkpoint-summary-apply-step',0,':source :coverage :bounds :directory :applied :more :state :exhausted')],
 'checkpoint-summary-authority-cold.lisp':[
  ('fn2-checkpoint-summary-authority-cold-begin',32,':source :more'),
  ('fn2-checkpoint-summary-authority-cold-step',4,':source :bounds :complete :more')]
}
def add_faces(source,targets):
    forms=lr.parse(source).forms
    output=[]
    for child,nbytes,answers in targets:
        if lr.match(f'(defcost {child}-op ?*body)',forms,deep=False): raise ValueError('face already declared '+child)
        fn=lr.match(f'(defun {child} ?args ?*body)',forms,deep=False)
        if len(fn)!=1:raise ValueError('missing actual child '+child)
        args=fn[0].captures['args'].items
        if any(not x.low.startswith('fn2-') for x in args):raise ValueError('unexpected scalar formal '+child)
        tables=' '.join('fn2-core-'+x.low[4:] for x in args)
        output.append(f'''(defcost {child}-op :child {child} :answers ({answers})
 :steps *fn2-work-stage* :bytes {nbytes} :descriptors 0
 :tables ({tables})
 :doc "Use the existing bounded cold primitive and its complete actual carrier footprint.")
''')
    return source+'''\n; machine-arms.lisp fn2-arms-op-face-events derives all bindings from the
; actual child's stobjs-in and mutable projection from stobjs-out. :tables
; below records every read/write carrier; it is not a substitute for that ABI.
'''+''.join(output)
if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]/'books'
    for name,targets in TARGETS.items():
        p=root/name;p.write_text(add_faces(p.read_text(),targets))

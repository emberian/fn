#!/usr/bin/env python3
"""Source transformation controls, not a physical-loader runtime test."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from cursor_physical_dispatch_rewrite import transform, transform_answers, transform_bundle_holds, READ_ERRORS

def test():
    text="""(:do (lc) (fn2-read-lookup (+ 1 (* 2 row-slot)) sid 4096)
      :accept () :case (((:ok) (:goto yes)) (:otherwise (:stop :bad))))
 (:do (nc) (fn2-read-next (* 2 row-slot) 4096)
 :accept () :case (((:more) (:yield)) (:otherwise (:stop :bad))))"""
    out,n=transform(text); assert n==2
    assert '(load-read (+ 1 (* 2 row-slot)))' in out
    assert '(load-read (* 2 row-slot))' in out
    again,n=transform(out); assert n==0 and again==out
    for bad in ['(:do (x) (fn2-read-next 0 4096))', '(:do (x) (fn2-read-next 0 4096) :case :bad)']:
        try: transform(bad)
        except ValueError: pass
        else: raise AssertionError('missing explicit routing accepted')
    untouched='(:do (x) (other-read 0) :case (((:miss) (:yield))))'
    assert transform(untouched)==(untouched,0)
    costs='(defcost fn2-read-lookup :answers (:ok :more :miss) :child real-read :doc "actual")'
    new,n=transform_answers(costs); assert n==1 and all(e in new for e in READ_ERRORS)
    assert transform_answers(new)==(new,0)
    holds='(:seek :cursor-row (:storage-window :while (lease :held)))'
    held,n=transform_bundle_holds(holds); assert n==1 and '(query-bundle :held)' in held
    assert transform_bundle_holds(held)==(held,0)
    assert transform_bundle_holds('(:storage-window :while (foreign :held))')[1]==0
    print('cursor physical dispatch rewrite: 7 controls pass')
if __name__=='__main__': test()

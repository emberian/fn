#!/usr/bin/env python3
"""Source controls for actual cold graph/empty boot binding; not admission."""
from pathlib import Path
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
    if isinstance(x,list):
        yield x
        for y in x:yield from walk(y)
def definition(s,name):
    return next(n for t in forms(s) for n in walk(read_sexp(t)) if n[:2]==['defun',name])
def check(bind,empty,pub,writer):
    source=list(walk(definition(bind,'fn2-checkpoint-bank-bind-source-p')))
    assert any(n and n[0]=='fn2-checkpoint-selected-source-current-p' for n in source)
    assert ['equal',['fn2-checkpoint-recovery-census-bound-mask','0','fn2-checkpoint-recovery-census'],['fn2-boot-config-anchor-checked-mask','fn2-boot-config']] in source
    canonical=list(walk(definition(bind,'fn2-checkpoint-bank-bind-canonical')))
    assert any(n and n[0]=='fn2-checkpoint-recovery-census-duplicate-p' for n in canonical)
    assert ['fn2-checkpoint-bank-cold-common-equal-p','0','c','probe','fn2-checkpoint-publication'] in canonical
    step=list(walk(definition(bind,'fn2-checkpoint-bank-bind-step')))
    assert ['head',['fn2-checkpoint-recovery-census-head','0','fn2-checkpoint-recovery-census']] in step
    assert ['fn2-checkpoint-bank-bind-base','head','fn2-checkpoint-publication'] in step
    assert not any(n and n[0] in ('bank0-valid','bank1-valid') for n in step)
    e=list(walk(definition(empty,'fn2-boot-bind-checkpoint-obligations')))
    for field,value in [('phase','*fn2-boot-state-epoch-result*'),('stage','3'),('event-ready','1'),('outcome','*fn2-outcome-done*'),('generation','ogen')]:
        assert ['equal',['fn2-machine-'+field,'id','fn2-core'],value] in e
    assert ['created',['fn2-machine-create','id','fn2-core']] in e
    assert ['equal',['fn2-boot-config-anchor-empty-mask','fn2-boot-config'],'15'] in e
    assert ['fn2-checkpoint-bank-empty-sources-p','0','fn2-checkpoint-publication'] in e
    for s in (pub,writer):
        assert '(fn2-checkpoint-bank-obligations-complete-p fn2-checkpoint-publication)' in s
        assert '(equal (fn2-checkpoint-publication-cold-pending-mask 0 fn2-checkpoint-publication) 0)' in s
    promote=definition(bind,'fn2-checkpoint-bank-promote-selected')
    assert not any(x in promote[2] for x in ('batch','event','checkpoint','ready'))
    nodes=list(walk(promote))
    assert ['fn2-checkpoint-bank-bind-base-current-p','0','c','fn2-checkpoint-publication'] in nodes
    assert ['installation-commit','batch'] in nodes and ['installation-event','event'] in nodes
if __name__=='__main__':
    b=(ROOT/'books/checkpoint-bank-bind.lisp').read_text();e=(ROOT/'books/checkpoint-bank-empty.lisp').read_text()
    p=(ROOT/'books/checkpoint-publication.lisp').read_text();w=(ROOT/'books/checkpoint-writer.lisp').read_text();check(b,e,p,w)
    from rewrite_checkpoint_bank_capture import rewrite_bind_base
    assert rewrite_bind_base(b)==b, 'base identity recipe must be idempotent'
    damaged=b.replace('(+ (* 48 head) 39)', '(+ (* 48 head) 38)',1)
    assert rewrite_bind_base(damaged)==b, 'full descriptor base identity repair'
    changes=[(b.replace('(fn2-checkpoint-selected-source-current-p ','(missing-selected ',1),e,p,w),
      (b.replace('(fn2-checkpoint-recovery-census-duplicate-p ','(missing-duplicate ',1),e,p,w),
      (b.replace('(fn2-checkpoint-bank-cold-common-equal-p 0 c probe fn2-checkpoint-publication)','t',1),e,p,w),
      (b,e.replace('(equal (fn2-machine-stage id fn2-core) 3)','t',1),p,w),
      (b,e.replace('(equal (fn2-machine-generation id fn2-core) ogen)','t',1),p,w),
      (b,e,p,w.replace('(equal (fn2-checkpoint-publication-cold-pending-mask 0 fn2-checkpoint-publication) 0)','t',1)),
      (b.replace('(installation-event event)','(installation-event batch)',1),e,p,w)]
    for args in changes:
        try:check(*args)
        except (AssertionError,StopIteration):continue
        raise AssertionError('weakened bank binding survived')
    print(f'bank binding source controls: {len(changes)} rejected mutations; no execution/admission claim')

#!/usr/bin/env python3
"""Syntax controls for full physical bank obligations, not admission."""
from pathlib import Path
from lisp_source import forms, read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
    if isinstance(x,list):
        yield x
        for y in x:yield from walk(y)
def definition(s,name):
    return next(f for t in forms(s) if (f:=read_sexp(t))[:2]==['defun',name])
def check(s):
    excluded=list(walk(definition(s,'fn2-checkpoint-bank-obligations-excludedp')))
    assert ['fn2-checkpoint-bank-obligations-complete-p','fn2-checkpoint-publication'] in excluded
    assert ['fn2-checkpoint-bank-obligations-exclude-loop','0','c','checkpoint','history','incarnation','fn2-checkpoint-publication'] in excluded
    loop=list(walk(definition(s,'fn2-checkpoint-bank-obligations-exclude-loop')))
    assert ['member-equal',['fn2-checkpoint-bank-obligation-state','role','fn2-checkpoint-publication'],['quote',['1','2']]] in loop
    assert ['>=',['nfix','role'],'6'] in loop
    for arg,field in [('c','1'),('checkpoint','2'),('history','3'),('incarnation','4')]:
        assert ['equal',arg,['fn2-checkpoint-bank-obligation-identity','role',field,'fn2-checkpoint-publication']] in loop
    complete=list(walk(definition(s,'fn2-checkpoint-bank-obligations-complete-p')))
    assert ['fn2-checkpoint-bank-obligations-records-p','0','fn2-checkpoint-publication'] in complete
    records=list(walk(definition(s,'fn2-checkpoint-bank-obligations-records-p')))
    assert ['<',['fn2-checkpoint-publication-cold-catalogi','slot','fn2-checkpoint-publication'],'4'] in records
    observe=list(walk(definition(s,'fn2-checkpoint-bank-obligations-observe')))
    assert ['<','i','32'] in observe
    assert ['floor',['-','i','2'],'5'] in observe
    fence=list(walk(definition(s,'fn2-checkpoint-bank-obligations-record-fence')))
    assert ['equal',['fn2-checkpoint-publication-phase','0','fn2-checkpoint-publication'],'*fn2-checkpoint-publication-phase-wait-fence*'] in fence
    assert ['replaced',['logand','live','bank-mask']] in fence
    assert ['cold-pending-mask','replaced'] in fence
    assert not any(n and n[0]=='cold-retired-mask' for n in fence)
    for name in ('snapshot','event','word'):
        reader=list(walk(definition(s,'fn2-checkpoint-bank-obligations-pending-'+name)))
        assert ['fn2-checkpoint-bank-obligations-pending-p','slot','fn2-checkpoint-publication'] in reader
    snapshot=list(walk(definition(s,'fn2-checkpoint-bank-obligations-pending-snapshot')))
    assert ['fn2-checkpoint-publication-cold-catalogi','slot','fn2-checkpoint-publication'] in snapshot
if __name__=='__main__':
    s=(ROOT/'books/checkpoint-bank-obligations-state.lisp').read_text();check(s)
    changes=[s.replace("'(1 2)","'(1)",1),s.replace('(>= (nfix role) 6)','(>= (nfix role) 2)',1),
             s.replace('(equal history (fn2-checkpoint-bank-obligation-identity role 3 fn2-checkpoint-publication))','t',1),
             s.replace('(fn2-checkpoint-bank-obligations-records-p 0 fn2-checkpoint-publication)','t',1),
             s.replace('(cold-pending-mask replaced)','(cold-retired-mask replaced)',1),
             s.replace('(fn2-checkpoint-publication-cold-catalogi slot fn2-checkpoint-publication)','slot',1)]
    for bad in changes:
        try:check(bad)
        except (AssertionError,StopIteration):continue
        raise AssertionError('weakened obligation survived')
    print(f'bank obligations source controls: {len(changes)} rejected mutations; no execution/admission claim')

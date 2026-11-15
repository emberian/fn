#!/usr/bin/env python3
"""Narrow source contracts for fence-owned bank debt; no ACL2 execution."""
from pathlib import Path
from lisp_source import forms, read_sexp
ROOT = Path(__file__).resolve().parents[1]
def definition(source, name):
    for text in forms(source):
        form = read_sexp(text)
        if form[:2] == ['defun', name]: return form
    raise AssertionError(name)
def walk(x):
    if isinstance(x, list):
        yield x
        for y in x: yield from walk(y)
def check(publication, writer):
    harvest = definition(publication, 'fn2-checkpoint-publication-harvest')[-1]
    bindings = harvest[1]
    success = next(v for n,v in bindings if n == 'success')
    assert ['equal','outcome','*fn2-outcome-done*'] in list(walk(success))
    assert ['equal','count',['if','fence','0','4096']] in list(walk(success))
    assert ['equal',['fn2-checkpoint-publication-debt-valid','0','fn2-checkpoint-publication'],'0'] in list(walk(success))
    capture = next(v for n,v in bindings if n == 'fn2-checkpoint-publication' and isinstance(v,list) and ['fn2-checkpoint-publication-record-bank','fn2-checkpoint-publication'] in v)
    assert capture == ['if',['and','fence','success'],['fn2-checkpoint-publication-record-bank','fn2-checkpoint-publication'],'fn2-checkpoint-publication']
    evidence = next(v for n,v in bindings if n == 'fn2-checkpoint-publication' and isinstance(v,list) and ['fn2-checkpoint-bank-evidence-record-fence','fn2-checkpoint-publication'] in v)
    assert evidence == ['if',['and','fence','success'],['fn2-checkpoint-bank-evidence-record-fence','fn2-checkpoint-publication'],'fn2-checkpoint-publication']
    assert bindings.index(['fn2-checkpoint-publication', evidence]) < bindings.index(['fn2-checkpoint-publication', capture])
    record = definition(publication, 'fn2-checkpoint-publication-record-bank')[-1]
    assert record[:3] == ['if',['or',['zp',['fn2-checkpoint-publication-rows','fn2-checkpoint-publication']],['not',['equal',['fn2-checkpoint-publication-debt-valid','0','fn2-checkpoint-publication'],'0']]],'fn2-checkpoint-publication']
    nodes = list(walk(record))
    for bank in (0,1):
        for field in ('candidate','checkpoint','history','incarnation',*(f'hash-{i}' for i in range(8))):
            assert [f'debt-{field}',[f'fn2-checkpoint-publication-bank{bank}-{field}','0','fn2-checkpoint-publication']] in nodes
            source = 'candidate' if field == 'candidate' else 'attempt-'+field
            assert [f'bank{bank}-{field}',[f'fn2-checkpoint-publication-{source}','0','fn2-checkpoint-publication']] in nodes
    begin = definition(publication,'fn2-checkpoint-publication-begin')[-1]
    debt = ['equal',['fn2-checkpoint-publication-debt-valid','0','fn2-checkpoint-publication'],'0']
    assert debt in list(walk(begin[1][0])), 'public BEGIN cannot bypass debt'
    # Writer-start is materialized inside its event macro, so inspect its exact
    # retained mutation boundary in addition to the lower BEGIN.
    gate = writer.index('(equal (fn2-checkpoint-publication-debt-valid 0 fn2-checkpoint-publication) 0)')
    rearm = writer.index('(fn2-checkpoint-publication-set-phase 0 *fn2-checkpoint-publication-phase-idle*')
    assert gate < rearm
    assert '(debt-valid 0)' not in publication, 'no caller-clear operation'
def main():
    p=(ROOT/'books/checkpoint-publication-state.lisp').read_text() + '\n' + (ROOT/'books/checkpoint-publication.lisp').read_text()
    w=(ROOT/'books/checkpoint-writer.lisp').read_text()
    check(p,w)
    from rewrite_checkpoint_bank_capture import rewrite
    assert rewrite(p) == p, 'capture generator must be idempotent'
    fixture = '(defun untouched (x) x)\n' + next(t for t in forms(p) if read_sexp(t)[:2] == ['defun','fn2-checkpoint-publication-record-bank'])
    damaged = fixture.replace('(bank1-hash-7 (fn2-checkpoint-publication-attempt-hash-7', '(bank1-hash-7 (fn2-checkpoint-publication-attempt-hash-6', 1)
    repaired = rewrite(damaged)
    assert repaired.startswith('(defun untouched (x) x)\n')
    assert repaired == rewrite(fixture), 'scoped regeneration must restore full identity'
    mutations=[(p.replace('(and fence success)','success',1),w),
      (p.replace('(debt-hash-7 (fn2-checkpoint-publication-bank0-hash-7','(debt-hash-7 (fn2-checkpoint-publication-bank0-hash-6',1),w),
      (p.replace('(bank1-hash-7 (fn2-checkpoint-publication-attempt-hash-7','(bank1-hash-7 (fn2-checkpoint-publication-attempt-hash-6',1),w),
      (p,w.replace('(equal (fn2-checkpoint-publication-debt-valid 0 fn2-checkpoint-publication) 0)','t',1)),
      (p.replace('(equal (fn2-checkpoint-publication-debt-valid 0 fn2-checkpoint-publication) 0)','t',1),w),
      (p.replace('(equal count (if fence 0 4096))','t',1),w)]
    for a,b in mutations:
        try: check(a,b)
        except (AssertionError,ValueError): pass
        else: raise AssertionError('mutation survived')
    print(f'checkpoint bank source controls: {len(mutations)} rejected mutations; no execution claim')
if __name__=='__main__':main()

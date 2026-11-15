#!/usr/bin/env python3
"""Narrow source mutation controls; no execution/admission authority."""
from pathlib import Path
from lisp_source import forms, read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
    if isinstance(x,list):
        yield x
        for y in x:yield from walk(y)
def definition(s,name):
    return next(n for t in forms(s) for n in walk(read_sexp(t)) if n[:2]==['defun',name])
def check(s):
    source=list(walk(definition(s,'fn2-checkpoint-bank-protection-source-p')))
    for term in [
        ['=',['fn2-alloc-freeze-phase','fn2-extents'],'4'],
        ['=',['fn2-alloc-epoch-begun','fn2-extents'],'0'],
        ['=',['fn2-checkpoint-publication-bank0-valid','0','fn2-checkpoint-publication'],'0'],
        ['=',['fn2-checkpoint-publication-bank1-valid','0','fn2-checkpoint-publication'],'0']]: assert term in source
    assert any(n and n[0]=='fn2-checkpoint-projection-current-p' for n in source)
    current=list(walk(definition(s,'fn2-checkpoint-bank-protection-current-p')))
    assert ['fn2-checkpoint-bank-protection-sources-p','0','fn2-checkpoint-bank-closures','fn2-checkpoint-bank-protection'] in current
    assert ['=',['fn2-checkpoint-bank-protection-bound-mask','0','fn2-checkpoint-bank-protection'],['fn2-checkpoint-publication-cold-bound-mask','0','fn2-checkpoint-publication']] in current
    step=definition(s,'fn2-checkpoint-bank-protection-step');nodes=list(walk(step))
    assert not any(x in step[2] for x in ['e','slot','holder','epoch','allocation','ready'])
    for term in [
      ['slot',['floor','at','n']],['e',['mod','at','n']],
      ['fn2-checkpoint-bank-closure-row-p','slot','e','fn2-checkpoint-bank-closures','fn2-checkpoint-publication'],
      ['=',['fn2-extents-epoch','e','fn2-extents'],'epoch'],
      ['=',['fn2-extents-counter','e','fn2-extents'],'allocation'],
      ['=',['fn2-extents-release-pending','e','fn2-extents'],'0'],
      ['fn2-checkpoint-bank-closure-edge','slot','e','fn2-extents','fn2-ops','fn2-checkpoints'],
      ['fn2-alloc-edge-add-transition','edge','holder','e','epoch','allocation',':recovery-base','fn2-extents','fn2-alloc-edges']]: assert term in nodes
    complete=list(walk(definition(s,'fn2-checkpoint-bank-protection-complete-p')))
    assert any(n and n[0]=='fn2-checkpoint-bank-protection-current-p' for n in complete)
    assert ['=',['fn2-checkpoint-bank-protection-cursor','0','fn2-checkpoint-bank-protection'],['fn2-checkpoint-bank-protection-total','0','fn2-checkpoint-bank-protection']] in complete
def check_geometry(s):
    body=definition(s,'fn2-checkpoint-bank-closure-edge')[-1]
    assert body==['+', ['fn2-checkpoint-source-edge','slot','e','fn2-extents','fn2-ops','fn2-checkpoints'],
                  ['*','2',['fn2-checkpoints-rows','fn2-checkpoints'],['fn2-extents-rows','fn2-extents']]]
if __name__=='__main__':
    s=(ROOT/'books/checkpoint-bank-protection.lisp').read_text();check(s)
    g=(ROOT/'books/checkpoint-bank-closure-edges.lisp').read_text();check_geometry(g)
    for old,new in [('(* 2 (fn2-checkpoints-rows','(* 1 (fn2-checkpoints-rows'),('(fn2-checkpoint-source-edge slot e','(fn2-checkpoint-source-edge 0 e'),('(fn2-checkpoint-source-edge slot e','(fn2-checkpoint-source-edge slot 0')]:
        assert old in g
        try:check_geometry(g.replace(old,new,1))
        except (AssertionError,StopIteration):continue
        raise AssertionError('overlapping cold region survived')
    mutations=[('(= (fn2-alloc-freeze-phase fn2-extents) 4)','t'),
      ('(= (fn2-extents-release-pending e fn2-extents) 0)','t'),
      ('(= (fn2-extents-counter e fn2-extents) allocation)','t'),
      ('(fn2-checkpoint-bank-closure-edge slot e','(fn2-checkpoint-bank-closure-edge 0 e'),
      ('(fn2-checkpoint-bank-protection-sources-p 0','(missing-sources 0'),
      ('(fn2-checkpoint-bank-closure-row-p slot e','(missing-row slot e'),
      ('(fn2-checkpoint-projection-current-p ','(missing-source '),
      ('(= (fn2-checkpoint-publication-bank1-valid 0 fn2-checkpoint-publication) 0)','t'),
      ('(fn2-alloc-edge-add-transition edge holder e epoch allocation :recovery-base','(fn2-alloc-edge-add-transition edge holder e epoch allocation :promised-read')]
    for old,new in mutations:
        assert old in s
        try:check(s.replace(old,new,1))
        except (AssertionError,StopIteration):continue
        raise AssertionError('weakened physical protection survived: '+old)
    print(f'bank protection source controls: {len(mutations)} protection + 3 geometry rejected mutations; no execution/admission claim')

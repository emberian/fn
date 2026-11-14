#!/usr/bin/env python3
"""Syntax controls for the actual bounded teardown admission frontier."""
from pathlib import Path
from lisp_source import forms, read_sexp
ROOT=Path(__file__).resolve().parents[1]
def definition(source,name):
    for text in forms(source):
        f=read_sexp(text)
        if f[:2]==['defun',name]:return f
    raise AssertionError(name)
def walk(x):
    if isinstance(x,list):
        yield x
        for y in x:yield from walk(y)
def check(source,arms):
    owner=list(walk(definition(source,'fn2-checkpoint-teardown-ownerp')[-1]))
    for name,value in [('fn2-checkpoint-lifecycle-phase','*fn2-checkpoint-lifecycle-phase-complete*'),
                       ('fn2-csnapshot-phase','*fn2-csnapshot-phase-idle*'),
                       ('fn2-checkpoint-publication-phase','*fn2-checkpoint-publication-phase-complete*'),
                       ('fn2-checkpoint-publication-bundle-released','1')]:
        table={'fn2-checkpoint-lifecycle-phase':'fn2-checkpoint-lifecycle','fn2-csnapshot-phase':'fn2-csnapshot'}.get(name,'fn2-checkpoint-publication')
        assert ['equal',[name,'0',table],value] in owner
    assert ['equal',['fn2-alloc-freeze-token','fn2-extents'],'0'] in owner
    assert ['fn2-checkpoint-teardown-hash-p','t','0','c','fn2-checkpoint-publication','fn2-checkpoint-bytes'] in owner
    assert ['fn2-checkpoint-teardown-bank-excludedp','c','fn2-checkpoint-publication'] in owner
    eligible=list(walk(definition(source,'fn2-checkpoint-teardown-eligiblep')[-1]))
    for field in ['installed-root','recovery-base','prepared-successor','reservation','obligation','recovery-candidate','release-pending']:
        assert ['equal',[f'fn2-extents-{field}','e','fn2-extents'],'0'] in eligible
    assert ['<',['fn2-checkpoint-construction-role','e','fn2-checkpoint-construction'],'6'] in eligible
    assert ['fn2-alloc-edge-matchesp','edge','checkpoint','e','epoch','counter',':selectable-checkpoint','fn2-alloc-edges'] in eligible
    assert ['equal',['fn2-extents-selectable-checkpoint','e','fn2-extents'],['+','1',['fn2-checkpoint-teardown-root-count','0','c','e','epoch','counter','checkpoint','fn2-extents','fn2-ops','fn2-alloc-edges']]] in eligible
    scan=list(walk(definition(source,'fn2-checkpoint-teardown-inspect-children')[-1]))
    assert ['mv',':eligible','cursor','cursor',['fn2-extents-epoch','cursor','fn2-extents'],['fn2-extents-counter','cursor','fn2-extents']] in scan
    assert ['mv',':more',['+','1','cursor'],'0','0','0'] in scan
    assert not any(n and isinstance(n[0],str) and (n[0].startswith('fn2-alloc-edge-drop') or n[0]=='fn2-retirement-submit') for n in walk(definition(source,'fn2-checkpoint-teardown-inspect-children')))
    assert '(fn2-retirement-submit ' not in arms, 'no submit before async intent barrier exists'
    release=arms.index('(:snapshot-release :on-refusal')
    begin=arms.index('(:next :teardown-begin)',release)
    inspect=arms.index('(fn2-checkpoint-teardown-inspect-op ')
    assert release<begin<inspect
    assert '(:teardown-barrier (:set (stopped 1)) (:stop :checkpoint))' in arms
    assert '(debt-valid 0)' not in source and 'state-free*' not in source
if __name__=='__main__':
    p=(ROOT/'books/checkpoint-teardown.lisp').read_text();a=(ROOT/'books/checkpoint-master-arms.lisp').read_text()
    check(p,a)
    mutations=[]
    for field in ['installed-root','recovery-base','prepared-successor','reservation','obligation','recovery-candidate']:
        mutations.append((p.replace(f'(equal (fn2-extents-{field} e fn2-extents) 0)','t',1),a))
    mutations.extend([(p.replace('(fn2-checkpoint-teardown-hash-p t 0 c fn2-checkpoint-publication fn2-checkpoint-bytes)','t',1),a),
      (p.replace('(< (fn2-checkpoint-construction-role e fn2-checkpoint-construction) 6)','t',1),a),
      (p,a.replace('(:next :teardown-begin)','(:next :done)',1))])
    for x,y in mutations:
        try:check(x,y)
        except (AssertionError,ValueError):pass
        else:raise AssertionError('mutation survived')
    print(f'checkpoint teardown source controls: {len(mutations)} rejected mutations; no runtime claim')

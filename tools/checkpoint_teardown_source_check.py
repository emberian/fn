#!/usr/bin/env python3
"""Syntax controls for the actual bounded teardown admission frontier."""
from pathlib import Path
from lisp_source import forms, read_sexp
ROOT=Path(__file__).resolve().parents[1]
def definition(source,name):
    for text in forms(source):
        f=read_sexp(text)
        for node in walk(f):
            if node[:2]==['defun',name]:return node
    raise AssertionError(name)
def walk(x):
    if isinstance(x,list):
        yield x
        for y in x:yield from walk(y)
def check(source,arms,state):
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
    eligible=list(walk(definition(source,'fn2-checkpoint-teardown-eligiblep')[-1])) + list(walk(definition(source,'fn2-checkpoint-teardown-ownedp')[-1])) + list(walk(definition(source,'fn2-checkpoint-teardown-unsharedp')[-1]))
    for field in ['installed-root','recovery-base','prepared-successor','reservation','obligation','recovery-candidate','release-pending']:
        assert ['equal',[f'fn2-extents-{field}','e','fn2-extents'],'0'] in eligible
    assert ['<',['fn2-checkpoint-construction-role','e','fn2-checkpoint-construction'],'6'] in eligible
    assert ['fn2-alloc-edge-matchesp','edge','checkpoint','e','epoch','counter',':selectable-checkpoint','fn2-alloc-edges'] in eligible
    assert ['equal',['fn2-extents-selectable-checkpoint','e','fn2-extents'],['+','1',['fn2-checkpoint-teardown-root-count','0','c','e','epoch','counter','checkpoint','fn2-extents','fn2-ops','fn2-alloc-edges']]] in eligible
    scan=list(walk(definition(source,'fn2-checkpoint-teardown-inspect-children')[-1]))
    assert ['mv',':eligible','cursor','cursor',['fn2-extents-epoch','cursor','fn2-extents'],['fn2-extents-counter','cursor','fn2-extents']] in scan
    assert ['mv',':more',['+','1','cursor'],'0','0','0'] in scan
    assert not any(n and isinstance(n[0],str) and (n[0].startswith('fn2-alloc-edge-drop') or n[0]=='fn2-retirement-submit') for n in walk(definition(source,'fn2-checkpoint-teardown-inspect-children')))
    allnodes=[n for text in forms(source) for n in walk(read_sexp(text))]
    for name,args in [('fn2-checkpoint-teardown-submit',['token','kind','slot','gen','cursor','epoch','counter','fn2-core']),
                      ('fn2-checkpoint-teardown-poll',['kind','slot','gen','fn2-core'])]:
        assert ['fn2-core-preserves',name,args,':position','4',':rows','nil'] in allnodes
        cost=next(n for n in allnodes if n[:2]==['defcost',name])
        tables=cost[cost.index(':tables')+1]
        assert 'fn2-core-checkpoint-future' in tables and 'fn2-core-checkpoint-future-windows' in tables
    submit=definition(source,'fn2-checkpoint-teardown-submit')[-1]
    bindings=submit[1]
    assert bindings[1] == [['unless','eligible'],['mv',':retained',':retained','0','0','fn2-core']]
    assert bindings[2][1] == ['fn2-retirement-submit','cursor','epoch','counter','kind','slot','gen','fn2-core']
    assert ['fn2-checkpoint-teardown-eligiblep',['fn2-checkpoint-publication-debt-candidate','0','fn2-checkpoint-publication'],'cursor','fn2-checkpoints','fn2-checkpoint-construction','fn2-extents','fn2-ops','fn2-alloc-edges'] in list(walk(bindings[0]))
    assert ['if',['member-eq','code',["quote",[':ok',':uncertain']]],':ok','code'] in list(walk(submit))
    poll=definition(source,'fn2-checkpoint-teardown-poll')[-1]
    assert poll[2] == ['fn2-retirement-poll','kind','slot','gen','fn2-core']
    assert ['if',['member-eq','outcome',["quote",[':accepted',':refused']]],':ok','outcome'] in list(walk(poll))
    drop=list(walk(definition(source,'fn2-checkpoint-teardown-drop-children')[-1]))
    assert ['equal',['fn2-extents-state','cursor','fn2-extents'],'*fn2-extent-state-retire-pending*'] in drop
    assert ['equal',['fn2-extents-retirement','cursor','fn2-extents'],'batch'] in drop
    assert ['fn2-alloc-edge-drop','edge',['fn2-checkpoints-checkpoint','c','fn2-checkpoints'],'cursor','epoch','counter',':selectable-checkpoint','fn2-extents','fn2-alloc-edges'] in drop
    armforms=[read_sexp(t) for t in forms(arms)]
    declaration=next(f for f in armforms if f[:2]==['defmachine-arms','fn2-checkpoint-master'])
    amap={a[0]:a for a in declaration[declaration.index(':arms')+1]}
    for tag in (':teardown-submit',':teardown-wait',':teardown-drop'):
        assert amap[tag][-1][:2] == [':if',['and',['natp','budget'],['<','0','budget']]], 'zero budget must have no effects'
    wait=list(walk(amap[':teardown-wait']))
    assert ['equal','batch','row-batch'] in wait and ['equal','event','row-event'] in wait
    assert [':release',[':storage-window']] in wait
    assert [':acquire',[':storage-window']] in list(walk(amap[':teardown-submit']))
    stateforms=[read_sexp(t) for t in forms(state)]
    machine=next(f for f in stateforms if f[:2]==['defmachine','fn2-checkpoint-master'])
    holds={h[0]:h[1:] for h in machine[machine.index(':holds')+1]}
    for tag in (':teardown-wait',':teardown-holding-uncertain'):
        assert holds[tag] == [':storage-window']
    for tag in (':teardown-source',':teardown-submit',':teardown-drop',':teardown-retained',':teardown-uncertain'):
        assert tag not in holds
    release=arms.index('(:snapshot-release :on-refusal')
    begin=arms.index('(:next :teardown-begin)',release)
    inspect=arms.index('(fn2-checkpoint-teardown-inspect-op ')
    assert release<begin<inspect
    assert '(:teardown-holding-uncertain (:set (stopped 1)) (:stop :checkpoint))' in arms
    assert '(debt-valid 0)' not in source and 'state-free*' not in source
if __name__=='__main__':
    p=(ROOT/'books/checkpoint-teardown.lisp').read_text();a=(ROOT/'books/checkpoint-master-arms.lisp').read_text()
    state=(ROOT/'books/checkpoint-master-state.lisp').read_text()
    check(p,a,state)
    mutations=[]
    for field in ['installed-root','recovery-base','prepared-successor','reservation','obligation','recovery-candidate']:
        mutations.append((p.replace(f'(equal (fn2-extents-{field} e fn2-extents) 0)','t',1),a))
    mutations.extend([(p.replace('(fn2-checkpoint-teardown-hash-p t 0 c fn2-checkpoint-publication fn2-checkpoint-bytes)','t',1),a),
      (p.replace('(< (fn2-checkpoint-construction-role e fn2-checkpoint-construction) 6)','t',1),a),
      (p,a.replace('(:next :teardown-begin)','(:next :done)',1)),
      (p.replace('(equal (fn2-extents-retirement cursor fn2-extents) batch)','t',1),a),
      (p,a[:a.index('  (:teardown-wait')]+a[a.index('  (:teardown-wait'):].replace('(equal event row-event)','t',1)),
      (p.replace('((unless eligible) (mv :retained :retained 0 0 fn2-core))','((unless t) (mv :retained :retained 0 0 fn2-core))',1),a)])
    for x,y in mutations:
        try:check(x,y,state)
        except (AssertionError,ValueError):pass
        else:raise AssertionError('mutation survived')
    missing= p.replace('fn2-core-retirement-control fn2-core-checkpoint-future fn2-core-checkpoint-future-windows fn2-core-commit-io','fn2-core-retirement-control fn2-core-commit-io',1)
    try:check(missing,a,state)
    except (AssertionError,ValueError):pass
    else:raise AssertionError('missing nested future footprint survived')
    damaged=state.replace('(:teardown-wait :storage-window)','(:teardown-wait)',1)
    try:check(p,a,damaged)
    except (AssertionError,ValueError):pass
    else:raise AssertionError('missing staging hold survived')
    print(f'checkpoint teardown source controls: {len(mutations)+2} rejected mutations; no runtime claim')

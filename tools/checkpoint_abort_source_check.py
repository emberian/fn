#!/usr/bin/env python3
"""Narrow abort-authority source controls; no ACL2 or constructor simulation."""
from pathlib import Path
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk
ROOT=Path(__file__).resolve().parents[1]
def definition(source,name):
    for text in forms(source):
        for form in walk(read_sexp(text)):
            if len(form)>2 and form[:2]==['defun',name]:return form
    raise AssertionError('missing '+name)
def check(source):
    base=definition(source,'fn2-checkpoint-master-preconstructionp')
    terms=list(walk(base))
    for required in [
      ['equal',['fn2-checkpoints-state','c','fn2-checkpoints'],'*fn2-checkpoint-state-free*'],
      ['equal',['fn2-checkpoint-build-phase','0','fn2-checkpoint-build'],'*fn2-checkpoint-build-phase-idle*'],
      ['equal',['fn2-checkpoint-root1-token','0','fn2-checkpoint-root1'],'0'],
      ['equal',['fn2-checkpoint-future-token','0','fn2-checkpoint-future'],'0'],
      ['member-equal',['fn2-checkpoint-master-phase','0','fn2-checkpoint-master'],['list','*fn2-checkpoint-master-state-abort-snapshot*','*fn2-checkpoint-master-state-abort-working*','*fn2-checkpoint-master-state-abort-complete*']]]:
        assert required in terms
    assert any(x and x[0]=='fn2-checkpoint-future-no-loansp' for x in terms)
    step=definition(source,'fn2-checkpoint-master-abort-step-children')
    nodes=list(walk(step))
    assert ['and',['natp','budget'],['<','0','budget']] in nodes
    assert ['equal',['fn2-checkpoint-master-phase','0','fn2-checkpoint-master'],'*fn2-checkpoint-master-state-abort-working*'] in nodes
    assert ['equal',['fn2-csnapshot-phase','0','fn2-csnapshot'],'*fn2-csnapshot-phase-idle*'] in nodes
    assert ['equal',['fn2-alloc-freeze-token','fn2-extents'],'0'] in nodes
    calls=[x for x in nodes if x and x[0]=='fn2-checkpoint-working-release-step']
    assert len(calls)==1
    assert not any(isinstance(x[0],str) and x[0].startswith(('fn2-alloc-cancel','fn2-alloc-retire','fn2-alloc-release')) for x in nodes if x)
    complete=list(walk(definition(source,'fn2-checkpoint-master-abort-complete-children')))
    for carrier in ['fn2-checkpoint-root1','fn2-checkpoint-future']:
        assert ['equal',[carrier+'-reserved','0',carrier],'0'] in complete
    budget=definition(source,'fn2-checkpoint-directory-budget')
    assert budget[-1]==['+','1',['ceiling',['nfix','extents'],'*fn2-checkpoint-allocation-records-per-ticket*']]
    return True
if __name__=='__main__':
    source=(ROOT/'books/checkpoint-master-abort.lisp').read_text()
    check(source)
    mutations=[source.replace('*fn2-checkpoint-state-free*','*fn2-checkpoint-state-building*'),
      source.replace('*fn2-checkpoint-build-phase-idle*','*fn2-checkpoint-build-phase-ready*'),
      source.replace('*fn2-checkpoint-master-state-abort-working*','*fn2-checkpoint-master-state-root1-source*'),
      source.replace('(fn2-checkpoint-future-token 0 fn2-checkpoint-future) 0','(fn2-checkpoint-future-token 0 fn2-checkpoint-future) 1'),
      source.replace('(fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-idle*','(fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*'),
      source.replace('fn2-checkpoint-working-release-step budget','fn2-alloc-cancel budget'),
      source.replace('*fn2-checkpoint-allocation-records-per-ticket*','25')]
    for bad in mutations:
        try:check(bad)
        except AssertionError:pass
        else:raise AssertionError('abort mutation escaped source authority check')
    print('abort source authority controls: 7 rejected mutations; no execution claim')

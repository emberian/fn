#!/usr/bin/env python3
"""Narrow source dispatch controls, not ACL2 admission or execution."""
from pathlib import Path
from lisp_source import forms, read_sexp
ROOT = Path(__file__).resolve().parents[1]
def walk(x):
    if isinstance(x, list):
        yield x
        for y in x:
            yield from walk(y)
def declaration(source):
    return next(read_sexp(s) for s in forms(source)
                if read_sexp(s)[:3] == ['defmachine-arms', 'fn2-checkpoint-master', ':declare'])
def check(source):
    form = declaration(source)
    arms = {a[0]: a for a in form[form.index(':arms') + 1]}
    state = next(read_sexp(s) for s in forms((ROOT/'books/checkpoint-master-state.lisp').read_text())
                 if read_sexp(s)[:2] == ['defmachine','fn2-checkpoint-master'])
    assert set(arms) == set(state[state.index(':states')+1]), 'every retained phase needs one actual arm'
    for phase, op in [(':root1-read', 'fn2-checkpoint-root1-read-op'),
                      (':events-read', 'fn2-checkpoint-events-read')]:
        arm = arms[phase]
        branch = next(x for x in arm if isinstance(x,list) and x and x[0] == ':if')
        assert branch[1] == ['and', ['natp','budget'], ['<','0','budget']]
        assert branch[3] == [[':yield']]
        issue = next(x for x in walk(branch[2]) if x and x[0] == ':issue')
        assert issue[1][0] == op
        assert not any(x and x[0] == ':do' for x in walk(branch[2]))
    take = [x for x in walk(form) if x and x[0] == 'fn2-checkpoint-page-take']
    assert take == [['fn2-checkpoint-page-take']], 'all producers share one destination-derived transfer'
    assert [':wake-row','target'] in list(walk(arms[':page-take']))
    assert [':charge',':steps','*fn2-work-small*'] in list(walk(arms[':page-take']))
    assert [':next',':page-wait'] in list(walk(arms[':page-take']))
    for phase, op in [(':descriptor-begin','fn2-checkpoint-build-begin-op'),
                      (':plan-count','fn2-checkpoint-plan-count-op'),
                      (':freeze','fn2-checkpoint-plan-freeze')]:
        assert any(x and x[0] == op for x in walk(arms[phase]))
    consume = arms[':page-consume']
    for op in ['fn2-checkpoint-root1-consume-op','fn2-checkpoint-events-consume',
               'fn2-checkpoint-map-consume-page-op','fn2-checkpoint-build-consume-op']:
        assert any(x and x[0] == op for x in walk(consume))
    assert [':read-result',[':wake']] in form[form.index(':observes')+1]
    return True
if __name__ == '__main__':
    source = (ROOT/'books/checkpoint-master-arms.lisp').read_text()
    check(source)
    mutations = [source.replace('(< 0 budget)','(<= 0 budget)',1),
                 source.replace('(:wake-row target)','(:wake-row id)',1),
                 source.replace('fn2-checkpoint-build-consume-op','fn2-checkpoint-build-ready-op',1)]
    for bad in mutations:
        try:
            check(bad)
        except (AssertionError,StopIteration):
            pass
        else:
            raise AssertionError('mutation escaped dispatch contract')
    print('checkpoint master source controls: 3 rejected mutations; no runtime claim')

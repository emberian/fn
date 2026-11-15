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
    for phase in [':allocation-wait', ':installation-wait']:
        assert ['and', ['equal','batch','row-batch'], ['equal','event','row-event']] in list(walk(arms[phase])), 'settlement must match the actual retained admission'
    for phase in [':barrier-begin', ':installation-begin']:
        assert any(x and x[0] == 'fn2-checkpoint-master-ready-op' for x in walk(arms[phase]))
    assert ['fn2-checkpoint-lifecycle-begin','candidate','row-token','*fn2-checkpoint-master-kind*','id','row-generation'] in list(walk(arms[':barrier-begin']))
    assert ['fn2-checkpoint-lifecycle-step'] in list(walk(arms[':barrier-source']))
    assert ['fn2-checkpoint-lifecycle-step'] in list(walk(arms[':retention-source']))
    assert ['fn2-checkpoint-lifecycle-thaw'] in list(walk(arms[':thaw']))
    assert ['fn2-checkpoint-events-rearm'] in list(walk(arms[':event-rearm']))
    take_do = next(x for x in walk(arms[':page-take']) if x and x[0] == ':do')
    assert take_do[take_do.index(':effects')+1] == [[':release',[':storage-window']]]
    accept_do = next(x for x in walk(arms[':page-accept-return']) if x and x[0] == ':do')
    assert accept_do[2] == ['fn2-checkpoint-page-accept-return','*fn2-checkpoint-master-kind*','id','row-generation']
    assert accept_do[accept_do.index(':effects')+1] == [[':acquire',[':storage-window']]]
    holds = {x[0]:x[1:] for x in state[state.index(':holds')+1]}
    for phase in [':snapshot-begin',':snapshot-poll',':reserve',':abort-empty']:
        assert holds.get(phase,[]) == [], 'closing/drain and unsuccessful TRY own no working bundle'
    assert [':next',':snapshot-begin'] in list(walk(arms[':catalog']))
    assert [':next',':reserve'] in list(walk(arms[':snapshot-poll']))
    assert [':next',':directory'] in list(walk(arms[':workspaces']))
    assert ['fn2-checkpoint-root1-reserve-op','row-candidate','row-token','*fn2-checkpoint-master-kind*','id','row-generation'] in list(walk(arms[':reserve']))
    assert ['fn2-checkpoint-master-abort-empty-ready-op'] in list(walk(arms[':abort-empty']))
    assert any(x and x[0] == 'fn2-csnapshot-release' for x in walk(arms[':abort-empty']))
    assert not any(x and x[0] in (':park',':wait',':yield') for x in walk(arms[':abort-empty']))
    debt_updates = [(tag,pair) for tag,arm in arms.items() for node in walk(arm) if node and node[0] == ':set' for pair in node[1:] if pair[0] == 'retirement-seen']
    assert debt_updates == [(':done',['retirement-seen','row-attempt-retirement'])]
    for phase in [':page-wait',':page-accept-return',':loan-uncertain']:
        assert holds[phase] == [':storage-window']
    for phase in [':page-take',':page-consume',':uncertain',':release-complete']:
        assert holds[phase] == [':storage-window',':storage-window']
    assert arms[':cancel-ledger'][-1][:2] == [':if',['and',['natp','budget'],['<','0','budget']]], 'ledger cancellation must yield at zero budget'
    parked = {tag for tag,arm in arms.items() if arm[1:] == [[':idle']]}
    assert parked == {':disabled', ':admission-refused'}, 'no productive phase may be a parked placeholder'
    assert ['fn2-checkpoint-master-release-complete-op','row-token','*fn2-checkpoint-master-kind*','id','row-generation'] in list(walk(arms[':release-complete']))
    assert [':read-result',[':wake']] in form[form.index(':observes')+1]
    return True
def check_creation(index, callbacks, state_source):
    index_forms = [s.strip() for s in forms(index)]
    declaration = '(include-book "checkpoint-master-kind")'
    assert declaration in index_forms
    assert index_forms.index(declaration) < index_forms.index('(fn2-machine-index-events)')
    callback_forms = [read_sexp(s) for s in forms(callbacks)]
    for name in ['fn2-checkpoint-page-worker-events', 'fn2-checkpoint-writer-events', 'fn2-event-producer-rearm-events', 'fn2-checkpoint-master-events']:
        assert [name] in callback_forms
    assert callback_forms.index(['fn2-checkpoint-writer-events']) < callback_forms.index(['fn2-event-producer-rearm-events']) < callback_forms.index(['fn2-checkpoint-master-events'])
    state_forms = [read_sexp(s) for s in forms(state_source)]
    assert ['defconst', '*fn2-checkpoint-activation-qualified*', 'nil'] in state_forms
    state = next(x for x in state_forms if x[:2] == ['defmachine','fn2-checkpoint-master'])
    assert state[state.index(':genesis')+1] == [[':charge',':steps','*fn2-work-small*',':runnable','t']]
    return True

if __name__ == '__main__':
    source = (ROOT/'books/checkpoint-master-arms.lisp').read_text()
    check(source)
    index = (ROOT/'books/assembly-index.lisp').read_text()
    callbacks = (ROOT/'books/assembly-callbacks-c.lisp').read_text()
    state = (ROOT/'books/checkpoint-master-state.lisp').read_text()
    check_creation(index, callbacks, state)
    for bad in [state.replace('(defconst *fn2-checkpoint-activation-qualified* nil)', '(defconst *fn2-checkpoint-activation-qualified* t)'), state.replace(':runnable t', ':runnable nil')]:
        try:
            check_creation(index, callbacks, bad)
        except AssertionError:
            pass
        else:
            raise AssertionError('mutation escaped creation/gate contract')
    mutations = [source.replace('(< 0 budget)','(<= 0 budget)',1),
                 source.replace('(:wake-row target)','(:wake-row id)',1),
                 source.replace('fn2-checkpoint-build-consume-op','fn2-checkpoint-build-ready-op',1),
                 source.replace('(equal event row-event)','(equal event event)',1),
                 source.replace('fn2-checkpoint-master-ready-op','fn2-checkpoint-build-ready-op',1),
                 source.replace('(:next :snapshot-begin)','(:next :reserve)',1),
                 source.replace('(retirement-seen row-attempt-retirement)','(retirement-seen 0)',1)]
    for bad in mutations:
        try:
            check(bad)
        except (AssertionError,StopIteration):
            pass
        else:
            raise AssertionError('mutation escaped dispatch contract')
    print('checkpoint master source controls: 9 rejected mutations; no runtime claim')

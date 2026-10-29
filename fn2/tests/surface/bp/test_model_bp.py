"""BP S: fixed per-verb witnesses, then generated carry/obligation/route transitions (bp_model).

One fresh store and FNWF journal per example (the developer image, FN_NATIVE_DEVELOPER_HOST), no node
running, at most five works on one peer EID, one loopback boundary whose contact nothing listens on.
Every CLI has a 20 s timeout. After every step the whole carry list (every work's pin and hold) is read
back, with the touched work's status line, and the boundaries' peer-list lines after a boundary or route
verb (live on fn1: 5 examples of 30 steps in about 3 minutes). Test-work bounds,
not product ceilings; the enclosing surface child supplies the hard wall bound.
"""
from contextlib import ExitStack
import os
import unittest

from fn2.tests.model.bp_model import PEER, BpModel
from fn2.tests.surface import SurfaceCase, owned_ports, serving
from fn2.tests.surface.live_evidence import capture_step, json_value, record_failure, run_live_machine

ARTICLES = 5


class BpTarget:
    @owned_ports
    def __init__(self, case):
        from tests.native_harness import free_port, native_image, scratch
        self.adjudication_target = os.environ.get('FN2_SURFACE_TARGET', 'fn2')
        self.image = native_image('FN_NATIVE_DEVELOPER_HOST')
        self.tmp = scratch(case, 'fn2-bp-s-')
        self.store, self.journal, self.config = self.tmp / 'store', self.tmp / 'workflow', self.tmp / 'fn.toml'
        self.config.write_text(f'[store]\npath = "{self.store}"\n', encoding='ascii')
        self.listen, self.dead = free_port(), free_port()
        self.attempts = 0
        steps = [('store', self.store, 'init', 'fn.test')]
        for k in range(1, ARTICLES + 1):
            ident = f'<bp-s-{k}@surface.invalid>'
            payload = self.tmp / f'article-{k}'
            payload.write_text(f'Message-ID: {ident}\r\nNewsgroups: fn.test\r\n\r\nbody {k}\r\n', encoding='ascii')
            steps.append(('store', self.store, 'post', ident, payload, '-', '-', 'fn.test'))
        steps.append(('app-journal', 'workflow-init', self.store, self.journal, 'dtn://fn-a/', PEER, 'policy-a',
                      'authority-a', '3600000', 'incarnation-a', 'authorization-a'))
        for words in steps:
            reply = self.fn(*words)
            if reply['exit']:
                record_failure(case, 'bp', rule='fixture', request=[str(w) for w in words], reply=reply,
                               verdict=dict(ok=False, detail='fixture setup'), trace=[])
            case.assertEqual(reply['exit'], 0, (words, reply))

    def fn(self, *words):
        from tests.native_harness import environment, run
        result = run([self.image, '--fn', *[str(w) for w in words]], env=environment(None), timeout=20)
        return dict(exit=result.returncode, text=(result.stdout + result.stderr).decode('ascii', 'replace'))

    def call(self, request):
        v, a = request.verb, list(request.args)
        if v.startswith('carry '):
            sub = v.split()[1]
            words = ['drop', a[0], '--abandon', *a[1:]] if sub == 'abandon' else [sub, *a]
            return self.fn('operator', self.config, 'carry', self.journal, *words)
        if v.startswith('bp-obligation '):
            sub = v.split()[1]
            if sub == 'request':
                return self.fn('bp-obligation', 'request', self.store, self.journal, a[0], a[1],
                               self.tmp / 'fnbs', 'dtn://fn-a/', '127.0.0.1', self.dead)
            if sub == 'receipt':
                receipt = self.tmp / 'receipt.adu'
                receipt.write_bytes(b'unsigned')
                return self.fn('bp-obligation', 'receipt', self.store, self.journal, receipt, '2', '0', 'unsigned-lab')
            return self.fn('bp-obligation', sub, self.store, self.journal, *a)
        return self.fn('operator', self.config, *request.words)

    def enqueue(self, serial, work, msgid):
        return self.fn('app-journal', 'workflow-enqueue', self.store, self.journal, str(serial), '0', work, msgid,
                       'forward-' + work, PEER, 'policy-a', 'terms-a')

    def peer_list(self):
        return self.fn('operator', self.config, 'peer', 'list')


class Exercise:
    def __init__(self, case, target, trace=None):
        self.case, self.target = case, target
        self.model = BpModel(fn1=getattr(target, 'adjudication_target', 'fake') == 'fn1')
        self.trace = trace if trace is not None else []
        self.checked_verbs, self.serial, self.attempt = set(), 0, 0

    def require(self, good, *, rule, request, reply, detail):
        if not good:
            record_failure(self.case, 'bp', rule=rule, request=request, reply=reply,
                           verdict=dict(ok=False, detail=detail), trace=self.trace)
        self.case.assertTrue(good, (detail, request, reply))

    @capture_step(None, 'bp', request=lambda self, verb, *args, **kwargs: dict(verb=verb, args=args))
    def step(self, verb, *args, observe=True):
        expected = self.model.rule(verb, *args)
        result = self.target.call(expected.request)
        self.trace.append(dict(request=expected.request, reply=result))
        target = getattr(self.target, 'adjudication_target', 'fake')
        recorded = expected.recorded_difference(result, target)
        problem = expected.check(result)
        if recorded is None:
            self.require(problem is None, rule=verb, request=expected.request, reply=result, detail=problem)
        recorded = expected.update(result, target)
        self.checked_verbs.add((verb, expected.exit not in (0, 7) and expected.argument_class != 'attempted'))
        if recorded is not None and hasattr(self.case, 'evidence'):
            self.case.evidence.setdefault('recorded_differences', []).append(json_value(dict(recorded, step=len(self.trace))))
        if observe:
            self.observe(work=args[0] if args and args[0] in self.model.works else None,
                         boundaries=verb.startswith(('bp-boundary', 'bp-route')))
        return result

    def request(self, work):
        self.attempt += 1
        return self.step('bp-obligation request', work, f'attempt-{self.attempt}')

    @capture_step(None, 'bp')
    def enqueue(self, work=None):
        self.serial += 1
        work = work or f'work-{self.serial}'
        msgid = f'<bp-s-{len(self.model.works) + 1}@surface.invalid>'
        duplicate = work in self.model.works
        # The producer's sequence word is the journal's next enqueue (accepted ones only).
        reply = self.target.enqueue(len(self.model.works) + 1, work, msgid)
        self.trace.append(dict(enqueue=work, msgid=msgid, reply=reply))
        self.require(reply['exit'] == (1 if duplicate else 0), rule='enqueue', request=work, reply=reply,
                     detail='the fixture producer enqueues a new work and refuses a duplicate work id')
        if not duplicate:
            self.model.enqueued(work, msgid)
        self.observe()
        return work

    @capture_step(None, 'bp')
    def observe(self, work=None, boundaries=True):
        """Every work's pin and hold (carry list) after every step; the touched work's status line; the
        boundaries' peer-list lines after a boundary or route verb."""
        self.step('carry list', observe=False)
        if work is not None:
            self.step('bp-obligation status', work, observe=False)
        if not boundaries:
            return
        reply = self.target.peer_list()
        problem = None if reply['exit'] == 0 else 'peer list: exit'
        problem = problem or self.model.check_boundaries(reply['text'])
        self.trace.append(dict(peer_list=reply, verdict=problem))
        self.require(problem is None, rule='peer list', request=None, reply=reply, detail=problem)

    @capture_step(None, 'bp')
    def witnesses(self):
        s, t = self.step, self.target
        s('carry list')
        # The producer enqueues every work first: an enqueue needs no transaction pending in the journal
        # and a fresh transaction id (books/bp-workflow.lisp fn-bp-prepare-enqueue), which requests use too.
        a, b, c, d, e = (self.enqueue() for _ in range(ARTICLES))
        self.enqueue(a)                                                    # duplicate work id
        s('bp-obligation status', 'work-absent')
        s('bp-obligation undertake', a, '3')
        s('bp-obligation undertake', a, '3')
        s('bp-obligation undertake', 'work-absent', '3')
        s('bp-obligation undertake', b, '3')
        s('carry inspect', a)
        s('carry inspect', 'work-absent')
        s('carry pause', a)
        s('carry pause', a)
        self.request(a)                                                    # carry-paused
        s('carry resume', a)
        s('carry resume', a)
        s('carry pause', '*')
        s('carry resume', '*')
        s('carry resume', '*')
        s('carry pause', 'work-absent')
        s('carry resume', 'work-absent')
        s('carry drop', b, 'peer', 'retired')
        s('carry drop', b, 'again')
        s('carry drop', a)                                                 # no reason: usage
        s('carry resume', b)
        s('carry pause', b)
        self.request(b)                                                    # carry-dropped
        self.request(c)                                                    # forward-pin-not-durable
        self.request(a)                                                    # no route
        s('carry abandon', c, 'never', 'undertaken')                       # not-held
        s('carry abandon', 'work-absent', 'x')
        s('carry abandon', b)                                              # no reason: usage
        s('carry abandon', b, 'peer', 'gone')
        s('carry abandon', b, 'again')
        self.request(b)
        s('bp-obligation receipt')
        s('bp-obligation undertake', b, '3')                               # a waived work is never re-pinned
        s('bp-boundary add', 'fn-b-boundary', 'fn-b.bp.gate.invalid', PEER, t.listen, 'contact', t.dead)
        s('bp-boundary add', 'bad-eid', 'bad.bp.gate.invalid', 'dtn:none', t.listen)
        s('bp-boundary add', 'carrier', 'carrier.bp.gate.invalid', 'dtn://fn-c/', t.listen + 1,
          'carries', 'dtn://src/', 'releases-for', 'dtn://iss/')
        s('bp-route add', 'dtn://fn-q/*', 'no-such-boundary')
        s('bp-route add', 'not an eid', 'fn-b-boundary')
        self.request(a)                                                    # no live hop / no route
        s('bp-route add', 'dtn://fn-b/*', 'fn-b-boundary')
        self.request(a)                                                    # routed: never connects, 7
        s('bp-route remove', 'dtn://fn-b/*', 'fn-b-boundary')
        s('bp-route remove', 'dtn://fn-b/*', 'fn-b-boundary')
        s('bp-obligation undertake', d, '3')
        s('carry pause', d)
        s('carry abandon', d, 'paused', 'then', 'waived')
        s('bp-obligation undertake', e, '3')
        s('carry pause', e)
        s('carry drop', e, 'paused', 'then', 'dropped')
        s('carry pause', '*')
        wanted = {(v, r) for v in BpModel.VERBS for r in (False, True)} - {
            ('carry list', True), ('bp-obligation status', True), ('bp-obligation receipt', False)}
        self.require(wanted <= self.checked_verbs, rule='witness-coverage', request=None,
                     reply=sorted(self.checked_verbs), detail='each scoped verb needs a success and a refusal witness')


GENERATED = (
    ('carry pause', '*'), ('carry resume', '*'), ('bp-route add', 'dtn://fn-b/*', 'fn-b-boundary'),
    ('bp-route add', 'dtn://fn-b/', 'fn-b-boundary', '5'), ('bp-route remove', 'dtn://fn-b/*', 'fn-b-boundary'),
    ('bp-route remove', 'dtn://fn-b/', 'fn-b-boundary'), ('bp-route add', 'dtn://fn-z/*', 'fn-b-boundary', '1'),
    ('bp-boundary add', 'other-boundary', 'other.bp.gate.invalid', 'ipn:7.1', '1'), ('bp-obligation receipt',),
)


def machine(case, target_factory=BpTarget, traces=None):
    from hypothesis import strategies as st
    from hypothesis.stateful import RuleBasedStateMachine, rule

    class BpMachine(RuleBasedStateMachine):
        @capture_step(case, 'bp')
        def __init__(self):
            super().__init__()
            self.cleanup, self.trace = ExitStack(), []
            resources = unittest.TestCase()
            resources.addCleanup = self.cleanup.callback
            try:
                self.exercise = Exercise(case, target_factory(resources), self.trace)
                self.exercise.witnesses()
            except BaseException:
                if traces is not None:
                    traces.append(self.trace)
                self.cleanup.close()
                raise

        def works(self):
            return sorted(self.exercise.model.works) + ['work-absent']

        @rule(words=st.sampled_from(GENERATED))
        @capture_step(case, 'bp', request=lambda self, words: dict(words=words))
        def config(self, words):
            self.exercise.step(*words)

        @rule(verb=st.sampled_from(('carry pause', 'carry resume', 'carry inspect', 'bp-obligation undertake',
                                    'bp-obligation status', 'bp-obligation request', 'carry drop', 'carry abandon')),
              index=st.integers(0, 7), malformed=st.booleans())
        @capture_step(case, 'bp', request=lambda self, verb, index, malformed: dict(verb=verb, index=index))
        def on_work(self, verb, index, malformed):
            works = self.works()
            work = works[index % len(works)]
            if verb == 'bp-obligation request':
                if work in self.exercise.model.works:
                    self.exercise.request(work)
                return
            extra = {'bp-obligation undertake': ('3',), 'carry drop': ('generated', 'drop'),
                     'carry abandon': ('generated', 'waiver')}.get(verb, ())
            if malformed and verb.startswith('carry '):
                extra = extra + ('',)
            self.exercise.step(verb, work, *extra)

        def teardown(self):
            if traces is not None:
                traces.append(self.trace)
            self.cleanup.close()

    return BpMachine


class TestSurface(SurfaceCase):
    family, form = 'bp', 'S'

    @serving('bp')
    def test_live_state_machine(self):
        self.evidence['recorded_differences'] = []
        traces = self.evidence['traces'] = []
        run_live_machine(self, 'bp', machine(self, traces=traces))

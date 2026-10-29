"""Live local consumer S form; public CLI JSON + cursor/report file observations.

The locator fixture witnesses Store positions through a separate consumer after
NNTP acceptance, checking every expected identity. It is not an oracle for the
consumer under test. No private journal layout or fn1 code is imported. General
rebase has no carried CLI opcode (spec request codes 0..10); that rule runs on
the fake semantic target and is explicitly unavailable on the local CLI.
"""
from contextlib import ExitStack
from dataclasses import replace
import json
import time
import unittest

from fn2.tests.model.consumer_model import ConsumerModel, Cursor, Event, Request
from fn2.tests.surface import RUN, SurfaceCase, Target, serving


class ConsumerTarget:
    supports_rebase = False

    def __init__(self, case):
        from tests.native_harness import article
        self.case, self.live = case, Target(case)
        self.node, self.serial = self.live.node, 0
        self.observer = self.call(Request('register', 'hs-locator'))['cursor']
        self.history, self.incarnation = self.observer.history, self.observer.incarnation
        self.principal, self.reserved_epochs = self.observer.principal, {self.observer.epoch}
        stream = self.live.connect()
        case.addCleanup(stream.close, quit=False)
        ids = ['<hs-one@surface.invalid>', '<hs-two@surface.invalid>']
        for ident in ids:
            first, final = stream.post(article(ident, groups='surface.test'))
            case.assertTrue(first.startswith(b'340'), first)
            case.assertTrue(final.startswith(b'240'), final)
        result = self.node.operator('article', 'withdraw', ids[1], '--reason', 'HS fixture', timeout=20)
        case.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.events, self.withdrawn = [], {ids[1]}
        fixture_frontier = self.sync_frontier()
        # Withdrawal adds an event in addition to replacing the original report.
        wanted = [(ids[0], 'article'), (ids[1], 'withdrawn'), (ids[1], 'withdrawn')]
        while wanted:
            frontier = self.sync_frontier()
            reply = self.call(Request('poll', 'hs-locator'))
            case.assertEqual(reply['outcome'], 'accepted', reply)
            cursor = reply['cursor']
            case.assertGreater(cursor.position, self.observer.position)
            case.assertLessEqual(cursor.position, min(frontier, self.observer.position + 16))
            if reply['report'] != 'empty':
                case.assertTrue(wanted, reply)
                case.assertEqual((reply['message_id'], reply['report']), wanted.pop(0))
                self.events.append(Event(cursor.position, reply['message_id'], kind=reply['report']))
                if reply['report'] == 'withdrawn':
                    case.assertEqual(reply['report_bytes'], b'FNWD\1' + reply['message_id'].encode())
            if cursor.position >= fixture_frontier:
                case.assertFalse(wanted, 'locator skipped NNTP-accepted fixture events')
            reply = self.call(Request('ack', 'hs-locator', cursor=cursor))
            case.assertEqual(reply['outcome'], 'accepted', reply)
            self.observer = reply['cursor']
        case.assertFalse(wanted, 'locator skipped NNTP-accepted fixture events')
        # Account creation follows the carried identity native's public exchange.
        invitation = self.node.operator('account', 'invite', '--expires', '3600', timeout=20)
        import re
        codes = re.findall(rb'^[0-9a-f]{32}$', invitation.stdout, re.M)
        case.assertEqual(len(codes), 1, invitation.stdout + invitation.stderr)
        case.assertTrue(stream.command('XREDEEM ' + codes[0].decode() + ' hs-account').startswith(b'381'))
        case.assertTrue(stream.command('XREDEEM PASS hs-secret').startswith(b'281'))
        self.frontier = self.sync_frontier()

    def sync_frontier(self):
        reply = self.call(Request('status', 'hs-locator'))
        self.case.assertEqual(reply['outcome'], 'accepted', reply)
        self.case.assertEqual(reply['committed_ack'], self.observer.position)
        self.case.assertEqual(reply['journal_event_distance'], reply['journal_frontier'] - self.observer.position)
        self.case.assertGreaterEqual(reply['journal_frontier'], getattr(self, 'frontier', 0))
        self.frontier = reply['journal_frontier']
        return self.frontier

    def bind(self, name, allowed=True):
        result = self.node.operator('consumer', 'bind', name, '--account', 'hs-account', timeout=20)
        self.case.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def call(self, request):
        r = request
        if r.verb == 'rebase':
            raise NotImplementedError('general rebase has no local CLI carrier')
        self.serial += 1
        base = self.node.root / ('hs-' + str(self.serial))
        cursor, report, secret = [base.with_suffix(s) for s in ('.fncu', '.report', '.secret')]
        words = ['consumer', '--json', r.verb, self.node.control]
        if r.verb in ('register', 'position'):
            words += [r.consumer] + ([r.query] if r.verb == 'register' else []) + [cursor]
        elif r.verb in ('ack', 'bound-ack'):
            cursor.write_bytes(r.cursor.encode()); words += [cursor]
            if r.verb == 'bound-ack':
                secret.write_text((r.secret or '') + '\n'); words += [secret]
        elif r.verb in ('poll', 'wait', 'bound-poll', 'bound-wait'):
            words += [r.consumer]
            if r.verb.startswith('bound-'):
                secret.write_text((r.secret or '') + '\n'); words += [secret]
            words += [cursor, report]
            if r.verb.endswith('wait'):
                words += ['--timeout', str(r.timeout)]
        else:
            words += [r.consumer]
        started = time.monotonic()
        result = self.node.invoke(*words, timeout=r.timeout + 15)
        reply = json.loads(result.stdout.decode('ascii'))
        reply['elapsed'] = time.monotonic() - started
        self.case.assertEqual(result.returncode, {'accepted': 0, 'refused': 1, 'uncertain': 3}.get(reply['outcome']), reply)
        if reply['outcome'] == 'accepted':
            if r.verb in ('ack', 'bound-ack'):
                # Ack writes no output cursor: observe durable position separately.
                reply['cursor'] = self.call(Request('position', r.consumer))['cursor']
            elif cursor.exists():
                reply['cursor'] = Cursor.decode(cursor.read_bytes())
            if report.exists():
                reply['report_bytes'] = report.read_bytes()
                # Not observed: the JSON line has no `more`. H3 receives it from the
                # frontier read; the model does not check it on this target.
                reply['_more_from_frontier'] = reply['cursor'].position < self.frontier
        return reply


def machine(case, target_factory=ConsumerTarget, traces=None):
    from hypothesis import strategies as st
    from hypothesis.stateful import Bundle, RuleBasedStateMachine, invariant, precondition, rule

    class ConsumerMachine(RuleBasedStateMachine):
        consumers, cursors = Bundle('consumers'), Bundle('cursors')

        def __init__(self):
            super().__init__()
            self.cleanup, self.trace = ExitStack(), []
            resources = unittest.TestCase()
            resources.addCleanup = self.cleanup.callback
            try:
                self.target = target_factory(resources)
                self.model = ConsumerModel(history=self.target.history, incarnation=self.target.incarnation,
                    principal=self.target.principal, events=self.target.events, frontier=self.target.frontier)
                self.model.withdrawn = set(self.target.withdrawn)
                self.model.epochs.update(self.target.reserved_epochs)
            except BaseException:
                self.cleanup.close()
                raise

        def step(self, verb, name, **kwargs):
            self.model.frontier = self.target.sync_frontier()
            expected = self.model.rule(verb, name, **kwargs)
            context = self.model.consumers.get(name, Cursor(self.model.history,
                self.model.incarnation, name, 0, self.model.principal, 'surface.test'))
            reply = self.target.call(expected.request)
            reply['_frontier_after'] = self.target.sync_frontier()
            self.trace.append((expected.request, context, reply))
            case.assertIsNone(expected.check(reply), (expected.check(reply), expected.request, reply))
            expected.update(reply)
            return reply.get('cursor')

        @rule(target=consumers, name=st.sampled_from(['hs-a', 'hs-b', 'hs-c']))
        def register(self, name):
            self.step('register', name)
            return name

        @rule(target=cursors, name=consumers)
        def position(self, name):
            return self.step('position', name)

        @rule(target=cursors, name=consumers)
        def poll(self, name):
            return self.step('poll', name)

        @rule(cursor=cursors)
        def ack(self, cursor):
            if cursor is not None:
                self.step('ack', cursor.consumer, cursor=cursor)

        @rule(name=consumers)
        def status(self, name):
            self.step('status', name)

        @rule(name=consumers)
        def unregister(self, name):
            self.step('unregister', name)

        @precondition(lambda self: self.target.supports_rebase)
        @rule(name=consumers)
        def rebase(self, name):
            old = self.model.consumers.get(name)
            self.step('rebase', name, view_version=old.view_version + 1 if old else 1)

        @rule(name=consumers)
        def bind(self, name):
            if name in self.model.consumers:
                self.target.bind(name)
                self.model.bindings[name] = ('hs-secret', True)

        @rule(target=cursors, name=consumers, secret=st.sampled_from(['hs-secret', 'wrong']))
        def bound_poll(self, name, secret):
            return self.step('bound-poll', name, secret=secret)

        @rule(cursor=cursors, secret=st.sampled_from(['hs-secret', 'wrong']))
        def bound_ack(self, cursor, secret):
            if cursor is not None:
                self.step('bound-ack', cursor.consumer, cursor=cursor, secret=secret)

        @rule(target=cursors, name=consumers)
        def wait(self, name):
            return self.step('wait', name, timeout=0)

        @rule(target=cursors, name=consumers, secret=st.sampled_from(['hs-secret', 'wrong']))
        def bound_wait(self, name, secret):
            return self.step('bound-wait', name, secret=secret, timeout=0)

        @rule(cursor=cursors, field=st.sampled_from(['history', 'incarnation', 'principal', 'query', 'epoch']))
        def foreign(self, cursor, field):
            if cursor is not None:
                value = cursor.epoch + 10000 if field == 'epoch' else 'foreign'
                self.step('ack', cursor.consumer, cursor=replace(cursor, **{field: value}))

        @invariant()
        def durable_positions(self):
            for name in list(self.model.consumers):
                self.step('position', name)

        def teardown(self):
            try:
                if traces is not None:
                    traces.append(self.trace)
            finally:
                self.cleanup.close()

    return ConsumerMachine


class TestSurface(SurfaceCase):
    family, form = 'consumer', 'S'

    @serving('consumer')
    def test_live_state_machine(self):
        from hypothesis import settings
        from hypothesis.stateful import run_state_machine_as_test
        run_state_machine_as_test(machine(self), settings=settings(max_examples=RUN.get('examples', 200),
            stateful_step_count=50, deadline=None, database=None, derandomize=True))

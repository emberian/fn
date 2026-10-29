"""HZ operator S: fixed per-verb witnesses, then 30 generated transitions.

One fresh node/example, STORE_INIT, loopback only. Every CLI has a 3 s timeout
(init/start 10 s), every wire read 3 s and every block <=512 lines/64 KiB.
The finite fixture has <=7 groups, <=4 logins and <=8 article identities;
ordinary native CLI calls should keep an example near 30 s (nominal, unmeasured
here without an image). These are test-work bounds, not product ceilings.
The enclosing surface TestCase supervisor supplies the hard wall bound.
"""
from contextlib import ExitStack, contextmanager
import os
import re
import time
import unittest

from fn2.tests.model import framing
from fn2.tests.model.limits_model import STORE_INIT
from fn2.tests.model.operator_model import (GROUP, INITIAL_GROUPS, NEW_PASSWORD,
    PASSWORD, OperatorModel, Request)
from fn2.tests.surface import SurfaceCase, owned_ports, serving
from fn2.tests.surface.live_evidence import capture_step, json_value, record_failure, run_live_machine


class Wire:
    def __init__(self, client):
        self.client, self.greeting = client, client.greeting

    def command(self, command):
        self.client.send(command + b'\r\n')
        return self.client.line(limit=512)

    def block(self):
        rows, total, deadline = [], 0, time.monotonic() + 3
        for _ in range(512):
            self.client.sock.settimeout(max(.001, deadline - time.monotonic()))
            row = self.client.line(limit=8192)
            rows.append(row)
            total += len(row)
            if total > 65536 or time.monotonic() > deadline:
                raise AssertionError('operator fixture block budget exceeded')
            if row == b'.\r\n':
                self.client.sock.settimeout(3)
                return b''.join(rows)
        raise AssertionError('operator fixture line budget exceeded')

    def post_body(self, data):
        self.client.send(data)
        return self.client.line(limit=512)

    def close(self):
        self.client.close(quit=False)


class OperatorTarget:
    @owned_ports
    def __init__(self, case):
        from tests.native_harness import Node, native_image
        self.adjudication_target = os.environ.get('FN2_SURFACE_TARGET', 'fn2')
        self.node = Node(case, native_image('FN_NATIVE_HOST'))
        flags = [item for key, value in STORE_INIT.items() for item in ('--' + key, str(value))]
        result = self.node.operator('init', '--profile', 'development', *flags, *INITIAL_GROUPS, timeout=10)
        reply = dict(exit=result.returncode, text=(result.stdout + result.stderr).decode('ascii'))
        if result.returncode:
            record_failure(case, 'operator', rule='init', request=flags, reply=reply,
                           verdict=dict(ok=False, detail='fixture init'), trace=[])
        case.assertEqual(result.returncode, 0, reply)
        self.node.start(timeout=10)

    def call(self, request):
        data = None if request.password is None else (request.password + '\n') * 2
        result = self.node.operator(*request.words, input=data.encode() if data else None, timeout=3)
        return dict(exit=result.returncode, text=(result.stdout + result.stderr).decode('ascii'))

    def status(self):
        result = self.node.operator('status', timeout=3)
        return dict(exit=result.returncode, text=(result.stdout + result.stderr).decode('ascii'))

    def open(self):
        from tests.native_harness import Client
        return Wire(Client(self.node.port, timeout=3, greeting=None))


class Exercise:
    def __init__(self, case, target, trace=None):
        self.case, self.target = case, target
        self.model = OperatorModel()
        self.trace = trace if trace is not None else []
        self.serial = 0
        self.checked_verbs = set()

    def require(self, good, *, rule, request, reply, detail):
        if not good:
            record_failure(self.case, 'operator', rule=rule, request=request, reply=reply,
                           verdict=dict(ok=False, detail=detail), trace=self.trace)
        self.case.assertTrue(good, (detail, request, reply))

    def check_wire(self, expected, status, body=None, *, request=None):
        verdict = expected.check(status, body)
        self.trace.append(dict(wire=request, status=status, body=body, verdict=verdict))
        if not verdict.ok:
            record_failure(self.case, 'operator', rule=verdict.rule, request=request,
                           reply=dict(status=status, body=body), verdict=verdict, trace=self.trace)
        self.case.assertTrue(verdict.ok, (verdict, status, body))
        expected.update(status, body)

    @capture_step(None, 'operator', request=lambda self, verb, *args, **kwargs: dict(verb=verb, args=args))
    def step(self, verb, *args, password=None, observe=True):
        expected = self.model.rule(verb, *args, password=password)
        result = self.target.call(expected.request)
        self.trace.append(dict(request=expected.request, reply=result))
        target = getattr(self.target, 'adjudication_target', 'fake')
        recorded = expected.recorded_difference(result, target)
        problem = expected.check(result)
        if recorded is None:
            self.require(problem is None, rule=verb, request=expected.request, reply=result, detail=problem)
        expected.update(result, target)
        self.checked_verbs.add((verb, bool(expected.reason)))
        if recorded is not None and hasattr(self.case, 'evidence'):
            self.case.evidence.setdefault('recorded_differences', []).append(json_value(dict(recorded, step=len(self.trace))))
        if observe:
            self.observe()
        return result

    @contextmanager
    def session(self, login=None, password=None):
        conn = self.model.wire.connect(tls=False, implicit_tls=False)
        wire = self.target.open()
        try:
            self.check_wire(conn.greeting(), wire.greeting)
            if login:
                self.command((conn, wire), 'AUTHINFO USER ' + login)
                self.command((conn, wire), 'AUTHINFO PASS ' + (password or PASSWORD))
            yield conn, wire
            self.command((conn, wire), 'QUIT')
        finally:
            conn.quit = True
            wire.close()

    def command(self, session, command):
        conn, wire = session
        raw = command.encode('ascii')
        expected = conn.send(raw + b'\r\n')
        status = wire.command(raw)
        body = wire.block() if expected.multiline_for(status) else None
        self.check_wire(expected, status, body, request=command)
        return status

    @capture_step(None, 'operator')
    def observe(self):
        # New sessions see operator publication; no second wire oracle.
        with self.session() as session:
            for cmd in ('LIST ACTIVE', 'LIST NEWSGROUPS', 'LIST MOTD'):
                self.command(session, cmd)
            for name in self.model.groups:
                self.command(session, 'GROUP ' + name)
        # The moderator sees held envelopes; the regular login sees approved
        # source bodies. Every known login and deleted/overridden password is
        # checked in the dedicated credentials witnesses below.
        if 'hz-reader' in self.model.wire.accounts:
            with self.session('hz-reader', self.model.wire.accounts['hz-reader']['password']) as session:
                self.command(session, 'LIST ACTIVE')
                for name in (GROUP, 'hz.mod', 'hz.mod.moderation'):
                    self.command(session, 'GROUP ' + name)
                for ident, h in self.model.held.items():
                    self.command(session, 'STAT ' + ident)
                    if h['state'] == 'approved':
                        self.command(session, 'BODY ' + ident)
        if 'hz-mod' in self.model.wire.accounts:
            with self.session('hz-mod', self.model.wire.accounts['hz-mod']['password']) as session:
                for h in self.model.held.values():
                    self.command(session, 'STAT ' + h['envelope'])
        if self.model.capacity is not None:
            reply = self.target.status()
            found = re.findall(r'\bcharge-capacity[=: ]+([0-9]+)', reply['text'])
            self.require(reply['exit'] == 0 and found == [str(self.model.capacity)], rule='capacity-status',
                         request='status', reply=reply, detail='capacity must be the published charge-capacity')

    @capture_step(None, 'operator')
    def redeem(self, login='hz-reader'):
        code = self.model.pending[-1]
        with self.session() as session:
            self.command(session, 'XREDEEM ' + code + ' ' + login)
            reply = self.command(session, 'XREDEEM PASS ' + PASSWORD)
            self.require(reply.startswith(b'281 '), rule='redeem', request=login, reply=reply,
                         detail='valid fixture invitation must redeem')
        self.model.redeemed(code, login, PASSWORD)
        self.observe()

    @capture_step(None, 'operator', request=lambda self, group=GROUP, **kwargs: group)
    def post(self, group=GROUP, *, login='hz-reader', accepted=True):
        self.serial += 1
        ident = f'<hz-{self.serial}@surface.invalid>'
        source = (f'From: hz@surface.invalid\r\nNewsgroups: {group}\r\nSubject: HZ\r\n'
                  f'Message-ID: {ident}\r\nDate: Thu, 29 Oct 2026 12:00:00 +0000\r\n\r\nHZ body {self.serial}\r\n').encode()
        flags = self.model.groups.get(group, {})
        envelope = '<fn-moderate.' + ident[1:]
        projected_id = envelope if flags.get('moderated') else ident
        # Only body/identity/membership reads: the private Injection-Info and
        # envelope headers are not invented from a target read.
        self.model.wire.policy.setdefault('stored_articles', {})[projected_id] = source
        with self.session(login, self.model.wire.accounts[login]['password']) as session:
            first = self.command(session, 'POST')
            if first.startswith(b'340 '):
                conn, wire = session
                block = framing.encode_block(source)
                expected = conn.send_block(block)
                reply = wire.post_body(block)
                self.check_wire(expected, reply, request=block)
                self.require(reply.startswith(b'240 ') == accepted, rule='post-determinate',
                    request=dict(group=group, login=login), reply=reply,
                    detail='finite funded fixture must accept valid POST, refuse disallowed POST')
                if accepted and flags.get('moderated'):
                    self.model.held[ident] = dict(group=group, envelope=envelope, source=source, state='held')
            else:
                self.require(not accepted, rule='post-permission', request=group, reply=first, detail='posting login must enter body mode')
        self.observe()
        return ident

    def witness(self, verb, *args, password=None):
        self.step(verb, *args, password=password)
        self.step(verb, *args, '', password=password)

    @capture_step(None, 'operator')
    def witnesses(self):
        self.witness('account invite', '--expires', '3600')
        self.redeem()
        self.witness('account list')
        self.witness('principal set-password', 'hz-mod', '--posting', password=PASSWORD)
        self.witness('account set-password', 'hz-reader', '--posting', password=NEW_PASSWORD)
        with self.session('hz-reader', PASSWORD):
            pass  # shadowed redeemed password MUST fail through NntpModel
        self.witness('principal list')
        self.witness('group create', 'hz.new')
        self.step('group create', 'hz.new')  # duplicate, not argv preflight
        self.witness('group describe', GROUP, 'HZ', 'discussion')
        self.step('group describe', 'hz.absent', 'missing')
        self.witness('group policy', GROUP, 'n')
        self.post(accepted=False)
        self.step('group policy', GROUP, 'y')
        self.witness('motd set', 'Hello HZ', '.dot line')
        self.witness('motd clear')
        self.witness('capacity', '1048576')
        self.step('capacity', 'not-a-count')
        self.witness('retention set', 'keep-forever')
        self.witness('retention expire', GROUP, 'purge', '30')
        self.step('retention expire', GROUP, 'clear')
        self.witness('account access', 'hz-reader', '--read', 'hz.*,!hz.test', '--post', 'hz.*,!hz.test')
        self.post(accepted=False)
        self.step('account access', 'hz-reader', '--read', 'hz.[', '--post', '*')
        self.step('account access', 'hz-reader', '--read', '*', '--post', '*')
        self.post()  # article survives retire/recreate and later refusals
        self.step('capacity', '0')
        self.step('capacity', '4294967296')
        self.witness('group retire', GROUP)
        self.step('group create', GROUP)
        self.witness('group moderate', 'hz.mod', '--moderators', 'hz-mod')
        self.step('group moderate', 'hz.mod', '--moderators', 'hz-mod', '--queue', 'hz.absent')
        approved = self.post('hz.mod')
        self.witness('moderation list', 'hz.mod')
        self.step('moderation approve', approved, '--moderator', 'hz-reader')
        self.witness('moderation approve', approved, '--moderator', 'hz-mod')
        self.step('moderation list', 'hz.mod')
        rejected = self.post('hz.mod')
        self.step('moderation reject', rejected, '--moderator', 'hz-reader', '--reason', 'HZ refusal')
        self.witness('moderation reject', rejected, '--moderator', 'hz-mod', '--reason', 'HZ rejected')
        self.step('moderation list', 'hz.mod')
        self.step('group moderate', 'hz.mod', '--off')
        self.witness('principal delete', 'hz-mod')
        self.witness('account delete', 'hz-reader')  # file first: old password revives
        self.step('account delete', 'hz-reader')  # redeemed tombstone
        with self.session('hz-reader', PASSWORD):
            pass
        self.step('account delete', 'hz-absent')
        self.step('account list')
        # Restore a posting account for generated wire observations.
        self.step('account set-password', 'hz-reader', '--posting', password=PASSWORD)
        self.require(self.checked_verbs == {(v, r) for v in OperatorModel.VERBS for r in (False, True)},
                     rule='witness-coverage', request=None, reply=sorted(self.checked_verbs), detail='each scoped verb needs success/refusal witness')


GENERATED = (
    ('group create', 'bad/group'), ('group create', 'hz.new'), ('group create', 'hz.extra'), ('group retire', 'hz.extra'),
    ('group describe', GROUP, 'Generated HZ'), ('group describe', 'hz.absent', 'missing'),
    ('group policy', GROUP, 'y'), ('group policy', GROUP, 'n'),
    ('group moderate', 'hz.mod', '--off'),
    ('group moderate', 'hz.mod', '--moderators', 'hz-reader'),
    ('motd set', 'Generated message'), ('motd clear',), ('capacity', '1048576'),
    ('capacity', 'wrong'), ('retention set', 'release-after', '30'),
    ('retention set', 'keep-forever'), ('retention expire', GROUP, 'purge', '30'),
    ('retention expire', GROUP, 'clear'), ('account list',), ('principal list',),
    ('account access', 'hz-reader', '--read', '*', '--post', '*'),
    ('account access', 'hz-reader', '--read', 'hz.*,!hz.test', '--post', 'hz.mod'),
    ('account access', 'hz-reader', '--read', 'hz.[', '--post', '*'),
    ('account delete', 'hz-absent'), ('principal delete', 'hz-absent'),
    ('account set-password', 'hz-reader', '--posting'),
    ('principal set-password', 'hz-reader', '--no-posting'),
    ('account invite', ''), ('moderation approve', '', '--moderator', 'hz-reader'),
    ('moderation reject', '', '--moderator', 'hz-reader'), ('moderation list', 'hz.absent'),
)


def machine(case, target_factory=OperatorTarget, traces=None):
    from hypothesis import strategies as st
    from hypothesis.stateful import RuleBasedStateMachine, precondition, rule

    class OperatorMachine(RuleBasedStateMachine):
        @capture_step(case, 'operator')
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

        @rule(words=st.sampled_from(GENERATED), malformed=st.booleans())
        @capture_step(case, 'operator', request=lambda self, words, malformed: dict(words=words, malformed=malformed))
        def transition(self, words, malformed):
            self.exercise.step(words[0], *words[1:], *(('',) if malformed else ()),
                               password=PASSWORD if words[0].endswith('set-password') else None)

        @precondition(lambda self: self.exercise.serial < 8 and
                      self.exercise.model.wire.accounts['hz-reader']['posting'])
        @rule()
        @capture_step(case, 'operator')
        def generated_post(self):
            model = self.exercise.model
            account = model.wire.accounts['hz-reader']
            from fn2.tests.model.nntp_model import wildmat
            admitted = (wildmat(account.get('read', '*'), 'hz.mod') and
                        wildmat(account.get('post', '*'), 'hz.mod'))
            self.exercise.post('hz.mod', accepted=admitted)

        @precondition(lambda self: any(h['state'] == 'held' and
                      any(login in self.exercise.model.wire.accounts for login in
                          self.exercise.model.groups[h['group']].get('moderators', ()))
                      for h in self.exercise.model.held.values()))
        @rule(approve=st.booleans(), wrong=st.booleans())
        @capture_step(case, 'operator', request=lambda self, approve, wrong: dict(approve=approve, wrong=wrong))
        def generated_decision(self, approve, wrong):
            model = self.exercise.model
            for ident, held in model.held.items():
                moderators = [login for login in model.groups[held['group']].get('moderators', ())
                              if login in model.wire.accounts]
                if held['state'] == 'held' and moderators:
                    self.exercise.step('moderation approve' if approve else 'moderation reject', ident,
                                       '--moderator', 'hz-stranger' if wrong else moderators[0])
                    self.exercise.step('moderation list', held['group'])
                    break

        def teardown(self):
            if traces is not None:
                traces.append(self.trace)
            self.cleanup.close()

    return OperatorMachine


class TestSurface(SurfaceCase):
    family, form = 'operator', 'S'

    @serving('operator')
    def test_live_state_machine(self):
        self.evidence['recorded_differences'] = []
        traces = self.evidence['traces'] = []
        run_live_machine(self, 'operator', machine(self, traces=traces))

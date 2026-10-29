"""HW live config/limits S form: one fresh owner per generated example.

Design note for Astra: fixed witnesses establish every requested wire effect;
30 generated steps explore policy interleavings, including all key types. Long
windows are never slept out: a 150 ms post-pacing observation is followed by
lifting the policy and observing the queued command. First/idle limits are 1 s,
with 2.5 s observation bounds. At most 64 sockets are opened per example (the
fixed campaign uses fewer than 20); all are closed in finally/ExitStack.
Nominal waiting is <=5.15 s plus local CLI/startup cost, targeting ~20 s/example;
this is not a measured hbox duration. Each CLI call has a 3 s timeout; init/start
have 10 s. No TCP-write == host-read assumption for the step-rate work quantum.
The 10 s send-stalled witness remains in E: forcing kernel send-buffer exhaustion
is outside this short S profile. No fn1 reply has been recorded for HW.

Set outcomes use their exit status and named refusal, with any success line
accepted where no literal is specified. Effects are observed on the NNTP wire;
no implementation-derived fallback oracle is used.
"""
from contextlib import ExitStack
import json
import select
import time
import unittest

from fn2.tests.model.limits_model import INIT_FIXED, KEYS, LimitsModel, STORE_DEFAULTS, TOML_KEYS, U32
from fn2.tests.model.nntp_model import NntpModel
from fn2.tests.surface import SurfaceCase, live_model_settings, serving

GROUP = 'surface.test'
ACCOUNT = {'hw-poster': {'password': 'hw-fixture-password', 'posting': True}}  # FAKE-SECRET
IDENT = '<hw-pacing@surface.invalid>'
ARTICLE = (b'From: hw@surface.invalid\r\nNewsgroups: surface.test\r\n'
           b'Subject: HW pacing\r\nMessage-ID: <hw-pacing@surface.invalid>\r\n'
           b'Date: Thu, 29 Oct 2026 12:00:00 +0000\r\n\r\nHW\r\n')
PROBE = .15
CLOSE_BOUND = 2.5


class Wire:
    def __init__(self, client):
        self.client = client
        self.greeting = client.greeting

    def command(self, command):
        return self.client.command(command)

    def send(self, data):
        self.client.send(data)

    def line(self):
        return self.client.line(limit=512)

    def observe(self, seconds):
        """Return actual bytes/EOF separately. A timeout is never an EOF.

        Inspect pending Client bytes before select; otherwise a coalesced extra
        line could be mistaken for a silent wait or silent close.
        """
        if self.client.pending:
            return self.client.pending, False
        if not select.select([self.client.sock], [], [], seconds)[0]:
            return b'', False
        data = self.client.sock.recv(513)
        return data, data == b''

    def close(self):
        self.client.close(quit=False)


class LimitsTarget:
    def __init__(self, case):
        from tests.native_harness import Node, native_image
        self.node = Node(case, native_image('FN_NATIVE_HOST'))
        flags = [item for k, v in STORE_DEFAULTS.items() for item in ('--' + k, str(v))]
        self.node.operator('init', '--profile', 'development', *flags,
                           GROUP, expect=0, timeout=10)
        self.node.operator('principal', 'set-password', 'hw-poster', '--posting',
                           input=b'hw-fixture-password\nhw-fixture-password\n', expect=0, timeout=3)
        self.node.start(timeout=10)
        self.case, self.opened = case, 0

    def set(self, key, value):
        result = self.node.operator('policy', 'set', key, value, timeout=3)
        return {'exit': result.returncode, 'text': (result.stdout + result.stderr).decode('ascii')}

    def open(self):
        from tests.native_harness import Client
        self.opened += 1
        if self.opened > 64:
            raise AssertionError('HW fixture exceeded its 64 socket budget')
        wire = Wire(Client(self.node.port, timeout=3, greeting=None))
        self.case.addCleanup(wire.close)
        return wire


class Exercise:
    """Shared executable checks: fake controls traverse exactly the live path."""
    def __init__(self, case, target, trace=None):
        self.case, self.target = case, target
        self.trace = trace if trace is not None else []
        self.policy = LimitsModel()
        # No article/cursor read is made in this workload. This uninterpreted
        # projection supplies H2's authenticated-POST seam; it is NOT a claim
        # about server Injection-Info bytes (which include a private hash).
        self.wire_model = NntpModel({GROUP: {}}, [], ACCOUNT,
            {'posting': True, 'stored_articles': {IDENT: ARTICLE}}, limits=self.policy)
        self.sessions = []

    def set(self, key, value):
        expected = self.policy.set(key, str(value))
        result = self.target.set(key, str(value))
        row = dict(key=key, value=str(value), result=result)
        self.trace.append(row)
        self.case.assertIsNone(expected.check(result), (expected.check(result), key, value, result))
        expected.update(result)

    def check(self, expected, status, *, eof=False):
        verdict = expected.check(status, None, eof=eof)
        self.trace.append(dict(rule=verdict.rule, spec=verdict.spec, status=status.hex(), eof=eof,
                               detail=verdict.detail))
        self.case.assertTrue(verdict.ok, (verdict, status))
        # Expect permits an optional close for some NNTP branches. HW's capacity
        # and deadline witnesses REQUIRE it, so check this independently too.
        if expected.close_after_reply or expected.close_without_reply:
            self.case.assertTrue(eof, 'mandatory EOF not observed')
        expected.update(status, None, eof=eof)

    def open(self):
        conn = self.wire_model.connect(tls=False, implicit_tls=False)
        wire = self.target.open()
        self.sessions.append((conn, wire))
        expected = conn.greeting()
        eof = False
        if expected.close_after_reply:
            extra, eof = wire.observe(CLOSE_BOUND)
            self.case.assertEqual(extra, b'', 'bytes after capacity refusal')
        self.check(expected, wire.greeting, eof=eof)
        return conn, wire

    def command(self, session, command, *, sent=False, block=False):
        conn, wire = session
        command = command.encode() if isinstance(command, str) else command
        expected = conn.send_block(command) if block else conn.send(command + b'\r\n')
        if block:
            wire.send(command)
            status = wire.line()
        else:
            status = wire.line() if sent else wire.command(command)
        eof = False
        if expected.close_after_reply:
            if status.startswith(b'481'):
                status += wire.line()
            extra, eof = wire.observe(CLOSE_BOUND)
            self.case.assertEqual(extra, b'', 'bytes after closing reply')
        self.check(expected, status, eof=eof)
        return status

    def release(self):
        for conn, wire in self.sessions:
            try:
                if not conn.quit:
                    self.command((conn, wire), b'QUIT')
            finally:
                wire.close()
        self.sessions.clear()

    def capacity(self):
        self.set('exposure-trusted', 'none')
        self.set('exposure-per-address', 4)
        self.set('exposure-connections', 2)
        self.open(); self.open()
        # Exit 1 means nothing changed (docs/operator.md:1233-1241). Hold the
        # two admitted sockets across refusal, then observe that same bound.
        self.set('exposure-connections', U32 + 1)
        self.open()  # named total refusal + EOF, also after the refused set
        self.set('exposure-connections', 3)
        self.open(); self.open()  # effect while original sockets remain held
        self.release()
        self.set('exposure-connections', 4)
        self.set('exposure-per-address', 1)
        self.open(); self.open()  # one admitted, named address refusal + EOF
        self.set('exposure-trusted', '127.0.0.1/32')
        self.open(); self.open(); self.open(); self.open()  # trusted still pays total
        self.release()

    def authentication(self):
        self.set('exposure-auth-failures', 2)
        first = self.open()
        self.command(first, b'AUTHINFO USER absent')
        self.command(first, b'AUTHINFO PASS wrong')
        self.release()
        second = self.open()
        self.command(second, b'AUTHINFO USER absent')
        self.command(second, b'AUTHINFO PASS wrong')  # address budget, only first on session
        self.open()  # address blocked at greeting despite trusted loopback
        self.release()
        self.set('exposure-auth-failures', 0)
        self.open()  # disabling applies live without resetting observed failures
        self.release()

    def pacing(self):
        self.set('exposure-posts-per-minute', 1)
        session = self.open()
        self.command(session, b'AUTHINFO USER hw-poster')
        self.command(session, b'AUTHINFO PASS hw-fixture-password')
        self.command(session, b'POST')
        # Require actual durable acceptance: a malformed body might never reach
        # the submission boundary and cannot establish a pacing antecedent.
        reply = self.command(session, ARTICLE + b'.\r\n', block=True)
        self.case.assertTrue(reply.startswith(b'240 '), reply)
        conn, wire = session
        wire.send(b'DATE\r\n')
        data, eof = wire.observe(PROBE)
        self.check(conn.exposure_wait('posts'), data, eof=eof)
        self.set('exposure-posts-per-minute', 0)
        self.command(session, b'DATE', sent=True)  # queued command resumes, no resend
        self.release()

    def deadlines(self):
        for first in (True, False):
            key = 'exposure-first-seconds' if first else 'exposure-idle-seconds'
            self.set(key, 1)
            conn, wire = self.open()
            if not first:
                self.command((conn, wire), b'DATE')
            started = time.monotonic()
            data, eof = wire.observe(CLOSE_BOUND)
            elapsed = time.monotonic() - started
            # Fake targets carry a virtual interval; production reads monotonic.
            elapsed = getattr(wire, 'observed_elapsed', elapsed)
            self.case.assertGreaterEqual(elapsed, 0.8, 'timer closed immediately/too early')
            self.case.assertLessEqual(elapsed, CLOSE_BOUND + .2, 'timer exceeded observation bound')
            # The oracle asks what must have happened BY the observation bound;
            # actual early/late timing is checked independently just above.
            self.check(conn.exposure_deadline(elapsed=CLOSE_BOUND, first=first), data, eof=eof)
            wire.close()
            self.sessions.clear()
            self.set(key, 0)

    def witnesses(self):
        self.capacity()
        self.authentication()
        self.pacing()
        self.deadlines()
        for key, value in [('exposure-connections', str(U32 + 1)),
                           ('exposure-idle-seconds', 'wrong'), ('hw-unknown-key', '1')]:
            self.set(key, value)


# Safe live samples include zero/off and low boundaries without starving future
# CLI work. Large schema boundaries are checked in unit tests and generated
# *invalid* sets; valid huge allocations need a resource observation, not a guess.
VALID = {
    k: tuple(str(x) for x in (spec.minimum, spec.default) if isinstance(x, int))
    for k, spec in KEYS.items() if spec.kind == 'count'
}
VALID.update({k: spec.choices for k, spec in KEYS.items() if spec.kind == 'enum'})
VALID.update({
    'exposure-connections': ('0', '1', '2', '4', '31'),
    'exposure-per-address': ('0', '1', '2', '8'),
    'exposure-trusted': ('none', '127.0.0.1/32', '127.0.0.0/8'),
    'tls-proxy-trusted-peers': ('none', '127.0.0.1/32'),
    'tls-handshake-source-overrides': ('none', '127.0.0.1=1', '127.0.0.1=30'),
    'path-identity': ('hw.surface.invalid', 'hw2.surface.invalid'),
    'complaints-to': ('abuse@surface.invalid', 'postmaster@surface.invalid'),
    **{k: (str(v),) for k, v in STORE_DEFAULTS.items()},
})
INVALID = [(k, v) for k, spec in KEYS.items() for v in (
    ('wrong', '-1', str(spec.maximum + 1)) if spec.kind in ('count', 'store') else ('???',))]
INVALID += [('hw-unknown-key', '1')] + [(k, '1') for k in INIT_FIXED]


def machine(case, target_factory=LimitsTarget, traces=None):
    from hypothesis import strategies as st
    from hypothesis.stateful import RuleBasedStateMachine, precondition, rule

    class LimitsMachine(RuleBasedStateMachine):
        def __init__(self):
            super().__init__()
            self.cleanup = ExitStack()
            resources = unittest.TestCase()
            resources.addCleanup = self.cleanup.callback
            self.trace = []
            try:
                self.exercise = Exercise(case, target_factory(resources), self.trace)
                self.exercise.witnesses()
            except BaseException:
                if traces is not None:
                    traces.append(self.trace)
                self.cleanup.close()
                raise

        @rule(pair=st.sampled_from([(k, v) for k, values in VALID.items() for v in values]))
        def valid_set(self, pair):
            self.exercise.set(*pair)

        @rule(pair=st.sampled_from(INVALID))
        def invalid_set(self, pair):
            self.exercise.set(*pair)

        @precondition(lambda self: self.exercise.target.opened < 64
                      and self.exercise.policy.get('exposure-steps-per-second') == 0)
        @rule()
        def admission(self):
            # Observe the current combination, including a zero capacity and
            # an address budget changed by generated sets. Fixed witnesses above
            # reach every saturation boundary; this probes their interleavings.
            self.exercise.open()
            self.exercise.release()

        def teardown(self):
            try:
                if traces is not None:
                    traces.append(self.trace)
            finally:
                self.cleanup.close()

    return LimitsMachine


def config_witnesses(case):
    """Parse every accepted key; refusal-to-run is distinct from parse refusal.

    Each table is tested independently beside a required store, so a pending
    consumer does not mask another table's parse acceptance. Only run-refusal
    cases invoke run; they must finish with a named failure, never start a node.
    """
    from tests.native_harness import Node, native_image
    node = Node(case, native_image('FN_NATIVE_HOST'))
    node.init(GROUP, profile='development', timeout=10)
    values = {
        'store': {'path': str(node.store_path)},
        'listener': {'host': '127.0.0.1', 'port': node.port, 'tls_port': 563 if node.port != 563 else 564,
                     'tls_cert': '/tmp/hw-cert', 'tls_key': '/tmp/hw-key'},
        'auth': {'required': False, 'protected_only': False, 'path': '/tmp/hw-auth'},
        'posting': {'enabled': True, 'agent': 'hw.invalid'}, 'anchor': {'server': '127.0.0.1'},
        'acl2': {'path': '/tmp/hw-acl2', 'slots': 1}, 'log': {'path': str(node.root / 'hw.log')},
        'control': {'path': str(node.root / 'hw.sock')},
        'alerts': {'command': '/bin/true', 'headroom_min_percent': 10,
                   'refusal_rate_per_minute': 10, 'cooldown_seconds': 60},
        'web': {'port': 8080, 'host': '127.0.0.1', 'site': 'HW', 'domain': 'hw.invalid',
                'proxied': False, 'tls': False, 'idle_seconds': 10, 'max_sessions': 4},
        'tls': {'key_exchange': 'hybrid-preferred'},
        'resources': {'cold_heap_octets': 1048576, 'cold_workers': 1,
                      'cold_descriptors': 16, 'cold_read_ids': 16, 'cold_file_ids': 16,
                      'output_heap_octets': 1048576, 'output_quantum_heap_octets': 4096,
                      'reclaim_live': False},
        'ops': {'mission': 'small-community', 'unit': 'hw', 'scope': 'user',
                'keep_releases': 2, 'log_max_bytes': 1048576, 'log_keep': 2, 'memory_max': '2G'},
    }
    case.assertEqual({k: set(v) for k, v in values.items()}, {k: set(v) for k, v in TOML_KEYS.items()})

    def write(table, fields):
        selected = {'store': values['store'], table: fields}
        node.config.write_text(''.join('[' + name + ']\n' + ''.join(
            k + ' = ' + json.dumps(v) + '\n' for k, v in fields.items())
            for name, fields in selected.items()), encoding='ascii')

    for table, fields in values.items():
        write(table, fields)
        result = node.operator('show', timeout=3)
        case.assertEqual(result.returncode, 0, (table, result.stdout, result.stderr))
    for table, fields, reason in [
        ('listener', {'host': '0.0.0.0'}, 'host'), ('listener', {'host': '::'}, 'host'),
        ('posting', {'agent': 'hw.invalid'}, 'agent'), ('anchor', {'server': '127.0.0.1'}, 'anchor'),
        ('acl2', {'path': '/tmp/hw-acl2', 'slots': 1}, 'acl2')]:
        write(table, fields)
        result = node.operator('run', timeout=3)
        case.assertEqual(result.returncode, 5, (table, result.stdout, result.stderr))
        case.assertIn(reason, (result.stdout + result.stderr).decode('ascii').lower())


class TestSurface(SurfaceCase):
    family, form = 'config_limits', 'S'

    @serving('config_limits')
    def test_live_state_machine(self):
        from hypothesis.stateful import run_state_machine_as_test
        self.evidence['recorded_differences'] = []
        traces = self.evidence['traces'] = []
        run_state_machine_as_test(machine(self, traces=traces), settings=live_model_settings('config_limits'))

    @serving('config_limits')
    def test_init_config_witnesses(self):
        config_witnesses(self)

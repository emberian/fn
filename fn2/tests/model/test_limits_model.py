"""HW independent fake, schema boundaries, composed wire tests and mutants.

The fake implements only the finite HW workload, never calls LimitsModel,
parse_value, NntpModel or Expect, and owns separate policy/wire dictionaries.
Literal defaults and wire bytes intentionally duplicate facts as a control.
This is not live-server evidence. No TCP bind or native image is needed.
"""
import re
import unittest

from .limits_model import ADJUDICATIONS, KEYS, LimitsModel, U32, parse_value
from .nntp_model import NntpModel
from fn2.tests.surface.config_limits.test_model_config_limits import Exercise, machine, VALID


class FakeTarget:
    def __init__(self, case=None, plant=None):
        self.plant = plant
        self.values = dict(zip((
            'exposure-connections', 'exposure-per-address', 'exposure-steps-per-second',
            'exposure-first-seconds', 'exposure-idle-seconds', 'exposure-auth-failures',
            'exposure-posts-per-minute', 'exposure-trusted', 'anonymous',
            'tls-handshakes-per-source-per-minute', 'tls-handshakes-in-flight',
            'tls-handshake-ms', 'tls-handshake-source-overrides', 'tls-proxy-trusted-peers',
            'log-batch-records', 'log-batch-octets', 'barrier-deadline-ms', 'barrier-stall-ms',
            'clock-event-ms', 'compress-min-octets', 'disk-reserve-octets', 'relay-date-skew',
            'refused-offer-capacity', 'relay-require-path', 'path-identity', 'posting-policy',
            'complaints-to', 'max-transactions', 'max-history-octets', 'max-article-octets'), (
            '31', '31', '0', '0', '0', '0', '0', 'none', 'open', '30', '16', '5000', 'none',
            'none', '64', '16777216', '5000', '30000', '1000', '0', '67108864', '86400',
            '4096', '0', 'unset', 'open', 'unset', '4096', '16777216', '32768')))
        self.wire_values = dict(self.values)
        self.explicit = set()
        self.sockets = []
        self.failures = self.posts = 0
        self.opened = 0

    def set(self, key, value):
        reason = None
        numeric = key in self.values and self.values[key].isdecimal()
        if key not in self.values:
            reason = 'unknown-policy-key'
        elif numeric:
            if not re.fullmatch('0|[1-9][0-9]*', value):
                reason = 'policy-value-not-a-number'
            else:
                upper = 86400 if key == 'relay-date-skew' else 1 if key == 'relay-require-path' else 4294967295
                positive = key.startswith(('tls-handshakes-', 'tls-handshake-ms', 'log-batch-',
                                           'barrier-', 'clock-event-', 'disk-reserve-', 'max-'))
                if int(value) > upper:
                    reason = 'above-representation-ceiling' if key.startswith('max-') else 'policy'
                elif int(value) == 0 and positive:
                    reason = 'profile-invalid' if key.startswith('max-') else 'policy'
        elif value == '???':
            reason = 'override-address' if key == 'tls-handshake-source-overrides' else 'policy'
        if self.plant == 'out-of-range' and key == 'exposure-connections' and value == '4294967296':
            reason = None
        if reason:
            if (self.plant == 'refusal-mutation' and key == 'exposure-connections'
                    and value == '4294967296'):
                self.wire_values['exposure-connections'] = '3'
            return {'exit': 1, 'text': 'refused ' + ('wrong-reason' if self.plant == 'wrong-reason' else reason)}
        self.values[key] = value
        self.explicit.add(key)
        if key == 'exposure-connections' and 'exposure-per-address' not in self.explicit:
            self.values['exposure-per-address'] = value
        if self.plant != 'stale-wire':
            self.wire_values = dict(self.values)
        return {'exit': 0, 'text': 'accepted'}

    def open(self):
        self.opened += 1
        if self.opened > 64:
            raise AssertionError('fake fixture socket bound')
        wire = FakeWire(self)
        self.sockets.append(wire)
        return wire


class FakeWire:
    def __init__(self, target):
        self.target = target
        self.closed, self.answered, self.login, self.body = False, False, False, False
        self.user = None
        self.failed = 0
        self.queued = []
        v = target.wire_values
        count = sum(not s.closed for s in target.sockets)
        why = None
        if count >= int(v['exposure-connections']):
            why = 'too many connections; try again later'
        elif v['exposure-trusted'] == 'none' and count >= int(v['exposure-per-address']):
            why = 'too many connections from this address; try again later'
        elif int(v['exposure-auth-failures']) and target.failures >= int(v['exposure-auth-failures']):
            why = 'too many authentication failures from this address'
        if why:
            self.greeting = ('400 ' + why + '\r\n').encode()
            self.closed = target.plant != 'capacity-no-close'
        else:
            self.greeting = b'201 fn fixture\r\n' if v['anonymous'] == 'none' else b'200 fn fixture\r\n'

    def command(self, command):
        self.send(command + b'\r\n')
        return self.line()

    def send(self, command):
        self.queued.append(command)

    def line(self):
        if self.closed:
            raise EOFError('fake closed')
        if not self.queued:
            raise AssertionError('fake unexpected read')
        command = self.queued.pop(0)
        if command.startswith(b'481') or command.startswith(b'400'):
            if command.startswith(b'400'):
                self.closed = True
            return command
        self.answered = True
        if self.body:
            self.body = False
            if self.login:
                self.target.posts += 1
            return b'240 article accepted\r\n' if b'Message-ID:' in command else b'441 malformed article\r\n'
        if command == b'QUIT\r\n':
            self.closed = True
            return b'205 closing\r\n'
        if command.startswith(b'AUTHINFO USER '):
            self.user = command.split()[2]
            return b'381 password required\r\n'
        if command.startswith(b'AUTHINFO PASS '):
            if self.user == b'hw-poster' and command.split()[2] == b'hw-fixture-password':
                self.login = True
                return b'281 authentication accepted\r\n'
            self.failed += 1
            self.target.failures += 1
            limit = int(self.target.wire_values['exposure-auth-failures'])
            if self.failed >= 3 or limit and self.target.failures >= limit:
                self.queued.insert(0, b'400 too many authentication failures; closing connection\r\n')
            return b'481 authentication rejected\r\n'
        if command == b'POST\r\n':
            self.body = True
            return b'340 send article\r\n'
        if command == b'DATE\r\n':
            return b'111 20261029120000\r\n'
        raise AssertionError('fake unsupported command ' + repr(command))

    def observe(self, seconds):
        if self.closed:
            return b'', True
        v = self.target.wire_values
        limit = int(v['exposure-posts-per-minute'])
        if self.queued and self.login and limit and self.target.posts >= limit:
            return b'', False
        timer = int(v['exposure-idle-seconds' if self.answered else 'exposure-first-seconds'])
        if timer and seconds >= timer:
            self.observed_elapsed = float(timer)
            self.closed = True
            return (b'400 timeout\r\n' if self.target.plant == 'deadline-reply' else b''), True
        if self.queued:
            return self.line(), False
        return b'', False

    def close(self):
        self.closed = True


class LimitsTests(unittest.TestCase):
    def test_defaults_are_listener_specific_and_store_defaults_are_inputs(self):
        loop, public = LimitsModel(), LimitsModel(public=True)
        self.assertEqual([public.get(k) for k in ('exposure-connections', 'exposure-per-address',
            'exposure-steps-per-second', 'exposure-first-seconds', 'exposure-idle-seconds',
            'exposure-auth-failures', 'exposure-posts-per-minute')], [31, 8, 64, 60, 600, 10, 60])
        self.assertEqual(loop.get('exposure-per-address'), 31)
        self.assertEqual(loop.get('exposure-first-seconds'), 0)
        self.assertEqual(LimitsModel(store_defaults={'max-transactions': 999}).get('max-transactions'), 999)
        self.assertEqual(ADJUDICATIONS, ())
        self.assertEqual(set(VALID), set(KEYS))

    def test_numeric_boundaries_and_named_type_refusals(self):
        for key, spec in KEYS.items():
            if spec.kind not in ('count', 'store'):
                continue
            with self.subTest(key=key):
                for n in (spec.minimum, spec.maximum):
                    self.assertEqual(parse_value(key, str(n)), (n, None))
                self.assertIsNotNone(parse_value(key, str(spec.maximum + 1))[1])
                for value in ('-1', '1.0', 'true', '1e3', '01'):
                    self.assertEqual(parse_value(key, value)[1], 'policy-value-not-a-number')

    def test_text_types_ranges_and_override_boundaries(self):
        for key, values in VALID.items():
            for value in values:
                self.assertIsNone(parse_value(key, value)[1], (key, value))
        for value in ('0.0.0.0/0', '::/0', '127.0.0.1/33', 'host.invalid', '::ffff:127.0.0.1'):
            self.assertEqual(parse_value('exposure-trusted', value)[1], 'policy')
        for value in ('a..b@example.org', 'a@example..org', '"a"@example.org', 'a@b\r\n'):
            self.assertEqual(parse_value('complaints-to', value)[1], 'policy')
        entries = ','.join('127.0.0.%d=1' % n for n in range(1, 65))
        self.assertIsNone(parse_value('tls-handshake-source-overrides', entries)[1])
        self.assertEqual(parse_value('tls-handshake-source-overrides', entries + ',127.0.0.65=1')[1], 'overrides-full')

    def test_refusal_preserves_model_state_and_funding(self):
        model = LimitsModel()
        before = {k: model.get(k) for k in KEYS}, dict(model.funded), dict(model.rows)
        for key, value in [('exposure-connections', str(U32+1)), ('unknown', '1'),
                           ('exposure-connections', 'banana'), ('max-article-octets', str(U32+1))]:
            expected = model.set(key, value)
            expected.update({'exit': 1, 'text': 'refused ' + expected.reason})
            self.assertEqual(({k: model.get(k) for k in KEYS}, model.funded, model.rows), before)

    def test_success_accepts_any_line_with_exit_zero(self):
        model = LimitsModel()
        for text in ('', 'accepted', 'applied exposure-connections=2', 'unspecified success line'):
            expected = model.set('exposure-connections', '2')
            self.assertIsNone(expected.check({'exit': 0, 'text': text}))
            self.assertIsNotNone(expected.check({'exit': 1, 'text': text}))
            expected.update({'exit': 0, 'text': text})
            self.assertEqual(model.get('exposure-connections'), 2)

    def test_fixed_live_path_on_independent_fake(self):
        fake = FakeTarget()
        Exercise(self, fake).witnesses()
        self.assertLessEqual(fake.opened, 64)
        self.assertTrue(all(s.closed for s in fake.sockets))

    def test_generated_machine_on_independent_fake(self):
        from hypothesis import settings, Phase
        from hypothesis.stateful import run_state_machine_as_test
        run_state_machine_as_test(machine(self, target_factory=FakeTarget), settings=settings(
            max_examples=200, stateful_step_count=30, deadline=None, database=None,
            derandomize=True, phases=(Phase.generate,), report_multiple_bugs=False))

    def test_mutation_accept_out_of_range(self):
        with self.assertRaisesRegex(AssertionError, 'named refusal'):
            Exercise(self, FakeTarget(plant='out-of-range')).set('exposure-connections', U32+1)

    def test_mutation_success_but_stale_wire(self):
        with self.assertRaisesRegex(AssertionError, 'mandatory EOF|code 200'):
            Exercise(self, FakeTarget(plant='stale-wire')).capacity()

    def test_mutation_capacity_refusal_without_close(self):
        with self.assertRaisesRegex(AssertionError, 'mandatory EOF'):
            Exercise(self, FakeTarget(plant='capacity-no-close')).capacity()

    def test_mutation_refused_set_changes_wire_limit(self):
        with self.assertRaisesRegex(AssertionError, 'mandatory EOF|code 200'):
            Exercise(self, FakeTarget(plant='refusal-mutation')).capacity()

    def test_mutation_wrong_refusal_reason(self):
        with self.assertRaisesRegex(AssertionError, 'named refusal'):
            Exercise(self, FakeTarget(plant='wrong-reason')).set('hw-unknown', '1')

    def test_mutation_deadline_emits_reply(self):
        with self.assertRaises(AssertionError):
            Exercise(self, FakeTarget(plant='deadline-reply')).deadlines()

    def test_wire_policy_is_live_but_other_policy_stays_pinned(self):
        policy = LimitsModel()
        model = NntpModel({}, [], {}, {'posting': True}, limits=policy)
        old = model.connect(tls=False, implicit_tls=False)
        policy.set('exposure-connections', '1').update({'exit': 0, 'text': 'accepted'})
        full = model.connect(tls=False, implicit_tls=False)
        self.assertTrue(full.greeting().check(b'400 too many connections; try again later\r\n', None, eof=True).ok)
        self.assertFalse(full.greeting().check(
            b'400 too many connections from this address; try again later\r\n', None, eof=True).ok)
        self.assertEqual(old.policy, {'posting': True, 'anonymous': 'open'})
        policy.set('exposure-connections', '3').update({'exit': 0, 'text': 'accepted'})
        full.greeting().update(b'400 too many connections; try again later\r\n', None, eof=True)
        self.assertTrue(model.connect(tls=False, implicit_tls=False).greeting().check(b'200 fn\r\n', None).ok)

    def test_wait_and_deadline_need_their_antecedents(self):
        model = NntpModel({}, [], {}, {}, limits=LimitsModel())
        conn = model.connect(tls=False, implicit_tls=False)
        with self.assertRaises(ValueError):
            conn.exposure_wait('posts')
        with self.assertRaises(ValueError):
            conn.exposure_deadline(elapsed=1000, first=True)
        model.limits.set('exposure-first-seconds', '1').update({'exit': 0, 'text': 'accepted'})
        expected = conn.exposure_deadline(elapsed=1, first=True)
        self.assertFalse(expected.check(b'400 timeout\r\n', None, eof=True).ok)
        expected.update(b'', None, eof=True)
        self.assertTrue(conn.quit)


if __name__ == '__main__':
    unittest.main()

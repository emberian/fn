"""HW independent fake, schema boundaries, composed wire tests and mutants.

The fake implements only the finite HW workload, never calls LimitsModel,
parse_value, NntpModel or Expect, and owns separate policy/wire dictionaries.
Literal defaults and wire bytes intentionally duplicate facts as a control.
This is not live-server evidence. No TCP bind or native image is needed.
"""
import json
from pathlib import Path
import re
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from .limits_model import (ADJUDICATIONS, KEYS, LimitsModel, OperatorExpectation,
    STORE_DEFAULTS, STORE_INIT, U32, init_history_expectation, parse_value, recorded_greeting)
from .nntp_model import NntpModel
from fn2.tests.surface.config_limits.test_model_config_limits import (
    Exercise, LISTENER_REFUSALS, init_store, machine, VALID)


# Minimal independent transcription of all 28 mismatches, not derived from the
# adjudication table. The optional seat file adds its full text and 124 controls.
HY_PAIRS = (
    ('exposure-trusted', '???', 5, 'POLICY', 'L03'),
    ('anonymous', '???', 5, 'POLICY', 'L03'),
    ('tls-handshakes-per-source-per-minute', 'wrong', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('tls-handshakes-per-source-per-minute', '-1', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('tls-handshakes-in-flight', 'wrong', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('tls-handshakes-in-flight', '-1', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('tls-handshake-ms', 'wrong', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('tls-handshake-ms', '-1', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('tls-handshake-source-overrides', '???', 5, 'OVERRIDE-ADDRESS', 'L04'),
    ('log-batch-records', 'wrong', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('log-batch-records', '-1', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('log-batch-octets', 'wrong', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('log-batch-octets', '-1', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('barrier-deadline-ms', 'wrong', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('barrier-deadline-ms', '-1', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('barrier-stall-ms', 'wrong', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('barrier-stall-ms', '-1', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('clock-event-ms', 'wrong', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('clock-event-ms', '-1', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('disk-reserve-octets', 'wrong', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('disk-reserve-octets', '-1', 1, 'UNKNOWN-POLICY-KEY', 'L02'),
    ('relay-date-skew', '86401', 5, 'POLICY', 'L06'),
    ('relay-require-path', 'wrong', 5, 'POLICY', 'L05'),
    ('relay-require-path', '-1', 5, 'POLICY', 'L05'),
    ('relay-require-path', '2', 5, 'POLICY', 'L05'),
    ('path-identity', '???', 5, 'POLICY', 'L03'),
    ('posting-policy', '???', 5, 'POLICY', 'L03'),
    ('complaints-to', '???', 5, 'POLICY', 'L03'),
)
HY_GREETING = b'400 too many authentication failures from this address; try again later\r\n'


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
            '4096', '0', 'unset', 'open', 'unset', '4096', '25165824', '32768')))
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
    def test_hy_embedded_pairs_target_scope_and_unchanged_state(self):
        self.assertEqual(len(HY_PAIRS), 28)
        for key, value, exit_code, reason, group in HY_PAIRS:
            for target in ('fn1', 'fn2', 'fake', 'other'):
                with self.subTest(key=key, value=value, target=target):
                    model = LimitsModel()
                    model.set('exposure-connections', '2').update({'exit': 0, 'text': ''})
                    before = dict(model.rows), dict(model.funded)
                    expected = model.set(key, value)
                    # Prose can change; the exact parenthesized reason cannot.
                    reply = dict(exit=exit_code, text=f'any prose (ADMINISTRATION {reason})\n')
                    allowed = target == 'fn1' or target == 'fn2' and group in ('L03', 'L05', 'L06')
                    recorded = expected.recorded_difference(reply, target)
                    self.assertEqual(recorded is not None, allowed)
                    self.assertIsNotNone(expected.check(reply))
                    if allowed:
                        self.assertEqual(recorded['group'], group)
                        self.assertEqual(expected.update(reply, target), recorded)
                    else:
                        with self.assertRaises(AssertionError):
                            expected.update(reply, target)
                    self.assertEqual((model.rows, model.funded), before)

    def test_hy_optional_full_seat_pairs(self):
        path = Path(__file__).resolve().parents[3] / 'build/hy-evidence/hy-policy-pairs-fn1.json'
        if not path.exists():
            self.skipTest('optional full seat file absent; all 28 minimal rows tested independently')
        rows = json.loads(path.read_text())
        self.assertEqual(len(rows), 152)
        mismatches = {(r['key'], r['value']) for r in rows if r['verdict'] is not None}
        self.assertEqual(mismatches, {(k, v) for k, v, *_ in HY_PAIRS})
        for row in rows:
            with self.subTest(key=row['key'], value=row['value']):
                expected = LimitsModel().set(row['key'], row['value'])
                reply = {k: row[k] for k in ('exit', 'text')}
                recorded = expected.recorded_difference(reply, 'fn1')
                self.assertTrue(expected.check(reply) is None or recorded is not None)
                if recorded:
                    self.assertEqual(row['text'], recorded['witness'])
                else:
                    self.assertIsNone(row['verdict'])
                expected.update(reply, 'fn1')

    def test_hy_set_planted_variants_fail_through_live_checks(self):
        for key, value, exit_code, reason, _ in HY_PAIRS:
            original = dict(exit=exit_code, text=f'policy set (ADMINISTRATION {reason})\n')
            outside = 'max-transactions' if exit_code == 5 else 'exposure-connections'
            # A known valid value with this refusal must fail as well.
            valid = VALID[key][0]
            variants = [
                (key, value, dict(original, exit=4)),
                (key, value, dict(original, text='policy set (ADMINISTRATION OTHER)\n')),
                (key, value, dict(original, text=f'policy set (ADMINISTRATION {reason}-SUFFIX)\n')),
                (key, value, dict(original, text=f'policy set {reason}\n')),
                (outside, value, original), (key, valid, original),
            ]
            for k, v, reply in variants:
                with self.subTest(key=k, value=v, reply=reply):
                    expected = LimitsModel().set(k, v)
                    self.assertIsNone(expected.recorded_difference(reply, 'fn1'))
                    self.assertIsNotNone(expected.check(reply))
                    target = SimpleNamespace(adjudication_target='fn1', set=lambda *_: reply)
                    exercise = Exercise(self, target)
                    with patch('fn2.tests.surface.config_limits.test_model_config_limits.record_failure') as failure:
                        with self.assertRaises(AssertionError):
                            exercise.set(k, v)
                        self.assertEqual(failure.call_args_list[0].kwargs['reply'], reply)
                    self.assertEqual(exercise.policy.rows, {})

    def test_hy_live_set_records_step_and_reply(self):
        for key, value, exit_code, reason, group in HY_PAIRS:
            with self.subTest(key=key, value=value):
                case = unittest.TestCase()
                case.evidence = {}
                reply = dict(exit=exit_code, text=f'(ADMINISTRATION {reason})\n')
                target = SimpleNamespace(adjudication_target='fn1', set=lambda *_: reply)
                exercise = Exercise(case, target)
                exercise.set(key, value)
                recorded, = case.evidence['recorded_differences']
                self.assertEqual((recorded['group'], recorded['step'], recorded['key'], recorded['value']),
                                 (group, 1, key, value))
                self.assertEqual(recorded['observed_reply'], reply)
                self.assertEqual(exercise.policy.rows, {})

    def test_hy_greeting_live_path_closes_and_records_only_on_fn1(self):
        class SeatTarget(FakeTarget):
            def open(self):
                wire = super().open()
                if wire.greeting == b'400 too many authentication failures from this address\r\n':
                    wire.greeting = HY_GREETING
                return wire

        for target in ('fn1', 'fn2', 'fake'):
            fake = SeatTarget()
            fake.adjudication_target = target
            case = unittest.TestCase()
            exercise = Exercise(case, fake)
            if target == 'fn1':
                case.evidence = {}
                exercise.authentication()
                row, = case.evidence['recorded_differences']
                self.assertEqual((row['group'], row['command']), ('L01', 'greeting'))
                self.assertEqual(row['observed_reply'], dict(status={'hex': HY_GREETING.hex()}, eof=True))
                self.assertEqual(exercise.trace[row['step'] - 1]['status'], HY_GREETING.hex())
                self.assertEqual(exercise.wire_model.address_failures['127.0.0.1'], 2)
                self.assertTrue(all(conn.quit for conn in exercise.wire_model.connections))
            else:
                with patch('fn2.tests.surface.config_limits.test_model_config_limits.record_failure') as failure:
                    with self.assertRaises(AssertionError):
                        exercise.authentication()
                    self.assertEqual(failure.call_args_list[0].kwargs['reply'],
                                     dict(status=HY_GREETING, eof=True))

    def test_hy_greeting_variants_and_wrong_antecedents_fail(self):
        for status, eof, request, cause in (
            (HY_GREETING, False, None, 'auth'),
            (HY_GREETING.replace(b'400', b'502'), True, None, 'auth'),
            (HY_GREETING.replace(b'later', b'soon'), True, None, 'auth'),
            (HY_GREETING + b'extra\r\n', True, None, 'auth'),
            (HY_GREETING, True, b'AUTHINFO PASS wrong', 'auth'),
            (HY_GREETING, True, None, 'capacity'),
            (HY_GREETING, True, None, 'open'),
        ):
            with self.subTest(status=status, eof=eof, request=request, cause=cause):
                exercise = Exercise(self, SimpleNamespace(adjudication_target='fn1'))
                if cause == 'auth':
                    exercise.policy.rows['exposure-auth-failures'] = 1
                    exercise.wire_model.address_failures['127.0.0.1'] = 1
                elif cause == 'capacity':
                    exercise.policy.rows['exposure-connections'] = 0
                conn = exercise.wire_model.connect(tls=False, implicit_tls=False)
                expected = conn.greeting()
                self.assertIsNone(recorded_greeting(expected, status, eof=eof, target='fn1', request=request))
                with patch('fn2.tests.surface.config_limits.test_model_config_limits.record_failure') as failure:
                    with self.assertRaises(AssertionError):
                        exercise.check(expected, status, eof=eof, request=request)
                    self.assertEqual(failure.call_args.kwargs['reply'], dict(status=status, eof=eof))
                self.assertFalse(conn.quit)

    def test_init_history_relation_and_named_refusal(self):
        # Vary R: the relation must not be a constant copied from a live reply.
        for record in (196608, 24 * 1024 * 1024, 64 * 1024 * 1024):
            for history in (record - 1, record, record + 1):
                expected = init_history_expectation(history, record)
                refused = history < record
                result = {'exit': 1 if refused else 0, 'text': (
                    'refused operator init MAX-HISTORY-OCTETS-BELOW-MAX-RECORD-OCTETS'
                    if refused else 'accepted')}
                self.assertIsNone(expected.check(result))
                self.assertIsNotNone(expected.check({**result, 'exit': 5}))
                if refused:
                    for text in ('host', 'profile-invalid',
                        'prefix-MAX-HISTORY-OCTETS-BELOW-MAX-RECORD-OCTETS-suffix'):
                        self.assertIsNotNone(expected.check({**result, 'text': text}))

    def test_live_init_passes_explicit_record_and_derived_history(self):
        calls = []

        class InitTarget:
            def operator(self, *args, **kwargs):
                calls.append((args, kwargs))
                record = int(args[args.index('--max-record-octets') + 1])
                history = int(args[args.index('--max-history-octets') + 1])
                return SimpleNamespace(returncode=1 if history < record else 0,
                    stdout=b'refused MAX-HISTORY-OCTETS-BELOW-MAX-RECORD-OCTETS'
                           if history < record else b'accepted', stderr=b'')

        init_store(self, InitTarget())
        init_store(self, InitTarget(), history_octets=STORE_INIT['max-record-octets'] - 1)
        self.assertGreaterEqual(STORE_DEFAULTS['max-history-octets'], STORE_INIT['max-record-octets'])
        self.assertEqual(len(calls), 2)
        for args, kwargs in calls:
            self.assertEqual(args[:3], ('init', '--profile', 'development'))
            self.assertEqual(kwargs, {'timeout': 10})
            self.assertEqual(set(args[3:-1:2]), {'--' + key for key in STORE_INIT})

    def test_listener_named_usage_refusals(self):
        self.assertEqual(dict(LISTENER_REFUSALS), {
            'not-an-address.invalid': 'listener-address',
            '0.0.0.0': 'listener-unspecified', '::': 'listener-unspecified',
            '::ffff:127.0.0.1': 'listener-mapped'})
        for host, reason in LISTENER_REFUSALS:
            expected = OperatorExpectation(5, reason)
            result = {'exit': 5, 'text': f'usage operator request (configuration {reason})'}
            self.assertIsNone(expected.check(result), host)
            self.assertIsNotNone(expected.check({**result, 'exit': 1}))
            self.assertIsNotNone(expected.check({**result, 'text': 'host'}))

    def test_defaults_are_listener_specific_and_store_defaults_are_inputs(self):
        loop, public = LimitsModel(), LimitsModel(public=True)
        self.assertEqual([public.get(k) for k in ('exposure-connections', 'exposure-per-address',
            'exposure-steps-per-second', 'exposure-first-seconds', 'exposure-idle-seconds',
            'exposure-auth-failures', 'exposure-posts-per-minute')], [31, 8, 64, 60, 600, 10, 60])
        self.assertEqual(loop.get('exposure-per-address'), 31)
        self.assertEqual(loop.get('exposure-first-seconds'), 0)
        self.assertEqual(LimitsModel(store_defaults={'max-transactions': 999}).get('max-transactions'), 999)
        self.assertEqual({row['group'] for row in ADJUDICATIONS},
                         {'L01', 'L02', 'L03', 'L04', 'L05', 'L06'})
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

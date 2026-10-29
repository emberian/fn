"""Spec-derived controls, golden observations, and seeded property histories."""
from copy import deepcopy
from dataclasses import replace
import base64
import io
import json
from pathlib import Path
import unittest

from hypothesis import given, settings, strategies as st

from . import consumer, durable, synthetic
from .from_observe import adapt, cursor
from .history import HistoryError, Record, pair, read_jsonl, write_jsonl

SEEDS = st.integers(min_value=0, max_value=2**32 - 1)
FIXTURES = Path(__file__).with_name('fixtures')
CAUGHT = {}


def kinds(h):
    return [a.kind for a in consumer.check(h) + durable.check(h)]


def scenario():
    b = synthetic.Builder(17)
    c = synthetic.registration()
    b.op('register', c, response={'position': 0})
    return b, c


class HistoryTests(unittest.TestCase):
    @settings(max_examples=200, deadline=None, database=None, derandomize=True)
    @given(SEEDS)
    def test_valid_histories(self, seed):
        h = synthetic.valid(seed)
        original = deepcopy(h)
        self.assertEqual(consumer.check(h), [])
        self.assertEqual(durable.check(h), [])
        self.assertEqual(h, original, 'checkers must not mutate their input')
        stream = io.StringIO()
        write_jsonl(h, stream)
        self.assertEqual(read_jsonl(io.StringIO(stream.getvalue())), h)
        self.assertEqual(synthetic.valid(seed), h)

    def test_named_well_formedness_errors(self):
        invoke = Record('p', 'invoke', 'read', {}, 10, 0)
        ok = Record('p', 'ok', 'read', {}, 20, 1)
        cases = [('completion-without-invoke', [ok]),
                 ('two-invokes', [invoke, replace(invoke, index=1, time=11)]),
                 ('time-backwards', [invoke, replace(ok, time=9)]),
                 ('incomplete-without-crash', [invoke]),
                 ('function-mismatch', [invoke, replace(ok, f='post')]),
                 ('index-order', [invoke, replace(ok, index=0)])]
        for kind, h in cases:
            with self.subTest(kind=kind), self.assertRaises(HistoryError) as raised:
                pair(h)
            self.assertEqual(raised.exception.kind, kind)
        with self.assertRaises(HistoryError) as raised:
            read_jsonl(io.StringIO('{oops}\n'))
        self.assertEqual(raised.exception.kind, 'invalid-json')

    def test_crash_closes_every_process_on_that_node(self):
        b = synthetic.Builder()
        b.record('a', 'invoke', 'post', {'node': 'A'})
        b.record('b', 'invoke', 'ack', {'node': 'A'})
        b.record('c', 'invoke', 'read', {'node': 'B'})
        b.op('crash', {'node': 'A', 'cut': 'commit'}, process='nemesis')
        b.record('c', 'ok', 'read', {})
        paired = pair(b.history)
        self.assertEqual({o.invoke.process: o.type for o in paired},
                         {'a': 'info', 'b': 'info', 'c': 'ok', 'nemesis': 'ok'})
        b.record('a', 'ok', 'post', {})
        with self.assertRaises(HistoryError) as raised:
            pair(b.history)
        self.assertEqual(raised.exception.kind, 'completion-without-invoke')

    def test_equal_and_failed_lower_ack(self):
        b, c = scenario()
        b.op('ack', c | {'position': 3})
        b.op('ack', c | {'position': 3})
        b.op('ack', c | {'position': 2}, phase='fail', response={'reason': 'lower'})
        b.restart()
        b.op('position', c, response={'position': 3})
        self.assertEqual(kinds(b.history), [])

    def test_recovered_position_bounds(self):
        for answer in (2, 6):
            b, c = scenario()
            b.op('ack', c | {'position': 3})
            b.op('ack', c | {'position': 5}, phase='info')
            b.restart()
            b.op('position', c, response={'position': answer})
            self.assertEqual(kinds(b.history), ['C1'])
        for answer in (3, 5):
            b, c = scenario()
            b.op('ack', c | {'position': 3})
            b.op('ack', c | {'position': 5}, phase='info')
            b.restart()
            b.op('position', c, response={'position': answer})
            self.assertEqual(kinds(b.history), [])

    def test_confirmed_info_ack_is_durable(self):
        b, c = scenario()
        b.op('ack', c | {'position': 4}, phase='info')
        b.restart()
        b.op('position', c, response={'position': 4})
        b.op('ack', c | {'position': 3})
        self.assertEqual(kinds(b.history), ['C1'])

    def test_redelivery_obligation_and_confirmation(self):
        for confirmed in (False, True):
            b, c = scenario()
            b.op('poll', c | {'cursor': 0}, response={'events': [[2, '<x>']], 'position': 2, 'more': False})
            b.op('ack', c | {'position': 2}, phase='info')
            b.op('poll', c | {'cursor': 2}, response={'events': [], 'position': 2, 'more': False})
            if confirmed:
                b.op('position', c, response={'position': 2})
            self.assertEqual(kinds(b.history), [] if confirmed else ['C2'])

    def test_short_scan_not_lost_and_eof_not_liveness(self):
        b, c = scenario()
        b.op('poll', c | {'cursor': 0}, response={'events': [[4, '<x>']], 'position': 4, 'more': False})
        b.op('poll', c | {'cursor': 0}, response={'events': [], 'position': 2, 'more': True})
        self.assertEqual(kinds(b.history), [])
        b.op('poll', c | {'cursor': 0}, response={'events': [], 'position': 4, 'more': False})
        self.assertEqual(kinds(b.history), ['C2'])

    def test_overlapping_page_before_ack_is_allowed(self):
        b, c = scenario()
        b.record('reader', 'invoke', 'poll', c | {'cursor': 0})
        b.op('ack', c | {'position': 1})
        b.record('reader', 'ok', 'poll', {'events': [[1, '<x>']], 'position': 1, 'more': False})
        self.assertEqual(kinds(b.history), [])

    def test_wait_slack_visibility_ack_and_deadline(self):
        b, c = scenario()
        deadline = b.time + 1000
        start = b.record('waiter', 'invoke', 'wait', c | {'cursor': 0, 'deadline': deadline})
        visible = dict(consumer='c', epoch=1, scope=c['scope'], position=1)
        post = b.op('post', {'message_id': '<x>', 'digest': 'x', 'visible': [visible]}, response={'code': 240})
        b.record('waiter', 'ok', 'wait', {'events': [], 'position': 0, 'more': False}, at=deadline)
        delta = post.time - start.time
        self.assertEqual(consumer.check(b.history, slack_ns=delta), [])
        self.assertEqual([a.kind for a in consumer.check(b.history, slack_ns=delta+1)], ['C4'])
        hidden = [replace(r, value=r.value | {'visible': []}) if r.f == 'post' else r for r in b.history]
        self.assertEqual(consumer.check(hidden, slack_ns=delta+1), [])
        b2, c = scenario()
        b2.op('wait', c | {'cursor': 1, 'deadline': b2.time+100}, response={
            'events': [[1, '<x>']], 'position': 1, 'more': False})
        self.assertEqual(kinds(b2.history), ['C4'])
        with self.assertRaises(ValueError):
            consumer.check([], slack_ns=-1)

    def test_poll_does_not_move_position_and_ack_can_overlap(self):
        b, c = scenario()
        b.op('poll', c | {'cursor': 0}, response={'events': [], 'position': 10, 'more': False})
        b.op('position', c, response={'position': 0})
        b.record('observer', 'invoke', 'position', c)
        b.op('ack', c | {'position': 10})
        b.record('observer', 'ok', 'position', {'position': 10})
        self.assertEqual(kinds(b.history), [])

    def test_scope_reset_and_message_id_is_not_position(self):
        b, c = scenario()
        b.op('poll', c | {'cursor': 0}, response={'events': [[1, '<x>'], [2, '<x>']], 'position': 2, 'more': False})
        b.op('ack', c | {'position': 2})
        new = synthetic.registration(view=1)
        b.op('rebase', new, response={'position': 0})
        b.op('poll', new | {'cursor': 0}, response={'events': [[1, '<x>']], 'position': 1, 'more': False})
        self.assertEqual(kinds(b.history), [])
        b.op('ack', c | {'position': 2})
        self.assertEqual(kinds(b.history), ['C5'])

    def test_withdrawal_and_refused_duplicate_are_not_loss(self):
        b = synthetic.Builder()
        v = {'message_id': '<x>', 'digest': 'body'}
        b.op('post', v, response={'code': 240})
        b.op('post', v, phase='fail', response={'code': 441, 'reason': 'duplicate'})
        b.restart()
        b.op('read', {'message_id': '<x>'}, response={'code': 220, 'digest': 'body'})
        b.op('withdraw', {'message_id': '<x>', 'authorized': True})
        b.op('read', {'message_id': '<x>'}, response={'code': 430})
        self.assertEqual(kinds(b.history), [])
        unauthorized = [replace(r, value=r.value | {'authorized': False}) if r.f == 'withdraw' else r for r in b.history]
        self.assertEqual(kinds(unauthorized), ['D1'])

    def test_wrong_digest_and_recovery_crashes(self):
        b = synthetic.Builder()
        b.op('post', {'message_id': '<x>', 'digest': 'body'}, response={'code': 240})
        b.restart()
        b.record('recovering', 'invoke', 'recover', {'posture': 'ready'})
        b.restart()
        b.op('read', {'message_id': '<x>'}, response={'code': 220, 'digest': 'changed'})
        self.assertEqual(kinds(b.history), ['D1'])

    def test_uncertain_retry_can_change_absence_to_presence(self):
        b = synthetic.Builder()
        v = {'message_id': '<x>', 'digest': 'body'}
        b.op('post', v, phase='info', response={'code': 441, 'reason': 'uncertain'})
        b.restart()
        b.op('read', {'message_id': '<x>'}, response={'code': 430})
        b.op('post', v, response={'code': 240})
        b.op('read', {'message_id': '<x>'}, response={'code': 220, 'digest': 'body'})
        self.assertEqual(kinds(b.history), [])

    def test_adapter_golden_and_all_unmapped_counts(self):
        expected_counts = {'consumer': {},
                           'wire': {'client.line:': 8, 'client.command:POST': 1}, 'captured': {}}
        for name, counts in expected_counts.items():
            with self.subTest(fixture=name):
                source = [json.loads(line) for line in (FIXTURES / f'{name}.jsonl').read_text().splitlines()]
                actual = adapt(source)
                self.assertEqual(actual.history, read_jsonl(FIXTURES / f'{name}.expected.jsonl'))
                self.assertEqual(actual.counts, counts)
                self.assertEqual(len(actual.unmapped), sum(counts.values()))
                self.assertTrue(all(item['reason'] for item in actual.unmapped))
                self.assertEqual(kinds(actual.history), [])

    def test_captured_session_crash_and_planted_loss(self):
        source = [json.loads(line) for line in (FIXTURES / 'captured.jsonl').read_text().splitlines()]
        result = adapt(source)
        self.assertEqual(result.unmapped, [])
        self.assertEqual([o.f for o in pair(result.history)],
                         ['recover', 'register', 'post', 'wait', 'poll', 'ack', 'crash',
                          'recover', 'position', 'read'])
        self.assertEqual(kinds(result.history), [])
        without_more = [r | {'history_value': {}} for r in source]
        self.assertEqual(adapt(without_more).counts, {'invoke:consumer': 2})
        self.assertEqual(next(o.value['cut'] for o in pair(result.history) if o.f == 'crash'), 'CUT')
        # The read command's negative answer has no multiline body.
        source = [r for r in source if r['kind'] != 'client.block']
        for r in source:
            if r.get('reply_hex', '').startswith(b'220'.hex()):
                r['reply_hex'] = b'430 no article\r\n'.hex()
            if r['kind'] == 'client.multiline' and r['phase'] == 'ok':
                r['replies_hex'] = [b'430 no article\r\n'.hex(), '']
        loss = adapt(source)
        self.assertEqual(loss.unmapped, [])
        self.assertEqual(consumer.check(loss.history), [])
        self.assertEqual([a.kind for a in durable.check(loss.history)], ['D1'])

    def test_call_ids_separate_overlapping_connections_and_truncated_send(self):
        source = []
        def record(conn, call, kind, phase, **fields):
            source.append(dict(t=len(source), test='overlap', node='N', conn=conn,
                               call=call, kind='client.' + kind, phase=phase, **fields))
        for conn in ('a', 'b'):
            record(conn, conn, 'command', 'invoke', command_hex=b'POST'.hex())
        for conn in ('b', 'a'):
            record(conn, conn, 'command', 'ok', command_hex=b'POST'.hex(), reply_hex=b'340 send\r\n'.hex())
            for phase in ('invoke', 'ok'):
                record(conn, conn+'s', 'send', phase,
                       sent_hex=f'Message-ID: <{conn}>\r\n\r\n..body\r\n.\r\n'.encode().hex())
            record(conn, conn+'r', 'line', 'invoke')
            record(conn, conn+'r', 'line', 'ok', reply_hex=b'240 accepted\r\n'.hex())
        result = adapt(source)
        self.assertEqual(result.unmapped, [])
        self.assertEqual({o.value['message_id'] for o in pair(result.history)}, {'<a>', '<b>'})
        for r in source:
            if r['kind'] == 'client.send':
                r.update(sent_sha256='hash-of-wire', sent_len=2000000)
        self.assertTrue(all(o.value['observed_only'] for o in pair(adapt(source).history)))

    def test_adapter_uncertain_441_not_fail(self):
        source = [dict(t=1, test='x', kind='client.command', phase='invoke', command_hex=b'POST'.hex(),
                       history_value={'message_id': '<x>', 'digest': 'body'}),
                  dict(t=2, test='x', kind='client.command', phase='ok', command_hex=b'POST'.hex(),
                       reply_hex=b'441 outcome uncertain\r\n'.hex())]
        result = adapt(source)
        self.assertEqual(pair(result.history)[0].type, 'info')
        self.assertEqual(result.counts, {})

    def test_own_cancel_observation_regression_and_refusal_control(self):
        source = [json.loads(line) for line in (FIXTURES / 'own-cancel.jsonl').read_text().splitlines()]
        actual = adapt(source)
        self.assertEqual(actual.unmapped, [])
        self.assertEqual(kinds(actual.history), [])
        before = [r for r in actual.history if r.f != 'withdraw']
        self.assertEqual(kinds(before), ['D1'])
        withdrawal = next(o for o in pair(actual.history) if o.f == 'withdraw')
        self.assertEqual(withdrawal.value['cause_call'], '575195:111')
        self.assertEqual(withdrawal.value['message_id'], '<own-target@example.invalid>')
        for reply, phase in [(b'441 unauthorized\r\n', 'fail'),
                             (b'441 outcome uncertain\r\n', 'info')]:
            refused = deepcopy(source)
            next(r for r in refused if r['call'] == '575195:115' and r['phase'] == 'ok')['reply_hex'] = reply.hex()
            h = adapt(refused).history
            self.assertEqual(kinds(h), ['D1'])
            self.assertEqual(next(o.type for o in pair(h) if o.f == 'withdraw'), phase)
        present = deepcopy(source)
        present[-1]['reply_hex'] = b'223 1 <own-target@example.invalid> present\r\n'.hex()
        self.assertEqual(kinds(adapt(present).history), [])

    def test_cancel_observed_on_peer_not_before(self):
        source = [json.loads(line) for line in (FIXTURES / 'own-cancel.jsonl').read_text().splitlines()]
        # Keep only target and accepted cancel submission; add a separate node.
        source = [r for r in source if int(r['call'].split(':')[1]) <= 115]
        end = source[-1]['t']
        def read(call, command, code):
            for phase in ('invoke', 'ok'):
                r = dict(t=end + len(source), kind='client.command', phase=phase,
                         call=call, conn='peer-connection', node='peer', command_hex=command.encode().hex())
                if phase == 'ok':
                    r['reply_hex'] = f'{code} result\r\n'.encode().hex()
                source.append(r)
        read('before', 'STAT <own-target@example.invalid>', 430)
        read('cause', 'STAT <own-cancel-alice@example.invalid>', 223)
        read('after', 'STAT <own-target@example.invalid>', 430)
        ops = pair(adapt(source).history)
        peer_withdrawals = [o for o in ops if o.f == 'withdraw' and o.node == 'peer']
        self.assertEqual(len(peer_withdrawals), 1)
        peer = peer_withdrawals[0]
        self.assertEqual(peer.value['cause_call'], '575195:111')
        self.assertEqual(peer.invoke.time, source[-3]['t'])
        self.assertLess(next(o.completion.index for o in ops if o.f == 'read' and o.value['code'] == 430), peer.invoke.index)

    def test_operator_withdraw_requires_success(self):
        for exit_code, outcome, expected in [(0, 'ok', 'ok'), (1, 'fail', 'fail'),
                                              (None, 'info', 'info')]:
            source = [dict(t=1, kind='operator', phase='invoke', call='op', node='N',
                           words=['article', 'withdraw', '<x>'])]
            source.append(source[0] | dict(t=2, phase=outcome, exit_code=exit_code))
            operation = pair(adapt(source).history)[0]
            self.assertEqual(operation.f, 'withdraw')
            self.assertEqual(operation.type, expected)
            self.assertEqual(operation.value.get('authorized', False), expected == 'ok')

    def test_peer_cancel_transfer_outcome_is_local(self):
        source = [json.loads(line) for line in (FIXTURES / 'own-cancel.jsonl').read_text().splitlines()
                  if json.loads(line)['call'] in {'575195:111', '575195:114', '575195:115'}]
        for r in source:
            r['node'] = 'peer'
            if r['kind'] == 'client.command':
                r['command_hex'] = b'IHAVE <own-cancel-alice@example.invalid>'.hex()
                if r['phase'] == 'ok':
                    r['reply_hex'] = b'335 send article\r\n'.hex()
        for reply, phase in [(b'235 transferred\r\n', 'info'), (b'437 refused\r\n', 'fail'),
                             (b'436 outcome uncertain\r\n', 'info')]:
            source[-1]['reply_hex'] = reply.hex()
            result = adapt(source)
            self.assertEqual(result.unmapped, [])
            ops = pair(result.history)
            self.assertEqual(len(ops), 1)
            self.assertEqual((ops[0].f, ops[0].type, ops[0].node), ('withdraw', phase, 'peer'))
            self.assertEqual(ops[0].value['cause_call'], '575195:111')

    def test_accepted_bob_cancel_cannot_excuse_lost_alice_post(self):
        source = [json.loads(line) for line in (FIXTURES / 'ineffective-cancel.jsonl').read_text().splitlines()]
        ops = pair(adapt(source).history)
        self.assertEqual(kinds(adapt(source).history), [])
        cancel = next(o for o in ops if o.f == 'withdraw')
        self.assertEqual(cancel.type, 'fail')
        self.assertNotIn('authorized', cancel.value)
        self.assertTrue(any(o.f == 'post' and o.type == 'ok' and
                            o.value['message_id'] == '<own-cancel-bob@example.invalid>' for o in ops))
        # Remove Alice's later cancel, retain the captured crash/recovery/absence.
        after = [json.loads(line) for line in (FIXTURES / 'own-cancel.jsonl').read_text().splitlines()
                 if int(json.loads(line)['call'].split(':')[1]) >= 204]
        self.assertEqual(kinds(adapt(source + after).history), ['D1'])

    def test_missing_or_failed_authentication_never_authorizes_local_cancel(self):
        source = [json.loads(line) for line in (FIXTURES / 'own-cancel.jsonl').read_text().splitlines()]
        for conn in ('575195:17', '575195:101'):
            for failed in (False, True):
                changed = deepcopy(source)
                if failed:
                    for row in changed:
                        if row.get('conn') == conn and bytes.fromhex(row.get('reply_hex', ''))[:3] == b'281':
                            row['reply_hex'] = b'481 authentication failed\r\n'.hex()
                else:
                    changed = [r for r in changed if not (r.get('conn') == conn and
                               bytes.fromhex(r.get('command_hex', '')).startswith(b'AUTHINFO'))]
                result = adapt(changed)
                self.assertEqual(next(o.type for o in pair(result.history) if o.f == 'withdraw'), 'info')
                self.assertEqual(kinds(result.history), ['D1'])

    def test_sasl_success_requires_observed_identity_on_that_connection(self):
        source = [json.loads(line) for line in (FIXTURES / 'own-cancel.jsonl').read_text().splitlines()]
        for mechanism, identity in [('PLAIN', b'\0alice\0password'),
                                    ('SCRAM-SHA-256', b'n,,n=alice,r=nonce')]:
            for code in (281, 283):
                changed = [deepcopy(r) for r in source if r['call'] not in {'575195:20', '575195:104'}]
                for row in changed:
                    if row['call'] in {'575195:23', '575195:107'}:
                        row['command_hex'] = (b'AUTHINFO SASL ' + mechanism.encode() + b' ' +
                                              base64.b64encode(identity)).hex()
                        if row['phase'] == 'ok':
                            row['reply_hex'] = f'{code} success\r\n'.encode().hex()
                self.assertEqual(kinds(adapt(changed).history), [])
                self.assertEqual(next(o.type for o in pair(adapt(changed).history) if o.f == 'withdraw'), 'ok')
        # A successful unsupported SASL mechanism does not reveal its account.
        for row in changed:
            if row['call'] == '575195:107':
                row['command_hex'] = b'AUTHINFO SASL UNKNOWN'.hex()
        self.assertEqual(next(o.type for o in pair(adapt(changed).history) if o.f == 'withdraw'), 'info')

    def test_peer_cancel_key_hashes_encoded_key_string_and_requires_headers(self):
        # RFC 8315 section 5.1 vector, independent of the adapter implementation.
        key = b'qv1VXHYiCGjkX/N1nhfYKcAeUn8bCVhrWhoKuBSnpMA='
        lock = b's/pmK/3grrz++29ce2/mQydzJuc7iqHn1nqcJiQTPMc='
        source = [json.loads(line) for line in (FIXTURES / 'own-cancel.jsonl').read_text().splitlines()
                  if json.loads(line)['call'] in {'575195:27', '575195:30', '575195:31',
                                                 '575195:111', '575195:114', '575195:115'}]
        import re
        for r in source:
            r['node'] = 'peer'
            if r['kind'] == 'client.command':
                r['command_hex'] = b'IHAVE <fixture@example.invalid>'.hex()
                if r['phase'] == 'ok':
                    r['reply_hex'] = b'335 send article\r\n'.hex()
            elif r['kind'] == 'client.line' and r['phase'] == 'ok':
                r['reply_hex'] = b'235 transferred\r\n'.hex()
            elif 'sent_hex' in r:
                data = bytes.fromhex(r['sent_hex'])
                data = re.sub(rb'Cancel-Lock: [^\r]+', b'Cancel-Lock: sha256:' + lock, data)
                data = re.sub(rb'Cancel-Key: [^\r]+', b'Cancel-Key: sha256:' + key, data)
                r['sent_hex'] = data.hex()
        self.assertEqual(next(o.type for o in pair(adapt(source).history) if o.f == 'withdraw'), 'ok')
        for replacement, outcome in [(b'c29tZS1vdGhlci1rZXk=', 'fail'), (None, 'info'),
                                     (b'(sha256:' + key + b')', 'info')]:
            changed = deepcopy(source)
            for r in changed:
                if 'sent_hex' in r:
                    data = bytes.fromhex(r['sent_hex'])
                    field = b'' if replacement is None else (b'Cancel-Key: ' +
                            (replacement if replacement.startswith(b'(') else b'sha256:' + replacement))
                    r['sent_hex'] = re.sub(rb'Cancel-Key: [^\r]+', field, data).hex()
            self.assertEqual(next(o.type for o in pair(adapt(changed).history) if o.f == 'withdraw'), outcome)

    def test_sasl_continuation_and_connection_reset(self):
        source = [json.loads(line) for line in (FIXTURES / 'own-cancel.jsonl').read_text().splitlines()]
        for raw_transport in (False, True):
            changed = deepcopy(source)
            for row in changed:
                if row['call'] == '575195:104':
                    row['command_hex'] = b'AUTHINFO SASL PLAIN'.hex()
                    if row['phase'] == 'ok':
                        row['reply_hex'] = b'383 continue\r\n'.hex()
                if row['call'] == '575195:107':
                    row['command_hex'] = base64.b64encode(b'\0alice\0password').hex()
            if raw_transport:
                start = next(r for r in changed if r['call'] == '575195:107' and r['phase'] == 'invoke')
                end = next(r for r in changed if r['call'] == '575195:107' and r['phase'] == 'ok')
                changed = [r for r in changed if r['call'] != '575195:107']
                send = dict(start, kind='client.send', sent_hex=start['command_hex'])
                send.pop('command_hex')
                line = dict(end, kind='client.line', call='sasl-result')
                line.pop('command_hex')
                changed += [send, dict(send, phase='ok', t=send['t']+1),
                            dict(line, phase='invoke', t=line['t']-1), line]
                changed.sort(key=lambda r: r['t'])
            self.assertEqual(next(o.type for o in pair(adapt(changed).history) if o.f == 'withdraw'), 'ok')
        before = next(r for r in source if r['call'] == '575195:111')
        for kind in ('client.connect', 'client.close', 'client.starttls'):
            reset = dict(node='origin', conn=before['conn'], kind=kind, call='reset')
            changed = source + [dict(reset, t=before['t']-2, phase='invoke'),
                                dict(reset, t=before['t']-1, phase='ok')]
            changed.sort(key=lambda r: r['t'])
            self.assertEqual(next(o.type for o in pair(adapt(changed).history) if o.f == 'withdraw'), 'info')

    def test_adapter_ambiguous_calls_and_cursor_bounds(self):
        invoke = dict(t=1, test='x', kind='invoke', phase='invoke', words=['consumer', 'ack', '/ctl', '/cursor'])
        complete = invoke | {'phase': 'ok', 'stdout': 'consumer accepted'}
        result = adapt([invoke, invoke | {'t': 2}, complete | {'t': 3}, complete | {'t': 4}])
        self.assertEqual(result.history, [])
        self.assertEqual(result.counts, {'invoke:consumer': 4})
        for token in ('', '666e637501', '666e63750100', 'ff'):
            with self.assertRaises(ValueError):
                cursor(token)

    def test_adapter_late_transport_reply_remains_info(self):
        words = ['consumer', 'ack', '/ctl', '/cursor']
        c = synthetic.registration(node='N') | {'position': 0}
        source = [dict(t=1, test='x', kind='invoke', phase='invoke', node='N', words=words,
                       history_value=c),
                  dict(t=2, test='x', kind='node.stop', phase='invoke', node='N', pid=42),
                  dict(t=3, test='x', kind='node.stop', phase='fail', node='N', pid=42, exit_class='code -9'),
                  dict(t=4, test='x', kind='invoke', phase='info', node='N', words=words,
                       history_value=c, exception='lost reply')]
        result = adapt(source)
        self.assertEqual([o.type for o in pair(result.history) if o.f == 'ack'], ['info'])
        self.assertEqual(result.counts, {'invoke:consumer': 1})
        self.assertIn('late reply', result.unmapped[0]['reason'])

    def test_wait_empty_after_overlapping_ack_is_allowed(self):
        b, c = scenario()
        b.op('post', {'message_id': '<x>', 'digest': 'x', 'visible': [
            dict(consumer='c', epoch=1, scope=c['scope'], position=1)]}, response={'code': 240})
        deadline = b.time + 1000
        b.record('waiter', 'invoke', 'wait', c | {'cursor': 0, 'deadline': deadline})
        b.op('ack', c | {'position': 1})
        b.record('waiter', 'ok', 'wait', {'events': [], 'position': 1, 'more': False}, at=deadline)
        self.assertEqual(kinds(b.history), [])

    def test_adapter_incomplete_payload_and_post_reply_are_info(self):
        for verb, reply, follow in [('ARTICLE <x>', '220 1 <x> article', 'client.block'),
                                    ('POST', '340 send article', 'client.line')]:
            command = verb.encode().hex()
            source = [dict(t=1, test='x', kind='client.command', phase='invoke', command_hex=command),
                      dict(t=2, test='x', kind='client.command', phase='ok', command_hex=command,
                           reply_hex=reply.encode().hex()),
                      dict(t=3, test='x', kind=follow, phase='invoke'),
                      dict(t=4, test='x', kind=follow, phase='info', exception='EOF')]
            operation = pair(adapt(source).history)[0]
            self.assertEqual(operation.type, 'info')
            self.assertEqual(operation.completion.time, 4)

    def test_zz_catch_table(self):
        if CAUGHT:  # Standalone invocation does not pretend the properties ran.
            print('\nInjected-violation catch table (100 Hypothesis examples per kind):')
            print('kind  caught  owning checker  other checker anomalies')
            for kind in synthetic.VIOLATIONS:
                self.assertEqual(CAUGHT[kind], 100)
                print(f'{kind}    {CAUGHT[kind]}/100 {"consumer" if kind[0] == "C" else "durable":<15} 0')


def mutation_test(kind, generator):
    @settings(max_examples=100, deadline=None, database=None, derandomize=True)
    @given(SEEDS)
    def test(self, seed):
        h = generator(seed)
        own, other = (consumer, durable) if kind.startswith('C') else (durable, consumer)
        found = own.check(h)
        self.assertEqual([a.kind for a in found], [kind])
        self.assertEqual(other.check(h), [])
        self.assertTrue(found[0].ops and found[0].explanation)
        CAUGHT[kind] = CAUGHT.get(kind, 0) + 1
    return test


for _kind, _generator in synthetic.VIOLATIONS.items():
    setattr(HistoryTests, 'test_mutation_' + _kind, mutation_test(_kind, _generator))


if __name__ == '__main__':
    unittest.main()

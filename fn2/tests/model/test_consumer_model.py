"""Independent fake consumer target, per-verb fixtures, S->H linkage and controls."""
from dataclasses import replace
import unittest

from .consumer_model import ConsumerModel, Cursor, Event, Request, to_h3


class FakeTarget:
    """Small server double: no ConsumerModel/Expect calls or oracle state aliases."""
    supports_rebase = True
    history, incarnation, principal = 'history', 'incarnation', 'owner'
    reserved_epochs = frozenset()

    def __init__(self, case=None, plant=None):
        self.events = [Event(2, '<one@test>'), Event(4, '<two@test>'),
                       Event(6, '<two@test>', kind='withdrawn')]
        self.withdrawn, self.frontier = {'<two@test>'}, 8
        self.rows, self.bindings, self.waiters = {}, {}, set()
        self.next_epoch, self.plant, self.polls = 1, plant, 0

    def sync_frontier(self):
        return self.frontier

    def bind(self, name, allowed=True):
        self.bindings[name] = ('hs-secret', allowed)

    def call(self, r):
        old = self.rows.get(r.consumer)
        reply = dict(command=r.verb, outcome='accepted', reason=None)

        def refuse(reason):
            return dict(command=r.verb, outcome='refused', reason=reason)

        if r.verb in ('register', 'rebase') and r.query != 'surface.test':
            return refuse('no-such-group')
        if r.verb == 'register':
            if old and (old.query, old.query_version, old.view_version) != (r.query, r.query_version, r.view_version):
                return refuse('scope')
            if old is None:
                old = Cursor(self.history, self.incarnation, r.consumer, self.next_epoch,
                             self.principal, r.query, r.query_version, r.view_version)
                self.next_epoch += 1; self.frontier += 1
                self.rows[r.consumer] = old
            return dict(reply, cursor=old)
        if old is None:
            return refuse('unknown-consumer')
        if r.verb in ('poll', 'ack', 'wait', 'bound-poll', 'bound-ack', 'bound-wait'):
            binding = self.bindings.get(r.consumer)
            if r.verb.startswith('bound-'):
                if binding is None:
                    return refuse('unbound')
                if r.secret != binding[0]:
                    return refuse('credential')
                if not binding[1]:
                    return refuse('access')
            elif binding:
                return refuse('bound')
        if r.verb.endswith('ack'):
            same_scope = r.cursor and replace(r.cursor, position=old.position) == old
            if not same_scope or r.cursor.position > self.frontier:
                if self.plant == 'foreign-mutation':
                    self.rows[r.consumer] = replace(old, position=2)
                return refuse('scope')
            if r.cursor.position < old.position and self.plant != 'backward-ack':
                return refuse('scope')
            self.rows[r.consumer] = r.cursor
            if r.cursor != old:
                self.frontier += 1
            return dict(reply, cursor=r.cursor)
        if r.verb == 'position':
            return dict(reply, cursor=old)
        if r.verb == 'status':
            return dict(reply, committed_ack=old.position, journal_frontier=self.frontier,
                        journal_event_distance=self.frontier-old.position)
        if r.verb == 'unregister':
            del self.rows[r.consumer]; self.frontier += 1
            return reply
        if r.verb == 'rebase':
            old = replace(old, query=r.query, query_version=r.query_version,
                          view_version=r.view_version, position=0)
            self.rows[r.consumer] = old; self.frontier += 1
            return dict(reply, cursor=old)
        if r.verb.endswith('wait') and len(self.waiters) >= 12:
            return refuse('waiters')
        self.polls += 1
        end = min(self.frontier, old.position+16)
        selected = [e for e in self.events if old.position < e.position <= end and e.group == old.query]
        if self.plant == 'skip-unacked' and self.polls > 1:
            selected = selected[1:]
        if self.plant == 'redelivery' and old.position >= 2:
            selected = self.events[:1]
        event = selected[0] if selected else None
        if event:
            end = event.position
        kind = ('withdrawn' if event.message_id in self.withdrawn else event.kind) if event else 'empty'
        return dict(reply, cursor=replace(old, position=end), report=kind,
                    message_id=event.message_id if event else None,
                    report_bytes=b'FNWD\1'+event.message_id.encode() if kind == 'withdrawn' else b'',
                    more=end < self.frontier, elapsed=r.timeout if event is None else 0)


class ModelTests(unittest.TestCase):
    def setUp(self):
        self.target = FakeTarget()
        self.model = ConsumerModel(events=self.target.events, frontier=self.target.frontier)
        self.model.withdrawn = set(self.target.withdrawn)
        self.trace = []

    def call(self, verb, name='c', *, valid=True, **kwargs):
        self.model.frontier = self.target.sync_frontier()
        expected = self.model.rule(verb, name, **kwargs)
        context = self.model.consumers.get(name, Cursor('history', 'incarnation', name, 0, 'owner', 'surface.test'))
        reply = self.target.call(expected.request)
        reply['_frontier_after'] = self.target.sync_frontier()
        self.trace.append((expected.request, context, reply))
        if valid:
            self.assertIsNone(expected.check(reply), (expected.check(reply), reply))
            expected.update(reply)
        return expected, reply

    def test_register_duplicate_unregister_and_epoch_fence(self):
        _, first = self.call('register')
        _, duplicate = self.call('register')
        self.assertEqual(first['cursor'], duplicate['cursor'])
        self.call('register', query='absent')
        self.call('unregister')
        self.call('position')
        _, fresh = self.call('register')
        self.assertNotEqual(first['cursor'].epoch, fresh['cursor'].epoch)
        self.assertEqual(self.call('ack', cursor=first['cursor'])[1]['reason'], 'scope')

    def test_poll_repeat_forward_equal_backward_and_position(self):
        self.call('register')
        _, first = self.call('poll')
        _, repeat = self.call('poll')
        self.assertEqual(first['cursor'], repeat['cursor'])
        self.assertEqual(self.call('position')[1]['cursor'].position, 0)
        self.call('ack', cursor=first['cursor'])
        self.call('ack', cursor=first['cursor'])
        self.assertEqual(self.call('ack', cursor=replace(first['cursor'], position=0))[1]['reason'], 'scope')
        self.assertEqual(self.call('poll')[1]['message_id'], '<two@test>')
        self.call('status')

    def test_all_nine_cursor_fields_are_scoped(self):
        _, reply = self.call('register'); cursor = reply['cursor']
        for field in ('history', 'incarnation', 'consumer', 'epoch', 'principal', 'query', 'query_version', 'view_version'):
            value = getattr(cursor, field)
            foreign = replace(cursor, **{field: value+1 if isinstance(value, int) else 'foreign'})
            self.assertEqual(self.call('ack', cursor=foreign)[1]['reason'], 'scope')
            self.assertEqual(self.call('position')[1]['cursor'], cursor)
        self.call('ack', cursor=replace(cursor, position=self.model.frontier+1))

    def test_rebase_resets_scope_and_fences_old_token(self):
        _, registered = self.call('register')
        self.call('ack', cursor=replace(registered['cursor'], position=4))
        _, rebased = self.call('rebase', view_version=1)
        self.assertEqual(rebased['cursor'].position, 0)
        self.assertEqual(rebased['cursor'].epoch, registered['cursor'].epoch)
        self.call('ack', cursor=registered['cursor'])
        self.call('rebase', query='absent', view_version=2)
        self.assertEqual(self.call('poll')[1]['message_id'], '<one@test>')

    def test_withdrawal_replaces_content_and_reports_cause_position(self):
        self.call('register')
        for position, kind in ((2, 'article'), (4, 'withdrawn'), (6, 'withdrawn')):
            _, page = self.call('poll')
            self.assertEqual((page['cursor'].position, page['report']), (position, kind))
            if kind == 'withdrawn':
                self.assertEqual(page['report_bytes'], b'FNWD\1<two@test>')
                wrong = dict(page, report_bytes=b'article content')
                self.assertIn('withdrawal', self.model.rule('poll', 'c').check(wrong))
            self.call('ack', cursor=page['cursor'])

    def test_bound_poll_ack_wait_and_latest_authority(self):
        self.call('register')
        self.call('bound-poll', secret='hs-secret')
        self.target.bind('c'); self.model.bindings['c'] = ('hs-secret', True)
        for verb in ('poll', 'wait'):
            self.assertEqual(self.call(verb)[1]['reason'], 'bound')
        self.assertEqual(self.call('bound-poll', secret='wrong')[1]['reason'], 'credential')
        _, page = self.call('bound-wait', secret='hs-secret', timeout=10)
        self.call('bound-ack', cursor=page['cursor'], secret='wrong')
        self.call('bound-ack', cursor=page['cursor'], secret='hs-secret')
        self.target.bind('c', False); self.model.bindings['c'] = ('hs-secret', False)
        self.assertEqual(self.call('bound-wait', secret='hs-secret')[1]['reason'], 'access')
        self.call('position')

    def test_multiple_defects_have_no_invented_refusal_precedence(self):
        _, registered = self.call('register')
        self.target.bind('c'); self.model.bindings['c'] = ('hs-secret', True)
        expected, reply = self.call('bound-ack', secret='wrong',
                                   cursor=replace(registered['cursor'], history='foreign'))
        self.assertEqual(expected.reasons, {'credential', 'scope'})
        self.assertIsNone(expected.check(dict(reply, reason='credential')))
        self.assertIsNone(expected.check(dict(reply, reason='scope')))
        self.assertIsNotNone(expected.check(dict(reply, reason='access')))
        self.call('position')

    def test_wait_deadline_and_capacity(self):
        self.call('register')
        _, ready = self.call('wait', timeout=10)
        self.assertEqual(ready['elapsed'], 0)
        self.call('ack', cursor=replace(ready['cursor'], position=self.model.frontier))
        expected, empty = self.call('wait', timeout=10)
        self.assertEqual(empty['report'], 'empty')
        self.assertIn('early', expected.check(dict(empty, elapsed=9)))
        self.target.waiters = self.model.waiters = set(range(12))
        self.assertEqual(self.call('wait')[1]['reason'], 'waiters')

    def test_empty_pages_scan_at_most_sixteen_without_ack(self):
        self.target.events = []; self.model.events = []; self.target.frontier = 100
        self.call('register')
        self.assertEqual(self.call('poll')[1]['cursor'].position, 16)
        self.assertEqual(self.call('position')[1]['cursor'].position, 0)

    def test_no_hidden_write_on_equal_ack_refusal_or_read_and_page_evidence(self):
        _, registered = self.call('register')
        for verb, kwargs in [('ack', {'cursor': registered['cursor']}), ('position', {}),
                             ('poll', {}), ('bound-poll', {'secret': 'wrong'})]:
            expected, reply = self.call(verb, **kwargs)
            self.assertIn('no-mutation', expected.check(dict(reply, _frontier_after=self.model.frontier+1)))
        expected, page = self.call('poll')
        self.assertIn('more', expected.check(dict(page, more=not page['more'])))
        self.target.events = []; self.model.events = []
        expected, page = self.call('poll')
        self.assertIn('empty', expected.check(dict(page, report_bytes=b'garbage')))

    def test_two_consumers_have_independent_progress(self):
        self.call('register', 'a'); self.call('register', 'b')
        _, page = self.call('poll', 'a')
        self.call('ack', 'a', cursor=page['cursor'])
        self.assertEqual(self.call('poll', 'b')[1]['cursor'].position, 2)

    def test_determinate_rule_rejects_uncertain_and_wrong_reason(self):
        expected, reply = self.call('register')
        self.assertIsNotNone(expected.check(dict(reply, outcome='uncertain')))
        expected, reply = self.call('position', 'absent')
        self.assertIsNotNone(expected.check(dict(reply, reason='credential')))

    def test_codec_all_fields_and_invalid_encodings(self):
        cursor = Cursor('h'*64, 'i'*64, 'c'*64, 0xffffffff, 'p'*64, 'q'*64, 3, 4, 123)
        self.assertEqual(len(cursor.encode()), 346)
        self.assertEqual(Cursor.decode(cursor.encode()), cursor)
        golden = b'fncu\1\1h\1i\1c\1p\1q' + bytes.fromhex('00000003000000040000000500000006')
        self.assertEqual(Cursor.decode(golden), Cursor('h', 'i', 'c', 5, 'p', 'q', 3, 4, 6))
        for raw in (b'', cursor.encode()+b'x', cursor.encode()[:-1], b'fncu\2'+cursor.encode()[5:]):
            with self.assertRaises(ValueError):
                Cursor.decode(raw)

    def test_h3_morphism_preserves_ack_request_and_uncertainty(self):
        _, registered = self.call('register'); cursor = registered['cursor']
        rows = to_h3([(Request('ack', 'c', cursor=cursor), cursor,
                       dict(command='ack', outcome='accepted', reason=None, cursor=replace(cursor, position=7)))])
        self.assertEqual(rows[1]['value']['position'], 0)
        rows = to_h3([(Request('ack', 'c', cursor=cursor), cursor,
                      dict(command='ack', outcome='uncertain', reason='lost-reply'))])
        self.assertEqual([r['type'] for r in rows], ['invoke', 'info'])

    def test_public_cli_adapter_argv_json_cursor_and_report_observations(self):
        import json
        from pathlib import Path
        import tempfile
        from types import SimpleNamespace
        from fn2.tests.surface.consumer.test_model_consumer import ConsumerTarget
        fake, calls = FakeTarget(), []

        class PublicNode:
            control = '/scratch/control.sock'

            def invoke(node, *words, timeout):
                calls.append(words)
                self.assertEqual(words[:2], ('consumer', '--json'))
                verb, control, *args = words[2:]
                self.assertEqual(control, node.control)
                cursor_path = report_path = None
                kwargs = {}
                if verb.endswith('ack'):
                    token = Cursor.decode(args[0].read_bytes())
                    name, kwargs['cursor'] = token.consumer, token
                    if verb == 'bound-ack':
                        kwargs['secret'] = args[1].read_text().rstrip('\n')
                else:
                    name = args.pop(0)
                    if verb == 'register':
                        kwargs['query'], cursor_path = args
                    elif verb == 'position':
                        cursor_path = args[0]
                    elif verb in ('poll', 'wait', 'bound-poll', 'bound-wait'):
                        if verb.startswith('bound-'):
                            kwargs['secret'] = args.pop(0).read_text().rstrip('\n')
                        cursor_path, report_path, *tail = args
                        if verb.endswith('wait'):
                            self.assertEqual(tail[0], '--timeout')
                            kwargs['timeout'] = int(tail[1])
                reply = fake.call(Request(verb, name, **kwargs))
                if reply['outcome'] == 'accepted':
                    if cursor_path:
                        cursor_path.write_bytes(reply['cursor'].encode())
                    if report_path:
                        report_path.write_bytes(reply['report_bytes'])
                wire = {k: v for k, v in reply.items() if k not in ('cursor', 'report_bytes', 'more', 'elapsed')}
                return SimpleNamespace(returncode=0 if reply['outcome'] == 'accepted' else 1,
                                       stdout=json.dumps(wire).encode(), stderr=b'')

        with tempfile.TemporaryDirectory() as root:
            target = ConsumerTarget.__new__(ConsumerTarget)
            target.node, target.case, target.serial = PublicNode(), self, 0
            target.node.root, target.frontier = Path(root), fake.frontier
            token = target.call(Request('register', 'c'))['cursor']
            self.assertEqual(token.consumer, 'c')
            for verb in ('position', 'status', 'poll', 'wait', 'bound-poll', 'bound-wait'):
                reply = target.call(Request(verb, 'c', timeout=0))
                self.assertEqual(reply['outcome'], 'refused' if verb.startswith('bound-') else 'accepted')
            target.call(Request('ack', 'c', cursor=replace(token, position=2)))
            fake.bind('c')
            page = target.call(Request('bound-wait', 'c', secret='hs-secret'))
            self.assertEqual(page['report_bytes'], b'FNWD\1<two@test>')
            target.call(Request('bound-ack', 'c', cursor=page['cursor'], secret='hs-secret'))
            target.call(Request('unregister', 'c'))
            with self.assertRaises(NotImplementedError):
                target.call(Request('rebase', 'c'))
        self.assertEqual({words[2] for words in calls}, set(ConsumerModel.VERBS) - {'rebase'})

    def test_fake_target_state_machine_and_every_trace_h3(self):
        from hypothesis import settings
        from hypothesis.stateful import run_state_machine_as_test
        from fn2.tests.surface.consumer.test_model_consumer import machine
        from fn2.tests.history.consumer import check
        traces = []
        run_state_machine_as_test(machine(self, FakeTarget, traces), settings=settings(
            max_examples=200, stateful_step_count=50, deadline=None, database=None, derandomize=True))
        self.assertGreaterEqual(len(traces), 200)
        for trace in traces:
            self.assertEqual(check(to_h3(trace)), [], trace)


class MutationControls(unittest.TestCase):
    setUp = ModelTests.setUp
    call = ModelTests.call

    def test_mutation_catch_table(self):
        from fn2.tests.history.consumer import check
        table = {'backward-ack': ('refusal', 'C1'), 'skip-unacked': ('poll', 'C2'),
                 'foreign-mutation': ('position', 'C1'), 'redelivery': ('poll', 'C3')}
        for plant, (predicate, anomaly) in table.items():
            with self.subTest(plant=plant):
                self.setUp(); self.target.plant = plant
                _, registered = self.call('register'); zero = registered['cursor']
                _, first = self.call('poll')
                if plant in ('backward-ack', 'redelivery'):
                    self.call('ack', cursor=first['cursor'])
                if plant == 'backward-ack':
                    expected, bad = self.call('ack', cursor=zero, valid=False)
                elif plant == 'foreign-mutation':
                    self.call('position')
                    self.call('ack', cursor=replace(zero, history='foreign', position=2))
                    expected, bad = self.call('position', valid=False)
                else:
                    expected, bad = self.call('poll', valid=False)
                self.assertTrue(expected.check(bad).startswith(predicate + ':'), expected.check(bad))
                kinds = {a.kind for a in check(to_h3(self.trace))}
                self.assertIn(anomaly, kinds)
                print(f'{plant} -> {predicate} predicate; H3 {anomaly}')


if __name__ == '__main__':
    unittest.main()

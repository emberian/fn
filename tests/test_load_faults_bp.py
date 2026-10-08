"""Pure F8 tests: fake node observations; no image, ACL2, or box process."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch

from tools.load import faults, faults_bp as bp


def post(h, mid, value, outcome='completed'):
    op = h.plan('POST', {'msgid': mid, 'sha256': value})
    if outcome != 'not-attempted':
        h.sent(op)
    if outcome == 'completed':
        h.complete(op, b'240 accepted\r\n')
    return op


def observation(articles, **kwargs):
    return dict(articles=dict(articles), article_count=len(articles), complete=True, **kwargs)


class GeneratorTests(unittest.TestCase):
    def test_seeded_and_full_fault_recipe(self):
        self.assertEqual(bp.generate(42), bp.generate(42))
        self.assertNotEqual(bp.generate(42), bp.generate(43))
        for seed in range(20):
            recipe = bp.generate(seed)
            self.assertEqual([r['step'] for r in recipe], list(range(len(recipe))))
            self.assertEqual({r['mode'] for r in recipe if r['action'] == 'transfer'},
                             {'drop', 'kind7', 'decision', 'clean'})
            self.assertTrue({'duplicate', 'restart', 'boot', 'stale'} <= {r['action'] for r in recipe})
            produced = set()
            for row in recipe:
                if row['action'] == 'post':
                    produced.add(row['i'])
                elif row['action'] in ('transfer', 'duplicate', 'stale'):
                    self.assertIn(row['i'], produced)
            self.assertEqual(recipe[-1]['mode'], 'clean')


class OracleTests(unittest.TestCase):
    def setUp(self):
        self.h = faults.History()
        post(self.h, '<one>', 'digest-one')
        post(self.h, '<maybe>', 'digest-maybe', 'attempted-uncertain')
        post(self.h, '<never>', 'digest-never', 'not-attempted')
        self.present = {'<one>': 'digest-one'}

    def findings(self, a, b):
        return bp.check(self.h.ops, {'A': a, 'B': b})

    def test_clean_uncertain_whole_or_absent(self):
        for extra in ({}, {'<maybe>': 'digest-maybe'}):
            obs = observation(dict(self.present, **extra))
            self.assertEqual(self.findings(obs, obs), [])

    def test_lost_completed_article_has_teeth_even_if_both_lose_it(self):
        found = self.findings(observation({}), observation({}))
        self.assertIn(('P1-DURABLE', 'A: missing or changed: <one>'), found)
        self.assertIn(('P1-DURABLE', 'B: missing or changed: <one>'), found)

    def test_duplicate_has_teeth_even_when_map_is_identical(self):
        good = observation(self.present)
        duplicate = dict(good, article_count=2)
        self.assertIn(('P2-IDENTITY', 'B: duplicate or unenumerated article'),
                      self.findings(good, duplicate))
        duplicate = dict(good, duplicates=['<one>'])
        self.assertIn(('P2-IDENTITY', 'B: duplicate or unenumerated article'),
                      self.findings(good, duplicate))

    def test_divergent_uncertain_article_has_teeth(self):
        a = observation(dict(self.present, **{'<maybe>': 'digest-maybe'}))
        self.assertIn(('P2-IDENTITY', 'divergence is nonzero'),
                      self.findings(a, observation(self.present)))

    def test_changed_uncertain_article_is_a_third_state(self):
        obs = observation(dict(self.present, **{'<maybe>': 'half-body'}))
        self.assertTrue(any(p == 'P2-IDENTITY' for p, _ in self.findings(obs, obs)))

    def test_unattempted_article_is_not_allowed(self):
        obs = observation(dict(self.present, **{'<never>': 'digest-never'}))
        self.assertTrue(any(p == 'P2-IDENTITY' for p, _ in self.findings(obs, obs)))

    def test_missing_inventory_or_count_is_never_clean(self):
        for bad in ({}, {'complete': False}, {'complete': True, 'articles': self.present},
                    {'complete': True, 'article_count': 0}):
            self.assertIn(('P5-RECOVERY', 'B: complete inventory missing'),
                          self.findings(observation(self.present), bad))

    def test_refused_post_is_not_accepted(self):
        self.h.complete(self.h.ops[0], b'441 refused\r\n')
        self.assertEqual(self.findings(observation({}), observation({})), [])


class FakeCampaign(bp.BpCampaign):
    """One fresh fake pair per trial; only a retained transfer triggers loss."""
    def __init__(self, missing=False):
        super().__init__(SimpleNamespace(cell_id='F8', label='unit'), {}, '/fake/dtn', '/fake/developer')
        self.calls, self.stores = [], []
        self.missing = missing

    def trial(self, recipe):
        self.calls.append(copy.deepcopy(recipe))
        stores = {'A': {}, 'B': {}}
        self.stores.append(stores)
        h = self.history()
        for row in recipe:
            op = h.plan('F8', row)
            op['replayable'] = True
            h.sent(op)
            h.complete(op, b'observed\r\n')
        post(h, '<one>', 'digest-one')
        bad = any(row['action'] == 'transfer' for row in recipe)
        fs = [('P1-DURABLE', 'B: missing or changed: <one>')] if bad else []
        obs = {n: observation({}) for n in stores}
        if self.missing:
            obs.pop('B')
        h.trial_notes = {'observations': obs, 'witnessed': sorted(bp.FAULTS), 'nodes': {}}
        return h, fs, h.trial_notes


class ReplayTests(unittest.TestCase):
    def setUp(self):
        tmp = self.enterContext(tempfile.TemporaryDirectory())
        self.enterContext(patch.dict('os.environ', FN_LOAD_TRACE_DIR=tmp))

    def test_real_campaign_constructs_and_closes_a_fresh_pair_per_trial(self):
        pairs = []
        class FakePair:
            def __init__(self, campaign, history):
                self.closed = False
                pairs.append(self)
            def execute(self, step, witnessed):
                pass
            def converge(self, witnessed):
                pass
            def observe(self):
                return {n: observation({}) for n in ('A', 'B')}
            def close(self):
                self.closed = True
        campaign = object.__new__(bp.BpCampaign)
        with patch.object(bp, 'Pair', FakePair):
            for _ in range(2):
                _, findings, _ = campaign.trial([])
                self.assertEqual(findings, [])
        self.assertEqual(len(pairs), 2)
        self.assertIsNot(pairs[0], pairs[1])
        self.assertTrue(all(p.closed for p in pairs))

    def test_fixed_drain_offers_deleted_transfers_without_reoffering_completed_ones(self):
        pair = object.__new__(bp.Pair)
        pair.requests = {0: b'first', 1: b'second', 2: b'third'}
        pair.offered = {1}
        calls = []
        pair.transfer = lambda i, mode, witnessed: calls.append((i, mode))
        pair.converge(set())
        self.assertEqual(calls, [(0, 'clean'), (2, 'clean')])

    def test_shared_report_uses_shared_shrinker_and_fresh_trials(self):
        campaign = FakeCampaign()
        with patch.object(faults, 'shrink', wraps=faults.shrink) as shrink:
            out = bp.run_campaign(campaign, seed=13, budget=8)
        shrink.assert_called_once()
        finding = out['faults']['violations'][0]
        self.assertGreater(finding['shrink']['runs'], 0)
        self.assertLessEqual(finding['shrink']['runs'], 8)
        self.assertEqual(finding['shrink']['budget'], 8)
        self.assertLess(len(finding['shrunk_history']), len(campaign.calls[0]))
        self.assertEqual(len({id(s) for s in campaign.stores}), len(campaign.calls))
        self.assertTrue(any(op['args']['action'] == 'transfer' for op in finding['shrunk_history']))
        self.assertTrue(out['faults']['histories'])
        self.assertEqual(out['status'], 'failed')
        self.assertTrue(out['faults']['traces'])
        for path in out['faults']['traces']:
            trace = json.loads(Path(path).read_text())
            self.assertEqual(trace['schema'], 1)
            self.assertEqual(trace['cell'], 'F8')
            self.assertIn('tcpcl-octets', trace['extensions'])
            self.assertIn('steps', trace)
        self.assertIn('trace', finding)

    def test_missing_required_observation_with_all_faults_is_not_measured(self):
        out = bp.run_campaign(FakeCampaign(missing=True), budget=0)
        self.assertEqual(out['faults']['checked'], [])
        self.assertEqual(out['status'], 'not-measured')

    def test_every_record_has_contract_fields(self):
        out = bp.run_campaign(FakeCampaign(), budget=0)
        for op in out['faults']['histories'][0]:
            self.assertIn(op['outcome'], faults.OUTCOMES)
            self.assertEqual(len(op['args_digest']), 64)
            self.assertIsInstance(op['op_id'], int)
            self.assertIsNotNone(op['send_time'])
            self.assertTrue(op['reply_line'].endswith('\r\n'))

    def test_failure_records_step_traceback_and_all_node_stderr_paths(self):
        class FailingPair:
            def __init__(self, campaign, history):
                history.trial_notes['nodes'] = {
                    'A': {'stderr': ['/private/work/A/owner.1.err', '/private/work/A/bp-2.stderr']},
                    'B': {'stderr': ['/private/work/B/bp-3.stderr']}}
            def execute(self, step, witnessed):
                if step['action'] == 'duplicate':
                    raise ValueError('transfer rejected 060201')
            def close(self):
                pass
        campaign = object.__new__(bp.BpCampaign)
        recipe = [{'step': 0, 'action': 'transfer'}, {'step': 1, 'action': 'duplicate'},
                  {'step': 2, 'action': 'stale'}]
        with patch.object(bp, 'Pair', FailingPair):
            h, findings, notes = campaign.trial(recipe)
        self.assertTrue(findings)
        self.assertEqual(notes['failing_step'], {'phase': 'recipe', **recipe[1]})
        self.assertEqual(notes['exception']['type'], 'ValueError')
        self.assertIn('transfer rejected 060201', '\n'.join(notes['exception']['traceback_tail']))
        self.assertTrue(any('in execute' in line for line in notes['exception']['traceback_tail']))
        self.assertEqual([s['outcome'] for s in notes['steps']],
                         ['completed', 'attempted-uncertain', 'not-attempted'])
        self.assertEqual(len(notes['nodes']['A']['stderr']), 2)
        snap = campaign.snapshot(h)
        self.assertFalse(snap['sequential'])
        self.assertEqual(snap['trial']['nodes'], notes['nodes'])

    def test_setup_exception_keeps_diagnostics_before_pair_assignment(self):
        class BrokenPair:
            def __init__(self, campaign, history):
                history.trial_notes['nodes']['A'] = {'stderr': ['/work/A/bp-1.stderr']}
                raise RuntimeError('no BP NODE LISTENING')
        campaign = object.__new__(bp.BpCampaign)
        with patch.object(bp, 'Pair', BrokenPair):
            _, _, notes = campaign.trial([])
        self.assertEqual(notes['failing_step'], {'phase': 'setup'})
        self.assertEqual(notes['exception']['type'], 'RuntimeError')
        self.assertIn('A', notes['nodes'])

    def test_completed_enqueue_refusal_does_not_abort_remaining_recipe_or_inventory(self):
        calls = []
        refusal = {'rc': 1, 'reply_line': bp.ENQUEUE_PREFLIGHT_REFUSAL.decode() + '\r\n',
                   'decision': 'fn-workflow-preflight-record', 'txid': 2,
                   'generation': bp.ENQUEUE_GENERATION, 'article': 1}
        class RefusingPair:
            def __init__(self, campaign, history):
                pass
            def execute(self, step, witnessed):
                calls.append(step['step'])
                if step['step'] == 0:
                    return refusal
                witnessed.update(bp.FAULTS)
            def converge(self, witnessed):
                calls.append('converge')
            def observe(self):
                calls.append('inventory')
                return {n: observation({}) for n in ('A', 'B')}
            def close(self):
                calls.append('close')
        campaign = object.__new__(bp.BpCampaign)
        recipe = [{'step': 0, 'action': 'post', 'i': 1}, {'step': 1, 'action': 'post', 'i': 2}]
        with patch.object(bp, 'Pair', RefusingPair):
            h, findings, notes = campaign.trial(recipe)
        self.assertEqual(calls, [0, 1, 'converge', 'inventory', 'close'])
        self.assertIsNone(notes['exception'])
        self.assertIsNone(notes['failing_step'])
        self.assertEqual(h.ops[0]['outcome'], 'completed')
        self.assertEqual(h.ops[0]['reply_line'], refusal['reply_line'])
        self.assertEqual(h.ops[0]['rc'], 1)
        self.assertEqual([s['outcome'] for s in notes['steps']], ['completed', 'completed'])
        self.assertEqual(len(notes['refusals']), 1)
        self.assertTrue(any(p == 'P5-RECOVERY' and 'fn-workflow-preflight-record' in d for p, d in findings))


class EnqueueTests(unittest.TestCase):
    def setUp(self):
        root = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.pair = object.__new__(bp.Pair)
        self.pair.sequence = 0
        self.pair.h = faults.History()
        self.pair.notes = {'commands': []}
        self.pair.c = SimpleNamespace(image='/not-launched', recovery=1, serial=1,
                                      run=SimpleNamespace(node=SimpleNamespace(work=root)))
        self.pair.nodes = {'A': SimpleNamespace(store=root / 'store', work=root, port=1)}
        self.enterContext(patch('tests.native_harness.environment', return_value={}))

    def test_receipt_then_restart_does_not_reuse_receipt_transaction_key(self):
        # External fake journal models the documented used-PAIR precondition.
        # Control: generation 0 reproduces run3's second-enqueue refusal.
        for generation, refused in ((0, True), (bp.ENQUEUE_GENERATION, False)):
            with self.subTest(generation=generation):
                self.pair.sequence = 0
                durable = set()
                def command(argv, **kwargs):
                    self.assertEqual(argv[2:4], ['app-journal', 'workflow-enqueue'])
                    key = (int(argv[6]), int(argv[7]))
                    if key in durable:
                        return SimpleNamespace(returncode=1, stdout=b'', stderr=bp.ENQUEUE_PREFLIGHT_REFUSAL)
                    durable.add(key)
                    return SimpleNamespace(returncode=0, stdout=b'workflow durable\n', stderr=b'')
                with patch.object(bp, 'ENQUEUE_GENERATION', generation), \
                        patch('tests.native_harness.run', side_effect=command):
                    self.assertIsNone(self.pair.enqueue(0, '<first>'))
                    # fn-bprl-receipt-auto-record's first receipt uses (2, 0).
                    # Reopening preserves this used key; it cannot be reused.
                    durable.add((2, 0))
                    result = self.pair.enqueue(1, '<second>')
                self.assertEqual(result is not None, refused)
                if not refused:
                    self.assertIn((2, bp.ENQUEUE_GENERATION), durable)

    def test_preflight_refusal_is_completed_with_reply_and_exit(self):
        result = SimpleNamespace(returncode=1, stdout=b'', stderr=bp.ENQUEUE_PREFLIGHT_REFUSAL)
        with patch('tests.native_harness.run', return_value=result):
            refusal = self.pair.enqueue(0, '<refused>')
        self.assertEqual(refusal['decision'], 'fn-workflow-preflight-record')
        op = self.pair.h.ops[-1]
        self.assertEqual(op['outcome'], 'completed')
        self.assertEqual(op['rc'], 1)
        self.assertIn(bp.ENQUEUE_PREFLIGHT_REFUSAL.decode(), op['reply_line'])
        self.assertIsNotNone(op['send_time'])

    def test_other_errors_and_ambiguous_publication_still_stop(self):
        from tests.native_harness import EXIT
        for rc, message in ((EXIT.REFUSED, b'application journal publication refused'),
                            (EXIT.UNCERTAIN, bp.ENQUEUE_PREFLIGHT_REFUSAL)):
            with self.subTest(rc=rc), patch('tests.native_harness.run', return_value=SimpleNamespace(
                    returncode=rc, stdout=b'', stderr=message)):
                with self.assertRaisesRegex(RuntimeError, 'workflow-enqueue exit'):
                    self.pair.enqueue(0, '<error>')

    def test_refused_enqueue_restarts_sender_without_authoring_a_request(self):
        pair = self.pair
        pair.posted, pair.requests = {}, {}
        refusal = {'rc': 1, 'reply_line': 'refused\r\n'}
        pair.stop_bp = Mock()
        pair.start_reader = Mock()
        pair.stop_reader = Mock()
        pair.enqueue = Mock(return_value=refusal)
        pair.start_bp = Mock(return_value=(None, 1234))
        pair.relay = Mock()
        pair.author_request = Mock()
        pair.invoke = Mock(return_value=SimpleNamespace(stdout=b'stored article'))
        class Client:
            def __init__(self, *args):
                pass
            def __enter__(self):
                return self
            def __exit__(self, *args):
                pass
            def post(self, i, octets, op):
                pair.h.sent(op)
                pair.h.complete(op, b'240 accepted\r\n')
                return b'240 accepted\r\n'
        pair.c.deadline = 1
        with patch.object(bp, 'Client', Client):
            self.assertEqual(pair.execute({'action': 'post', 'i': 1, 'octets': 512}, set()), refusal)
        pair.start_bp.assert_called_once_with('A')
        pair.relay.route.assert_called_once_with(1234)
        pair.author_request.assert_not_called()
        self.assertEqual(pair.requests, {})
        self.assertEqual(pair.invoke.call_args.args[0], 'store')
        self.assertEqual(pair.invoke.call_count, 1)
        accepted = pair.h.ops[0]['args']
        findings = bp.check(pair.h.ops, {'A': observation({accepted['msgid']: accepted['sha256']}),
                                        'B': observation({})})
        self.assertTrue(any(p == 'P1-DURABLE' for p, _ in findings))


class WireTests(unittest.TestCase):
    def peer(self, frames):
        peer = object.__new__(bp.WirePeer)
        peer.segment_mru, peer.transfer_mru = 65536, 1048576
        peer.recorder = None
        class Sock:
            def sendall(self, wire):
                self.wire = wire
        peer.sock = Sock()
        replies = iter(frames)
        peer.frame = lambda: next(replies)
        return peer

    def test_exact_ack_is_captured_and_replayed_verbatim(self):
        ack = b'\x02\x03' + (0).to_bytes(8, 'big') + (3).to_bytes(8, 'big')
        peer = self.peer([b'\x04', ack, b'\x06\x01\x02'])
        self.assertEqual(peer.transfer(b'abc'), ack)
        self.assertEqual(peer.replay(ack), b'\x06\x01\x02')
        self.assertEqual(peer.sock.wire, ack)

    def test_partial_ack_cannot_complete_a_transfer(self):
        peer = self.peer([b'\x02\x02' + (0).to_bytes(8, 'big') + (2).to_bytes(8, 'big')])
        with self.assertRaises(ValueError):
            peer.transfer(b'abc')

    def test_handshake_and_segment_frames_match_raw_peer_with_negotiated_mru(self):
        from tests.test_bp_node_native import RawTcpclPeer
        for length in (512, 1024, 1025, 2500):
            with self.subTest(length=length):
                bundle = bytes(i % 256 for i in range(length))
                node = b'dtn://receiver/'
                # Include session extensions and fragment all socket reads:
                # first XFER_SEGMENT may only follow the COMPLETE SESS_INIT.
                extensions = b'\x00\x00\x99\x00\x01x'
                init = (b'\x07\x00\x01' + (1024).to_bytes(8, 'big')
                        + (1048576).to_bytes(8, 'big') + len(node).to_bytes(2, 'big')
                        + node + len(extensions).to_bytes(4, 'big') + extensions)
                acks = []
                for offset in range(0, length, 1024):
                    end = min(offset + 1024, length)
                    flags = (2 if not offset else 0) | (1 if end == length else 0)
                    acks.append(b'\x02' + bytes([flags]) + bytes(8) + end.to_bytes(8, 'big'))
                class Socket:
                    def __init__(self):
                        self.incoming = b'dtn!\x04\x00' + init + b''.join(acks)
                        self.at, self.sent = 0, []
                    def settimeout(self, _):
                        pass
                    def sendall(self, data):
                        if data[0] == 1:
                            self_test.assertGreaterEqual(self.at, 6 + len(init))
                        self.sent.append(data)
                    def recv(self, n):
                        data = self.incoming[self.at:self.at + min(n, 3)]
                        self.at += len(data)
                        return data
                    def close(self):
                        pass
                self_test = self
                actual = Socket()
                rec = faults.TraceRecorder()
                with patch.object(bp.socket, 'create_connection', return_value=actual):
                    peer = bp.WirePeer(1, 10, recorder=rec, node='B')
                    ack = peer.transfer(bundle)
                    peer.abort()
                reference = Socket()
                with patch.object(bp.socket, 'create_connection', return_value=reference), \
                        patch('tests.test_bp_node_native.threading.Thread'):
                    raw = RawTcpclPeer(1)
                # Raw's reader thread was suppressed; the reference sender
                # is now established for the purpose of comparing wire bytes.
                reference.at = 6 + len(init)
                for offset in range(0, length, 1024):
                    raw.segment(0, bundle[offset:offset + 1024], start=offset == 0,
                                end=offset + 1024 >= length)
                raw.close()
                self.assertEqual(actual.sent, reference.sent)
                self.assertEqual(ack, acks[-1])
                sends = [bytes.fromhex(s['hex']) for s in rec.steps if s['t'] == 'send']
                self.assertEqual(sends, actual.sent)
                self.assertTrue(any(s.get('until') == 'octets' for s in rec.steps))
                self.assertEqual(rec.steps[-1]['t'], 'close')

    def test_wrong_cumulative_ack_never_completes_segmented_duplicate(self):
        peer = self.peer([b'\x02\x02' + bytes(8) + (2).to_bytes(8, 'big'),
                          b'\x02\x01' + bytes(8) + (1).to_bytes(8, 'big')])
        peer.segment_mru = 2
        with self.assertRaisesRegex(ValueError, '3/3'):
            peer.transfer(b'abc')


if __name__ == '__main__':
    unittest.main()

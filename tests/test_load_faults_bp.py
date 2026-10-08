"""Pure F8 tests: fake node observations; no image, ACL2, or box process."""
import copy
import unittest
from unittest.mock import patch

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


class FakeCampaign:
    """One fresh fake pair per trial; only a retained transfer triggers loss."""
    def __init__(self, missing=False):
        self.calls, self.stores = [], []
        self.missing = missing

    def trial(self, recipe):
        self.calls.append(copy.deepcopy(recipe))
        stores = {'A': {}, 'B': {}}
        self.stores.append(stores)
        h = faults.History()
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
        return h, fs, {'observations': obs, 'witnessed': sorted(bp.FAULTS)}


class ReplayTests(unittest.TestCase):
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


class WireTests(unittest.TestCase):
    def peer(self, frames):
        peer = object.__new__(bp.WirePeer)
        class Sock:
            def sendall(self, wire):
                self.wire = wire
        peer.sock = Sock()
        replies = iter(frames)
        peer.frame = lambda: next(replies)
        return peer

    def test_exact_ack_is_captured_and_replayed_verbatim(self):
        ack = b'\x02\x03' + (1).to_bytes(8, 'big') + (3).to_bytes(8, 'big')
        peer = self.peer([b'\x04', ack, b'\x06\x01\x02'])
        self.assertEqual(peer.transfer(b'abc'), ack)
        self.assertEqual(peer.replay(ack), b'\x06\x01\x02')
        self.assertEqual(peer.sock.wire, ack)

    def test_partial_ack_cannot_complete_a_transfer(self):
        peer = self.peer([b'\x02\x02' + (1).to_bytes(8, 'big') + (2).to_bytes(8, 'big')])
        with self.assertRaises(ValueError):
            peer.transfer(b'abc')


if __name__ == '__main__':
    unittest.main()

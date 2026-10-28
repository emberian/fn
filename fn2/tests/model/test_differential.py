"""No node/image required: wire controls, planted failures and corpus inventory."""
import json
import os
from pathlib import Path
import socket
import tempfile
import unittest
from unittest.mock import patch

from . import differential as d
from .nntp_model import Expect

ARTIFACTS = Path(os.environ.get('H2B_ARTIFACTS', f'/tmp/h2b-tests-{os.getpid()}'))


def setUpModule():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    (ARTIFACTS / 'run.pid').write_text(str(os.getpid()) + '\n')


class DifferentialTests(unittest.TestCase):
    def test_200_seeds_each_mode_every_cut(self):
        summary = dict(seeds_run=200, sessions=0, commands_compared=0, matches=0,
                       mismatches={}, steps=20, modes=['reader', 'node', 'peer'])
        for seed in range(200):
            for mode in summary['modes']:
                items = d.fz.Gen(seed, mode, d.fz.PRESENT_IDS).transcript(20)
                for cut in d.CUTS:
                    with self.subTest(seed=seed, mode=mode, cut=cut):
                        r = d.compare(items, seed=seed, mode=mode, cut=cut,
                                      transport=('plain', 'starttls', 'implicit')[seed % 3])
                        summary['sessions'] += 1
                        summary['commands_compared'] += r.compared
                        summary['matches'] += r.matches
                        self.assertEqual(r.rows, [])
        (ARTIFACTS / 'fake-summary.json').write_text(json.dumps(summary, indent=2) + '\n')

    def test_each_mutation_caught_and_minimized(self):
        expected = {'reuse-number': 'GROUP', '423-for-420': 'XOVER',
                    'frame-after-quit': 'closed', 'wrong-over-field': 'XOVER',
                    'dot-unstuffed': 'BODY'}
        table = {}
        for plant in d.PLANTS:
            for seed in range(200):
                items = d.fz.Gen(seed, 'reader', d.fz.PRESENT_IDS).transcript(20)
                run = lambda xs: d.compare(xs, seed=seed, plants=(plant,))
                result = run(items)
                if not result.rows:
                    continue
                row = result.rows[0]
                self.assertEqual(row['rule'], expected[plant], row)
                self.assertEqual(row['class'], 'unclassified')
                self.assertEqual(d.compare(items).rows, [], 'unmutated control')
                small = d.minimize(items, row, run, seconds=10)
                self.assertLessEqual(len(small), 3)
                reduced = run(small)
                self.assertEqual(reduced.rows[0]['rule'], row['rule'])
                # Units are commands, including one complete article block.
                self.assertLessEqual(len(reduced.commands), 3)
                for cut in d.CUTS:
                    self.assertEqual(d.compare(small, cut=cut).rows, [])
                    self.assertEqual(d.compare(small, cut=cut, plants=(plant,)).rows[0]['rule'], row['rule'])
                table[plant] = dict(seed=seed, rule=row['rule'], commands=len(small),
                                    row=row, minimized_hex=[x.hex() for x in small])
                break
            self.assertIn(plant, table, 'not caught within 200 seeds')
        (ARTIFACTS / 'mutation-controls.json').write_text(json.dumps(table, indent=2) + '\n')

    def test_committed_reproducer_inventory(self):
        paths = sorted((d.ROOT / 'tests/fixtures/fuzz-nntp').glob('*.json'))
        self.assertEqual(len(paths), 11, 'current tree has eleven files, not nine')
        results = [d.replay_fixture(path) for path in paths]
        self.assertEqual([r['verdict'] for r in results].count('match'), 4)
        self.assertEqual([r['verdict'] for r in results].count('unsupported-store'), 5)
        self.assertEqual([r['verdict'] for r in results].count('unsupported-bounds'), 2)
        self.assertFalse(any(r['verdict'] == 'mismatch' for r in results))
        for cut in d.CUTS:
            for path in paths:
                self.assertNotEqual(d.replay_fixture(path, cut=cut)['verdict'], 'mismatch')
        (ARTIFACTS / 'corpus-verdicts.json').write_text(json.dumps(results, indent=2) + '\n')

    def test_pipeline_boundary_and_transports(self):
        commands = [b'CAPABILITIES\r\nGROUP fn.test\r\n', b'STARTTLS\r\n',
                    b'STAT\r\nAUTHINFO USER fuzz\r\nAUTHINFO PASS fuzz-password\r\n',
                    b'COMPRESS DEFLATE\r\n', b'CAPABILITIES\r\nGROUP fn.test\r\nOVER 2\r\n',
                    b'BODY 2\r\nQUIT\r\nHELP\r\n']
        for transport in ('plain', 'starttls', 'implicit'):
            for cut in d.CUTS:
                self.assertEqual(d.compare(commands, transport=transport, cut=cut).rows, [])

    def test_cuts_preserve_items_and_bytes(self):
        items = [b'HE', b'LP\r\nGROUP fn.test\r\n', b'QUIT\r\n']
        for cut in d.CUTS:
            self.assertEqual(b''.join(d.pieces(items, 1, 15, cut)), b''.join(items)[1:15])
        self.assertEqual(d.pieces(items, 1, 15, 'per-item'), [b'E', items[1][:13]])
        self.assertEqual(d.compare(items).rows, [])

    def test_missing_terminator_and_third_auth_failure(self):
        for transcript in ([b'POST\r\nFrom: a@b\r\n\r\nincomplete'],
                           [b'AUTHINFO USER fuzz\r\nAUTHINFO PASS bad\r\n'] * 3,
                           [b'CAPABILITIES\r\nHELP'], [b'\r']):
            for cut in d.CUTS:
                self.assertEqual(d.compare(transcript, cut=cut).rows, [])

    def test_node_profile_is_empty_and_source_address_decides_peer(self):
        model = d.fixture(False)
        self.assertEqual(model.articles, {})
        self.assertEqual(set(model.groups), {'fn.test', 'fn.letters'})
        self.assertFalse(d.connection(model, 'reader', 'plain').peer)
        self.assertTrue(d.connection(model, 'peer', 'plain').peer)
        self.assertEqual(model.accounts['fuzz']['password'], 'fuzz-password')

    def test_fake_wire_faults_are_not_silently_accepted(self):
        original = d.Fake.recv
        def no_greeting(server, n):
            server.output.clear()
            server.closed = True
            return original(server, n)
        with patch.object(d.Fake, 'recv', no_greeting):
            r = d.compare([b'QUIT\r\n'])
        self.assertEqual(r.rows[0]['rule'], 'greeting')
        def timeout_at_eof(server, n):
            if server.closed:
                raise socket.timeout('planted EOF hang')
            return original(server, n)
        with patch.object(d.Fake, 'recv', timeout_at_eof):
            r = d.compare([b'HELP\r\n'])
        self.assertEqual(r.rows[0]['rule'], 'liveness')
        self.assertIn('EOF', r.rows[0]['detail'])

    def test_cli_reproducer_compatible_hex_schema(self):
        with tempfile.TemporaryDirectory(prefix='h2b-cli-') as out:
            rc = d.main(['--target', 'fake', '--seeds', '4..4', '--steps', '20',
                         '--mode', 'reader', '--cuts', 'whole', '--plant', 'reuse-number',
                         '--out', out])
            self.assertEqual(rc, 1)
            path = next(Path(out).glob('repro-*.json'))
            row = json.loads(path.read_text())
            self.assertEqual(row['campaign'], 'node')
            self.assertEqual(row['role'], 'reader')
            small = [bytes.fromhex(x) for x in row.get('minimized_hex') or row['chunks_hex']]
            self.assertEqual(len(small), 1)
            self.assertEqual(d.compare(small, plants=('reuse-number',)).rows[0]['rule'], 'GROUP')
            self.assertLessEqual(len(bytes.fromhex(row['reply_hex'])), 1024)
            self.assertTrue((Path(out) / 'run.pid').is_file())
            self.assertEqual(json.loads((Path(out) / 'summary.json').read_text())['minimized_reproducers'], 1)


if __name__ == '__main__':
    unittest.main()

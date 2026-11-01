"""No node/image required: wire controls, planted failures and corpus inventory."""
from contextlib import contextmanager, nullcontext
import errno
import json
import os
from pathlib import Path
import socket
import ssl
import shutil
import subprocess
import tempfile
import threading
import unittest
from unittest.mock import patch

from . import differential as d
from .nntp_model import Expect

ARTIFACTS = Path(os.environ.get('H2B_ARTIFACTS', f'/tmp/h2b-tests-{os.getpid()}'))


def setUpModule():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    (ARTIFACTS / 'run.pid').write_text(str(os.getpid()) + '\n')


class DifferentialTests(unittest.TestCase):
    def test_tls_incomplete_body_orderly_eof_keeps_final_reply(self):
        self.tls_close_control(peer_first=False)

    def test_tls_peer_initiated_close_gets_client_notify(self):
        self.tls_close_control(peer_first=True)
        self.tls_close_control(peer_first='cleanup')

    def tls_close_control(self, *, peer_first):
        openssl = os.environ.get('FN_TEST_OPENSSL_BIN') or shutil.which('openssl')
        self.assertIsNotNone(openssl, 'openssl required for loopback TLS control')
        with tempfile.TemporaryDirectory(prefix='hs-tls-') as tmp:
            cert, key = Path(tmp) / 'cert.pem', Path(tmp) / 'key.pem'
            subprocess.run([openssl, 'req', '-x509', '-newkey', 'rsa:2048', '-nodes',
                            '-keyout', str(key), '-out', str(cert), '-days', '1',
                            '-subj', '/CN=localhost'], check=True, timeout=20,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            server = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            server.load_cert_chain(cert, key)
            client = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
            client.check_hostname = False
            client.verify_mode = ssl.CERT_NONE
            for version in (ssl.TLSVersion.TLSv1_2, ssl.TLSVersion.TLSv1_3):
                server.minimum_version = server.maximum_version = version
                client.minimum_version = client.maximum_version = version
                errors, observed = [], []
                with socket.socket() as listener:
                    local_pair, why = None, ''
                    try:
                        # Reader sessions connect from 127.0.0.2 (fixture()); macOS
                        # has no such loopback alias, Linux has all of 127/8.
                        with socket.socket() as source:
                            source.bind(('127.0.0.2', 0))
                        listener.bind(('127.0.0.1', 0))
                        listener.listen(1)
                        listener.settimeout(3)
                    except OSError as exc:
                        # A sandbox may forbid bind; a host may lack the alias.
                        # Exercise identical TLS bytes over local connected FDs;
                        # the TCP branch runs where both binds succeed (hbox).
                        local_pair, why = socket.socketpair(), f' ({exc.strerror})'
                    (ARTIFACTS / 'tls-transport.txt').write_text(
                        'socketpair' + why + '\n' if local_pair else 'TCP loopback\n')
                    def respond():
                        try:
                            raw = local_pair[1] if local_pair else listener.accept()[0]
                            raw.settimeout(3)
                            with server.wrap_socket(raw, server_side=True, suppress_ragged_eofs=False) as stream:
                                stream.sendall(b'200 ready\r\n')
                                pending = bytearray()
                                while b'\r\n' not in pending:
                                    chunk = stream.recv(4096)
                                    self.assertTrue(chunk, 'EOF before POST')
                                    pending.extend(chunk)
                                if peer_first:
                                    self.assertEqual(pending, b'DATE\r\n' if peer_first == 'cleanup' else b'QUIT\r\n')
                                    stream.sendall(b'503 unavailable\r\n' if peer_first == 'cleanup' else b'205 closing\r\n')
                                    raw = stream.unwrap()
                                    observed.append('client-close-notify')
                                    raw.close()
                                    return
                                self.assertEqual(pending, b'POST\r\n')
                                stream.sendall(b'340 proceed\r\n')
                                pending.clear()
                                while True:
                                    data = stream.recv(4096)
                                    if not data:
                                        observed.append('client-close-notify')
                                        break
                                    pending.extend(data)
                                self.assertEqual(pending, b'From: a@b\r\n')
                                stream.sendall(b'441 posting failed; the article was not received\r\n')
                                raw = stream.unwrap()
                                raw.close()
                        except BaseException as exc:
                            errors.append(exc)
                    worker = threading.Thread(target=respond, daemon=True)
                    worker.start()
                    node = type('Node', (), {'config': None, 'tls_port': listener.getsockname()[1],
                                             'tls_context': lambda _: client, 'alive': lambda _: True})()
                    try:
                        with (patch.object(d.socket, 'create_connection', return_value=local_pair[0])
                              if local_pair else nullcontext()):
                            result = d.compare([b'DATE\r\n' if peer_first == 'cleanup' else b'QUIT\r\n']
                                               if peer_first else [b'POST\r\n', b'From: a@b\r\n'],
                                               node=node, transport='implicit', timeout=2)
                    finally:
                        worker.join(5)
                    self.assertFalse(worker.is_alive())
                    self.assertEqual(errors, [])
                    self.assertEqual(observed, ['client-close-notify'])
                    self.assertEqual(result.rows, [], result)
                    self.assertEqual(result.exchanges[-1]['rule'], 'DATE' if peer_first == 'cleanup' else
                                     'QUIT' if peer_first else 'POST')
                    self.assertTrue(result.exchanges[-1]['status_hex'].startswith(
                        (b'503' if peer_first == 'cleanup' else b'205' if peer_first else b'441').hex()))
                    self.assertTrue(result.wire['client_close_notify'])
                    self.assertTrue(result.wire['server_close_notify'], result.wire)
                    self.assertFalse(result.wire['reply_client_half_closed'])
                    self.assertIsNone(result.wire['reset'])

    def test_reset_after_close_notify_is_not_old_driver_halfclose(self):
        expected = Expect([441], rule='POST')
        old = d.reply_verdict(expected, b'', None, reset='reset', tls=True,
                              client_half_closed=True)
        new = d.reply_verdict(expected, b'', None, reset='reset', tls=True,
                              client_close_notify=True)
        self.assertEqual(old.rule, 'driver-environment')
        self.assertEqual(new.rule, 'tls-close')
        self.assertFalse(new.ok)

    def test_takethis_body_probe_awaited_silent_wrong_and_missing_id(self):
        original = d.Fake.sendall
        command = b'TAKETHIS <probe@test> \r\n'  # Valid ID, malformed trailing space.
        for reply in (b'439 <probe@test> malformed article\r\n', b'',
                      b'239 <probe@test> accepted\r\n'):
            sent = []
            def respond(server, data):
                sent.append(data)
                if data == command:
                    return
                if data == b'\r\n.\r\n':
                    server.output.extend(reply)
                    return
                original(server, data)
            with patch.object(d.Fake, 'sendall', respond):
                result = d.compare([command], mode='peer', takethis_probe=True)
            evidence = result.exchanges[-1]['takethis_probe']
            self.assertEqual(evidence['observation'], 'awaited-body' if reply else 'no-reply-after-body')
            self.assertLessEqual(len(bytes.fromhex(evidence['body_hex'])), 512)
            self.assertTrue(evidence['command_verdict']['ok'])
            self.assertEqual(result.rows == [], reply.startswith(b'439'))
            replay = d.replay_recorded(dict(mode='peer', exchanges=result.exchanges, wire=result.wire))
            self.assertEqual(replay['matched'], reply.startswith(b'439'))
            if reply:
                self.assertEqual(evidence['article_verdict']['ok'], reply.startswith(b'439'))
            else:
                self.assertEqual(result.rows[0]['rule'], 'TAKETHIS')
            with patch.object(d.Fake, 'sendall', respond):
                sent.clear()
                control = d.compare([command], mode='peer')
            self.assertTrue(control.rows)  # EOF without an article still fails.
            self.assertNotIn(b'\r\n.\r\n', sent)
        command = b'TAKETHIS <a@b\r\n'
        reply = b'439 <a@b malformed article\r\n'
        with patch.object(d.Fake, 'sendall', respond):
            result = d.compare([command], mode='peer', takethis_probe=True)
        self.assertFalse(result.rows)
        self.assertEqual(result.exchanges[-1]['takethis_probe']['article_verdict']['echo_binding'], 'token-or-dash')
        command = b'takethis <probe@test> \r\n'
        reply = b'439 <probe@test> malformed article\r\n'
        with patch.object(d.Fake, 'sendall', respond):
            self.assertEqual(d.compare([command], mode='peer', takethis_probe=True).rows, [])

    def test_malformed_takethis_early_reply_and_body_as_commands_is_caught(self):
        original = d.Fake.sendall
        command = b'TAKETHIS <a@b\r\n'
        def premature(server, data):
            if data == command:
                server.output.extend(b'439 <a@b refused\r\n')
                return  # Mutation: never enter body mode; subsequent lines are commands.
            original(server, data)
        for probe in (False, True):
            with self.subTest(probe=probe), patch.object(d.Fake, 'sendall', premature):
                result = d.compare([command, b'Subject: article\r\n\r\n.\r\n',
                                    b'DATE\r\n'], mode='peer', takethis_probe=probe)
            self.assertTrue(result.rows)
        self.assertFalse(d.replay_recorded(dict(mode='peer', exchanges=[
            dict(command_index=0, command_hex=command.hex(), status_hex=b'439 <a@b refused\r\n'.hex(),
                 body_hex=None, takethis_probe=dict(command_reply=dict(
                     status_hex=b'439 <a@b refused\r\n'.hex(), body_hex=None),
                     body_hex=b'\r\n.\r\n'.hex(), wire_eof=False,
                     wire_reset=None, wire_timeout=False))]))['matched'])

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

    def test_reply_window_grows_with_segments_sent(self):
        # H7-08: a bytewise send of N segments gives the reply N * 0.1 ms more, capped at 60 s, then resets.
        wire = d.Wire(d.Fake('peer', 'plain'), None, timeout=3)
        wire.send([b'x'] * 100000)
        self.assertAlmostEqual(wire.reply_window(), 13.0)
        self.assertEqual(wire.reply_window(), 3)
        wire.send([b'x'] * 10 ** 7)
        self.assertEqual(wire.reply_window(), 63.0)

    def test_focus_generators_agree_on_the_fake(self):
        # H7c: tls_auth's and peering's F use these; the unmutated fake must agree on every cut.
        for kind, mode in (('auth', 'reader'), ('feed', 'peer')):
            seen = set()
            for seed in range(60):
                items = d.generator(seed, mode, kind).transcript(20)
                seen.update(item.split(b' ', 1)[0].rstrip(b'\r\n').upper() for item in items)
                for cut in ('whole', 'bytewise'):
                    with self.subTest(kind=kind, seed=seed, cut=cut):
                        self.assertEqual(d.compare(items, seed=seed, mode=mode, cut=cut,
                                                   transport=('plain', 'starttls', 'implicit')[seed % 3]).rows, [])
            wanted = {b'AUTHINFO', b'XREDEEM', b'STARTTLS'} if kind == 'auth' else {b'IHAVE', b'CHECK', b'TAKETHIS', b'XFNCATCHUP'}
            self.assertLessEqual(wanted, seen, kind)

    def test_each_mutation_caught_and_minimized(self):
        expected = {'reuse-number': {'GROUP'}, '423-for-420': {'XOVER'},
                    'frame-after-quit': {'closed'}, 'wrong-over-field': {'OVER', 'XOVER'},
                    'dot-unstuffed': {'BODY'}, 'auth-wrong-accepted': {'AUTHINFO'},
                    'feed-wrong-id': {'CHECK', 'TAKETHIS'}}
        # H7c: the focus plants run under their family's focused generator and mode.
        focus = {'auth-wrong-accepted': ('auth', 'reader'), 'feed-wrong-id': ('feed', 'peer')}
        table = {}
        for plant in d.PLANTS:
            kind, mode = focus.get(plant, (None, 'reader'))
            for seed in range(200):
                items = d.generator(seed, mode, kind).transcript(20)
                run = lambda xs: d.compare(xs, seed=seed, mode=mode, plants=(plant,))
                result = run(items)
                if not result.rows:
                    continue
                row = result.rows[0]
                self.assertIn(row['rule'], expected[plant], row)
                self.assertEqual(row['class'], 'unclassified')
                self.assertEqual(d.compare(items, seed=seed, mode=mode).rows, [], 'unmutated control')
                small = d.minimize(items, row, run, seconds=10)
                self.assertLessEqual(len(small), 3)
                reduced = run(small)
                self.assertEqual(reduced.rows[0]['rule'], row['rule'])
                # Units are commands, including one complete article block.
                self.assertLessEqual(len(reduced.commands), 3)
                for cut in d.CUTS:
                    self.assertEqual(d.compare(small, cut=cut, mode=mode).rows, [])
                    self.assertEqual(d.compare(small, cut=cut, mode=mode, plants=(plant,)).rows[0]['rule'], row['rule'])
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

    def test_compression_authentication_and_capability_transitions(self):
        commands = [line + b'\r\n' for line in (
            b'CAPABILITIES', b'COMPRESS DEFLATE', b'AUTHINFO USER fuzz',
            b'AUTHINFO PASS fuzz-password', b'CAPABILITIES', b'COMPRESS DEFLATE',
            b'CAPABILITIES', b'AUTHINFO USER fuzz', b'COMPRESS DEFLATE')]
        for mode in ('reader', 'node', 'peer'):
            for transport in ('plain', 'starttls', 'implicit'):
                with self.subTest(mode=mode, transport=transport):
                    result = d.compare(commands, mode=mode, transport=transport)
                    self.assertEqual(result.rows, [])
                    compress = [bytes.fromhex(row['status_hex'])[:3] for row in result.exchanges
                                if bytes.fromhex(row['command_hex']) == b'COMPRESS DEFLATE\r\n']
                    self.assertEqual(compress, [b'480', b'206', b'502'])
                    caps = [row for row in result.exchanges
                            if bytes.fromhex(row['command_hex']) == b'CAPABILITIES\r\n']
                    label = b'COMPRESS DEFLATE\r\n'
                    self.assertEqual([label in bytes.fromhex(row['body_hex']) for row in caps],
                                     [False, True, False])
                    record = dict(mode=mode, transport=transport, exchanges=result.exchanges,
                                  wire=result.wire)
                    self.assertTrue(d.replay_recorded(record)['matched'])
                    caps[1]['body_hex'] = bytes.fromhex(caps[1]['body_hex']).replace(label, b'').hex()
                    self.assertFalse(d.replay_recorded(record)['matched'])

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

    def test_fake_creation_window_predicate_renderer(self):
        for cut in d.CUTS:
            result = d.compare([b'NEWGROUPS 20260101 000000 GMT\r\n',
                                b'NEWNEWS * 20260101 000000 GMT\r\nQUIT\r\n'], cut=cut)
            self.assertEqual(result.rows, [])

    def test_negotiated_tls_version_reaches_model_and_evidence(self):
        original_connection = d.connection
        for transport in ('implicit', 'starttls'):
            for negotiated in ('TLSv1.2', 'TLSv1.3'):
                observed = []
                def connection(model, mode, transport):
                    conn = original_connection(model, mode, transport)
                    observed.append(conn)
                    return conn
                def socket_connection(*args, **kwargs):
                    sock = d.Fake('reader', transport)
                    sock.version = lambda: negotiated
                    sock.settimeout = lambda *_: None
                    sock.setsockopt = lambda *_: None
                    return sock
                context = type('TLS', (), {'wrap_socket': lambda _, sock, **kw: sock})()
                node = type('Node', (), {'config': None, 'port': 1, 'tls_port': 2,
                                         'tls_context': lambda _: context,
                                         'alive': lambda _: True})()
                with self.subTest(transport=transport, negotiated=negotiated), patch.object(d, 'connection', connection), patch.object(d.socket, 'create_connection', socket_connection):
                    result = d.compare([b'QUIT\r\n'], node=node, transport=transport)
                self.assertEqual(result.rows, [])
                self.assertEqual(observed[0].policy['tls_version'], negotiated)
                self.assertEqual(observed[0].model.policy['tls_version'], negotiated)
                self.assertEqual(result.wire['tls_version'], negotiated)

    def test_recorded_status_boundaries_and_empty_reply(self):
        # H2b's wrong-number rows all contain zero octets. A following reply
        # sharing a recv must remain for the next expectation, never concatenate.
        sock = d.Fake('reader', 'plain')
        sock.output = bytearray(b'501 command syntax error\r\n502 command unavailable\r\n')
        wire = d.Wire(sock)
        first = Expect([501], rule='syntax')
        second = Expect([502], rule='MODE')
        self.assertEqual(wire.reply(first), (b'501 command syntax error\r\n', None))
        self.assertEqual(wire.reply(second), (b'502 command unavailable\r\n', None))
        sock.closed = True
        self.assertEqual(wire.reply(first), (b'', None))
        self.assertIn('wrong number', first.check(b'', None).detail)

    @staticmethod
    def recorded(exchanges, **wire):
        """Wire evidence, not fake-generated replies or invented state commits."""
        return dict(mode='reader', transport='plain', wire=wire,
                    exchanges=[dict(command_index=i - 1, command_hex=cmd.hex(),
                                    status_hex=status.hex(), body_hex=None,
                                    rule='', detail='', ok=True)
                               for i, (cmd, status) in enumerate(exchanges)])

    def test_recorded_eof_belongs_to_malformed_command(self):
        # Exact malformed line/reply from run 2 shard-0 repro-3-peer-whole-00030.
        command = b'HEAD <a@b\r>\r\n'
        source = self.recorded([(b'', b'200 fn-nntp experimental server ready\r\n'),
                                (command, b'501 syntax error\r\n'),
                                (b'HELP\r\n', b'')],
                               eof=True, reply_eof=True, reply_timeout=False)
        result = d.replay_recorded(source)
        self.assertTrue(result['matched'], result)
        self.assertEqual(result['closure']['command_index'], 0)
        self.assertEqual(result['closure']['command_hex'], command.hex())
        self.assertEqual(result['closure']['observed_at_index'], 1)
        self.assertEqual(len(result['exchanges']), 2)
        self.assertIn('513-518', result['closure']['spec'])
        # Semantic syntax failure has no blanket close permission.
        source['exchanges'][1]['command_hex'] = b'MODE X\r\n'.hex()
        result = d.replay_recorded(source)
        self.assertFalse(result['matched'])
        self.assertIsNone(result['closure'])
        self.assertEqual(result['rows'][0]['command_index'], 1)

    def test_live_eof_attribution_stops_after_permitted_close(self):
        command = b'HEAD <a@b\r>\r\n'
        original = d.Fake.sendall
        def closing(server, data):
            if server.closed:
                return
            pending = bytes(server.input) + data
            if command in pending:
                end = pending.index(command) + len(command) - len(server.input)
                original(server, data[:end])
                server.closed = True
            else:
                original(server, data)
        with patch.object(d.Fake, 'sendall', closing):
            for cut in d.CUTS:
                result = d.compare([command + b'HELP\r\nDATE\r\n'], cut=cut)
                self.assertEqual(result.rows, [])
                self.assertEqual(result.closure['command_index'], 0)
                self.assertEqual(result.compared, 1)

    def test_quit_requires_server_eof_without_client_halfclose(self):
        original = d.Fake.recv
        def wait_for_client(server, size):
            if server.conn.quit and not server.output and not server.closed:
                raise socket.timeout('server forgot to close after QUIT')
            return original(server, size)
        with patch.object(d.Fake, 'recv', wait_for_client):
            for transcript in ([b'QUIT\r\n'], [b'QUIT\r\nHELP\r\n']):
                result = d.compare(transcript)
                self.assertTrue(result.rows)
                self.assertTrue(result.wire['timeout'])
                self.assertFalse(result.wire['eof'])
                self.assertFalse(result.wire['reply_client_half_closed'])
                self.assertIn('EOF', result.rows[0]['detail'])

    def test_eof_after_final_drain_is_not_reply_eof(self):
        source = self.recorded([(b'', b'200 ready\r\n'),
                                (b'HEAD <a@b\r>\r\n', b'501 syntax error\r\n'),
                                (b'HELP\r\n', b'')],
                               eof=True, reply_eof=False, reply_timeout=True)
        result = d.replay_recorded(source)
        self.assertFalse(result['matched'])
        self.assertIsNone(result['closure'])
        self.assertTrue(result['rows'][0]['wire_timeout'])

    def test_recorded_silent_close_and_tls_client_halfclose_reset(self):
        source = self.recorded([(b'', b'200 ready\r\n'),
                                (b'HEAD <a@b\r>\r\n', b'')],
                               eof=True, reply_eof=True, reply_timeout=False)
        result = d.replay_recorded(source)
        self.assertTrue(result['matched'], result)
        self.assertEqual(result['closure']['evidence'], 'eof-without-reply')
        # Exact reset kind in run 2 seed 203: our raw SHUT_WR on TLS cannot
        # establish a clean server decision about an incomplete POST body.
        source = self.recorded([(b'', b'200 ready\r\n'),
                                (b'POST\r\n', b'340 send article to be posted\r\n'),
                                (b'From: author@example.invalid\r\n', b'')],
                               eof=True, reply_eof=True, reply_timeout=False,
                               reply_reset="SSLError(1, '[SSL: TLSV1_ALERT_DECODE_ERROR]')")
        source['transport'] = 'implicit'
        result = d.replay_recorded(source)
        self.assertFalse(result['matched'])
        self.assertIsNone(result['closure'])
        self.assertEqual(result['rows'][0]['rule'], 'driver-environment')

    def test_recorded_replay_uses_observed_state_and_stops_at_bad_commit(self):
        source = self.recorded([(b'', b'200 ready\r\n'),
                                (b'GROUP fn.test\r\n', b'211 0 1 0 fn.test\r\n'),
                                (b'STAT\r\n', b'420 no current article\r\n')])
        self.assertTrue(d.replay_recorded(source)['matched'])
        source['exchanges'][1]['status_hex'] = b'211 99 1 99 fn.test\r\n'.hex()
        result = d.replay_recorded(source)
        self.assertFalse(result['matched'])
        self.assertEqual(len(result['exchanges']), 2)
        self.assertEqual(result['rows'][0]['rule'], 'GROUP')

    def test_recorded_missing_evidence_and_environment_fail_closed(self):
        self.assertFalse(d.replay_recorded({'exchanges': []})['matched'])
        source = self.recorded([(b'', b'200 ready\r\n'),
                                (b'AUTHINFO SASL SCRAM-SHA-256-PLUS\r\n', b'383 =\r\n')])
        source['transport'] = 'implicit'
        source['wire']['tls_version'] = 'TLSv1.3'
        result = d.replay_recorded(source)
        self.assertFalse(result['matched'])
        self.assertEqual(result['rows'][0]['rule'], 'driver-environment')
        self.assertIn('exporter', result['rows'][0]['detail'])
        body = (b'From: author@example.invalid\r\nSubject: test\r\n'
                b'Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n'
                b'Newsgroups: fn.test\r\n\r\nbody\r\n.\r\n')
        source = self.recorded([(b'', b'200 ready\r\n'),
                                (b'POST\r\n', b'340 proceed\r\n'),
                                (body, b'240 accepted\r\n')])
        result = d.replay_recorded(source)
        self.assertFalse(result['matched'])
        self.assertEqual(result['rows'][0]['rule'], 'driver-environment')
        self.assertIn('generated_id', result['rows'][0]['detail'])

    def test_reply_timeout_survives_final_drain_and_disables_reuse(self):
        original = d.Fake.recv
        calls = 0
        def timeout(server, size):
            nonlocal calls
            calls += 1
            if calls == 2:
                raise socket.timeout('delayed first reply')
            return original(server, size)
        with patch.object(d.Fake, 'recv', timeout):
            result = d.compare([b'HELP\r\n'])
        self.assertTrue(result.wire['reply_timeout'])
        self.assertTrue(result.wire['timeout'])
        self.assertTrue(result.wire['eof'])
        self.assertFalse(result.reusable)
        self.assertTrue(result.rows[0]['wire_timeout'])

    def test_recorded_incomplete_post_eof_reply(self):
        # Exact reply bytes from shard-2/repro-404-reader-whole-00036.json.
        original = d.Fake.shutdown
        def eof_refusal(server, how):
            owed = bool(server.conn.pending)
            original(server, how)
            if owed:
                server.output = bytearray(b'441 posting failed; the article was not received\r\n')
        with patch.object(d.Fake, 'shutdown', eof_refusal):
            result = d.compare([b'POST\r\n', b'IHAVE <reader@example.invalid>\r\n'],
                               transport='plain')
        self.assertEqual(result.rows, [])
        self.assertEqual(result.exchanges[-1]['status_hex'],
                         b'441 posting failed; the article was not received\r\n'.hex())
        self.assertEqual(result.exchanges[-1]['rule'], 'POST')

    def test_reuse_excludes_mutation_anywhere_and_refreshes_sessions(self):
        for token in (b'POST', b'IHAVE', b'TAKETHIS', b'AUTHINFO', b'XREDEEM', b'CHECK', b'XFN'):
            self.assertFalse(d.read_only([b'HELP\r\n', token.lower(), b' suffix\r\n']))
        self.assertFalse(d.read_only([b'PO', b'ST\r\n']))
        self.assertTrue(d.read_only([b'GROUP fn.test\r\nQUIT\r\n']))
        opened, closed = [], []
        @contextmanager
        def owner(image, directory, ports):
            node = object()
            opened.append(node)
            try:
                yield node
            finally:
                closed.append(node)
        seen = []
        def compare(items, node, **kw):
            seen.append(node)
            return d.Result(reusable=d.read_only(items))
        with tempfile.TemporaryDirectory() as tmp, patch.object(d, 'owner', owner), patch.object(d, 'compare', compare):
            with d.SessionRunner('image', Path(tmp)) as run:
                for cut in d.CUTS:
                    run([b'HELP\r\n'], cut=cut)
                self.assertEqual(len(opened), 1)
                run([b'POST\r\n'])
                run([b'HELP\r\n'])
                self.assertEqual(len(opened), 3)
                self.assertEqual(len(closed), 2)
            self.assertEqual(opened, closed)
        # Concrete compare creates a new model/connection even on one live Node.
        node = type('Node', (), {'config': None, 'port': 1, 'alive': lambda _: True})()
        models = []
        original_connection = d.connection
        def connection(model, mode, transport):
            models.append(model)
            return original_connection(model, mode, transport)
        def socket_connection(*args, **kwargs):
            sock = d.Fake('reader', 'plain')
            sock.conn = original_connection(d.fixture(False), 'reader', 'plain')
            sock.settimeout = lambda *_: None
            sock.setsockopt = lambda *_: None
            return sock
        with patch.object(d, 'connection', connection), patch.object(d.socket, 'create_connection', socket_connection):
            for _ in range(2):
                self.assertEqual(d.compare([b'GROUP fn.test\r\nQUIT\r\n'], node=node).rows, [])
        # fake socket creates its independent model as well as compare's model.
        self.assertIsNot(models[0], models[2])

    def test_setup_failures_continue_and_collision_retries_once(self):
        for failure, attempts in ((ValueError('invalid setup config'), 1),
                                  (RuntimeError('peer add: CONFIGURATION INVALID'), 1),
                                  (RuntimeError('no LISTENING announcement'), 1),
                                  (RuntimeError('listen: EADDRINUSE'), 2),
                                  (OSError(errno.EADDRINUSE, 'address already in use'), 2)):
            calls = []
            @contextmanager
            def owner(image, directory, ports):
                calls.append(directory)
                raise failure
                yield
            with tempfile.TemporaryDirectory() as tmp, patch.object(d, 'owner', owner):
                with d.SessionRunner('image', Path(tmp)) as run:
                    for _ in range(2):
                        result = run([b'HELP\r\n'])
                        self.assertEqual(result.rows[0]['rule'], 'driver-environment')
                    self.assertEqual(len(calls), 2 * attempts)
                    self.assertEqual(len(set(calls)), len(calls))

    def test_collision_then_success_uses_fresh_ports(self):
        calls = []
        @contextmanager
        def owner(image, directory, ports):
            calls.append((ports(), ports()))
            if len(calls) == 1:
                raise RuntimeError('listen: EADDRINUSE')
            yield object()
        with tempfile.TemporaryDirectory() as tmp, patch.object(d, 'owner', owner), patch.object(d, 'compare', return_value=d.Result(reusable=True)):
            # This is a retry/ownership control, not a bind-availability test.
            with d.SessionRunner('image', Path(tmp), ports=iter(range(31000, 31004)).__next__) as run:
                result = run([b'HELP\r\n'])
                self.assertEqual(len(result.rows), 1)
                self.assertEqual(result.rows[0]['rule'], 'driver-environment')
                self.assertTrue(result.rows[0]['recovered'])
                self.assertIn('recovered by fresh-port retry', result.rows[0]['detail'])
        self.assertEqual(len(calls), 2)
        self.assertEqual(len(set(sum((list(x) for x in calls), []))), 4)

    def test_cli_environment_failure_records_each_session_without_minimizing(self):
        @contextmanager
        def owner(*args):
            raise RuntimeError('peer add: CONFIGURATION INVALID')
            yield
        with tempfile.TemporaryDirectory() as tmp, patch.object(d, 'owner', owner), patch.object(d, 'minimize') as minimize:
            image = Path(tmp) / 'image'
            image.touch()
            rc = d.main(['--target', 'fn1', '--image', str(image), '--seeds', '0..0',
                         '--mode', 'reader', '--steps', '1', '--out', tmp])
            self.assertEqual(rc, 1)
            self.assertEqual(json.loads((Path(tmp) / 'summary.json').read_text())['sessions'], 3)
            rows = [json.loads(x) for x in (Path(tmp) / 'differences.jsonl').read_text().splitlines()]
            self.assertEqual(len(rows), 3)
            self.assertTrue(all(r['rule'] == 'driver-environment' for r in rows))
            minimize.assert_not_called()

    def test_minimize_deadline_includes_initial_session(self):
        clock, calls = [0.0], []
        items = [b'DATE\r\n', b'HELP\r\n']
        def run(candidate):
            calls.append(candidate)
            clock[0] += 2
            return d.Result(commands=items, rows=[dict(rule='DATE', detail='planted')])
        with patch.object(d.time, 'monotonic', side_effect=lambda: clock[0]):
            self.assertEqual(d.minimize(items, dict(rule='DATE', detail='planted'), run, 1), items)
        self.assertEqual(len(calls), 1)

    def test_cli_budget_expiry_preserves_unminimized_evidence(self):
        clock, calls = [0.0], []
        row = dict(rule='DATE', detail='planted', **{'class': 'unclassified'})
        exchange = dict(command_hex=b'DATE\r\n'.hex(), status_hex=b'500 bad\r\n'.hex())
        def run(items, **kwargs):
            calls.append(items)
            clock[0] += 2
            return d.Result(rows=[row], exchanges=[exchange], compared=1)
        with tempfile.TemporaryDirectory() as tmp, \
                patch.object(d.time, 'monotonic', side_effect=lambda: clock[0]), \
                patch.object(d, 'SessionRunner', return_value=nullcontext(run)), \
                patch.object(d, 'minimize') as minimize:
            rc = d.main(['--target', 'fake', '--seeds', '0..9', '--mode', 'reader',
                         '--steps', '1', '--seconds', '1', '--out', tmp])
            self.assertEqual(rc, 1)  # A completed budget does not erase a mismatch.
            summary = json.loads((Path(tmp) / 'summary.json').read_text())
            self.assertTrue(summary['budget_exhausted'])
            self.assertEqual(summary['sessions'], 1)
            repro = json.loads(next(Path(tmp).glob('repro-*.json')).read_text())
            self.assertEqual(repro['minimized_commands_hex'], repro['chunks_hex'])
            self.assertEqual(repro['minimized_exchanges'], repro['exchanges'])
            minimize.assert_not_called()
        self.assertEqual(len(calls), 1)

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
            self.assertTrue(row['exchanges'])
            self.assertTrue(row['minimized_exchanges'])
            self.assertEqual(row['minimized_rows'][0]['detail'], row['detail'])
            self.assertIn('received_hex', row['wire'])
            self.assertIn('reply_timeout', row['wire'])
            self.assertTrue((Path(out) / 'run.pid').is_file())
            self.assertEqual(json.loads((Path(out) / 'summary.json').read_text())['minimized_reproducers'], 1)


if __name__ == '__main__':
    unittest.main()

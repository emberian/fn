"""HU socket-free controls. Fake is independent: it never calls NntpModel.

It implements only this driver's commands, with deterministic SCRAM server
nonces/salts. Its wire answers and mutation switches are not model evidence or
fn1 adjudications. Tests exercise the same machine/check/update path as live S.
"""
import base64
import copy
import hashlib
import hmac
import unittest
from unittest import mock

from fn2.tests.surface.tls_auth.test_model_tls_auth import GROUP, IDENT, Wire, machine


def b64(raw):
    return base64.b64encode(raw)


def mac(key, raw):
    return hmac.new(key, raw, hashlib.sha256).digest()


class FakeTarget:
    mutation = None

    def __init__(self, case, accounts, policy):
        self.case, self.accounts, self.policy = case, copy.deepcopy(accounts), dict(policy)
        self.invitations, self.clients = {}, []
        self.serial = 0

    def invite(self):
        self.serial += 1
        code = f'{self.serial:032x}'
        self.invitations[code] = None
        return code

    def connect(self, implicit=False):
        client = Fake(self, implicit)
        self.clients.append(client)
        self.case.addCleanup(client.close)
        return client


class Fake:
    def __init__(self, target, tls):
        self.target, self.tls = target, tls
        self.accounts = copy.deepcopy(target.accounts)
        self.greeting = b'201 ready\r\n' if target.policy['required'] else b'200 ready\r\n'
        self.user = self.login = self.selected = self.exchange = self.redemption = None
        self.failures, self.pending = 0, []
        self.closed = self.compressed = self.handshaking = self.tls_refused = False

    def reply(self, code, data=b'fake'):
        return str(code).encode() + b' ' + data + b'\r\n'

    def failed(self, cancelled=False):
        self.user = self.exchange = None
        if not cancelled:
            self.failures += 1
            if self.failures == 3:
                self.pending.append(self.reply(400))
                self.closed = self.target.mutation != 'no-third-close'
        return self.reply(481)

    def authenticated(self, login, code=281, data=b'accepted'):
        self.login, self.user, self.exchange = login, None, None
        return self.reply(code, data)

    def command(self, command):
        if self.closed:
            raise EOFError('closed fake')
        text = command.decode()
        if self.exchange:
            if text == '*':
                return self.failed(cancelled=True)
            return self.sasl_response(base64.b64decode(command, validate=True))
        words = text.split()
        verb, args = words[0], words[1:]
        if verb == 'QUIT':
            self.closed = True
            return self.reply(205)
        if verb == 'STARTTLS':
            if self.tls or self.login or self.compressed:
                self.tls_refused = True
                return self.reply(502)
            self.handshaking, self.user = True, None
            return self.reply(382)
        if verb == 'COMPRESS':
            if self.compressed:
                return self.reply(502)
            if not self.login:
                return self.reply(480)
            return self.reply(206)
        if verb in ('GROUP', 'STAT'):
            if self.target.policy['required'] and not self.login:
                return self.reply(480)
            if verb == 'GROUP':
                self.selected = GROUP
                return self.reply(211, b'1 1 1 surface.test')
            return self.reply(223, ('1 ' + IDENT).encode()) if self.selected else self.reply(412)
        if verb == 'AUTHINFO':
            if self.target.mutation == 'auth-after-refused-tls' and self.tls_refused:
                self.user = args[-1]
                return self.reply(381)
            if self.login or self.compressed:
                return self.reply(502)
            form = args[0]
            if not self.tls and (self.target.policy['protected_only'] or args[:2] == ['SASL', 'PLAIN']):
                return self.reply(483)
            if form == 'USER':
                self.user = args[1]
                return self.reply(381)
            if form == 'PASS':
                if self.user is None:
                    return self.reply(482)
                good = self.accounts.get(self.user, {}).get('password') == args[1]
                if good or self.target.mutation == 'wrong-password':
                    return self.authenticated(self.user)
                return self.failed()
            self.exchange = args[1]
            if len(args) == 2:
                return self.reply(383, b'=')
            return self.sasl_response(base64.b64decode(args[2], validate=True))
        if verb == 'XREDEEM':
            if self.login or self.compressed:
                return self.reply(502)
            if self.target.policy['protected_only'] and not self.tls:
                return self.reply(483)
            if args[0] != 'PASS':
                self.redemption = tuple(args)
                return self.reply(381)
            if not self.redemption:
                return self.reply(482)
            code, login = self.redemption
            self.redemption = None
            if code not in self.target.invitations or self.target.invitations[code] is not None:
                return self.reply(482)
            self.target.invitations[code] = (login, args[1])
            self.target.accounts[login] = {'password': args[1], 'posting': True}
            return self.reply(281)
        raise AssertionError('fake lacks command ' + text)

    def sasl_response(self, raw):
        if self.exchange == 'PLAIN':
            _, login, password = raw.decode().split('\0')
            if self.accounts.get(login, {}).get('password') == password:
                return self.authenticated(login)
            return self.failed()
        if self.exchange == 'SCRAM-SHA-256':
            self.bare = raw[3:]
            fields = dict(part.split(b'=', 1) for part in self.bare.split(b','))
            self.scram_login = fields[b'n'].decode()
            self.salt = b'HU independent fake salt'
            self.server_first = b'r=' + fields[b'r'] + b'-server,s=' + b64(self.salt) + b',i=4096'
            self.exchange = 'scram-final'
            return self.reply(383, b64(self.server_first))
        without_proof, proof = raw.rsplit(b',p=', 1)
        auth = self.bare + b',' + self.server_first + b',' + without_proof
        password = self.accounts.get(self.scram_login, {}).get('password', 'unknown')
        salted = hashlib.pbkdf2_hmac('sha256', password.encode(), self.salt, 4096)
        key = mac(salted, b'Client Key')
        signature = mac(hashlib.sha256(key).digest(), auth)
        wanted = bytes(a ^ b for a, b in zip(key, signature))
        if not hmac.compare_digest(base64.b64decode(proof), wanted):
            return self.failed()
        final = b'v=' + b64(mac(mac(salted, b'Server Key'), auth))
        return self.authenticated(self.scram_login, 283, b64(final))

    def line(self):
        if self.pending:
            return self.pending.pop(0)
        if self.closed:
            raise EOFError('closed fake')
        raise TimeoutError('open fake has no response')

    def establish_tls(self):
        if not self.handshaking:
            raise AssertionError('no fake handshake owed')
        self.tls, self.handshaking = True, False
        if self.target.mutation != 'keep-cursor':
            self.selected = None

    def fail_handshake(self, command):
        self.closed = True
        self.handshake_failure_bytes = b''
        return b'211 framed during handshake\r\n' if self.target.mutation == 'handshake-framing' else b''

    def establish_compression(self):
        self.compressed = True

    def close(self):
        self.closed = True


class TestTlsAuthUnit(unittest.TestCase):
    def make(self, required=False, protected=False, mode='plain', mutation=None):
        target = type('MutatedTarget', (FakeTarget,), {'mutation': mutation})
        driver = machine(self, target)()
        self.addCleanup(driver.teardown)
        first = driver.setup(required, protected, mode)
        return driver, first

    def test_generated_fake_sequences(self):
        from hypothesis import settings
        from hypothesis.stateful import run_state_machine_as_test
        run_state_machine_as_test(machine(self, FakeTarget), settings=settings(
            max_examples=200, stateful_step_count=30, deadline=None,
            database=None, derandomize=True))

    def test_policy_transport_matrix_and_pass_before_user(self):
        for required in (False, True):
            for protected in (False, True):
                for mode in ('plain', 'starttls', 'implicit'):
                    with self.subTest(required=required, protected=protected, mode=mode):
                        d, s = self.make(required, protected, mode)
                        d.compress(s)
                        self.assertEqual(bytes.fromhex(d.trace[-2]['status'])[:3], b'480')
                        self.assertFalse(s.conn.compressed)
                        d.password(s, 'right')
                        d.login(s, 'unknown', False)
                        d.login(s, 'hu-reader', False)
                        d.login(s, 'hu-poster', True)
                        if protected and mode == 'plain':
                            self.assertIsNone(s.conn.authenticated_as)
                            d.starttls(s)
                            d.login(s, 'hu-poster', True)
                        self.assertEqual(s.conn.authenticated_as, 'hu-poster')
                        d.starttls(s)  # refusal preserves authenticated reading
                        d.compress(s)
                        d.compress(s)
                        d.quit(s)

    def test_starttls_resets_real_cursor_twice_and_compression_refusal(self):
        d, s = self.make()
        d.step(s, b'GROUP surface.test')
        self.assertEqual(s.conn.current_article_number, 1)
        d.starttls(s)  # STAT must see 412 before the automatic GROUP
        self.assertEqual(bytes.fromhex(d.trace[-2]['status'])[:3], b'412')
        d.starttls(s)
        d.compress(s)
        self.assertFalse(s.conn.compressed)
        self.assertIsNone(s.conn.authenticated_as)
        d.login(s, 'hu-poster', True)
        d.compress(s)
        self.assertTrue(s.conn.compressed)
        self.assertEqual(s.conn.authenticated_as, 'hu-poster')
        self.assertEqual(bytes.fromhex(d.trace[-2]['command']), b'AUTHINFO USER hu-reader')
        self.assertEqual(bytes.fromhex(d.trace[-2]['status'])[:3], b'502')

    def test_sasl_plain_scram_cancellation_and_success(self):
        for scram in (False, True):
            d, s = self.make(True, True, 'implicit')
            if scram:
                d.scram(s, good=True, cancel=True)
                d.scram(s, good=False, cancel=False)
                d.scram(s, good=True, cancel=False)
            else:
                d.plain(s, good=True, cancel=True, initial=False)
                d.plain(s, good=False, cancel=False, initial=False)
                d.plain(s, good=True, cancel=False, initial=True)
            self.assertEqual(s.conn.failed_auth_count, 1)
            self.assertIsNotNone(s.conn.authenticated_as)

    def test_invitation_fresh_used_wrong_and_pinned_credentials(self):
        d, s = self.make(True, True, 'implicit')
        d.redeem(s, 'pass-first')
        before = len(d.used_codes)
        d.redeem(s, 'fresh')
        self.assertEqual(len(d.used_codes), before + 1)
        self.assertEqual(s.conn.failed_auth_count, 1)  # old pin cannot log in
        d.redeem(s, 'used')
        d.redeem(s, 'wrong')
        d.login(s, 'hu-reader', True)
        d.redeem(s, 'fresh')  # authenticated => 502
        plain = d.open('plain')
        d.redeem(plain, 'fresh')  # protected-only => 483 on both lines

    def test_mutation_wrong_password_authenticates(self):
        # Mandatory setup witness itself must catch it, before model mutation.
        with self.assertRaisesRegex(AssertionError, 'code 281'):
            self.make(mutation='wrong-password')

    def test_mutation_authinfo_after_refused_starttls(self):
        d, s = self.make()
        d.login(s, 'hu-poster', True)
        d.compress(s)
        d.starttls(s)
        d.step(s, b'AUTHINFO USER hu-reader')  # unmutated 502 control
        d.target.mutation = 'auth-after-refused-tls'
        with self.assertRaisesRegex(AssertionError, 'code 381'):
            d.step(s, b'AUTHINFO USER hu-reader')
        self.assertIsNone(s.conn.username)

    def test_mutation_third_failure_does_not_close(self):
        for sasl in (False, True):
            d, _ = self.make()
            d.target.mutation = 'no-third-close'
            with self.assertRaisesRegex(AssertionError, 'mandatory EOF'):
                d.fail_three(sasl)

    def test_mutation_starttls_preserves_cursor(self):
        d, s = self.make()
        d.step(s, b'GROUP surface.test')
        d.target.mutation = 'keep-cursor'
        with self.assertRaisesRegex(AssertionError, 'code 223'):
            d.starttls(s)

    def test_mutation_nntp_framed_during_handshake(self):
        d, _ = self.make()
        d.target.mutation = 'handshake-framing'
        with self.assertRaisesRegex(AssertionError, 'expected no reply and no framing'):
            d.handshake_witness()

    def test_live_wire_rejects_bytes_before_handshake(self):
        client = mock.Mock(greeting=b'200 ready\r\n', pending=b'211 framed\r\n')
        with self.assertRaisesRegex(AssertionError, 'before ClientHello'):
            Wire(client).establish_tls()

    def test_handshake_transport_alert_plaintext_and_timeout(self):
        alert = b'\x15\x03\x03\x00\x02\x02\x0a'
        for data, expected in ((b'', b''), (alert, b''), (b'500 forbidden\r\n', b'500 forbidden\r\n')):
            client = mock.Mock(greeting=b'200 ready\r\n', pending=b'')
            client.sock.recv.side_effect = [data, b'']
            wire = Wire(client)
            self.assertEqual(wire.fail_handshake(b'GROUP surface.test'), expected)
        client = mock.Mock(greeting=b'200 ready\r\n', pending=b'')
        client.sock.recv.side_effect = TimeoutError('no handshake termination')
        with self.assertRaises(TimeoutError):
            Wire(client).fail_handshake(b'GROUP surface.test')

    def test_manifest_cadence_and_unserved_surface(self):
        from fn2.tests import surface
        self.assertEqual(surface.FAMILIES['tls_auth']['forms']['S']['model'],
                         'fn2.tests.model.nntp_model')
        for box, count in [('laptop', 5), ('hbox', 50)]:
            with mock.patch.dict(surface.RUN, box=box):
                settings = surface.live_model_settings('tls_auth')
                self.assertEqual(settings.max_examples, count)
                self.assertEqual(settings.stateful_step_count, 30)
        with mock.patch.dict('os.environ', FN2_SURFACE_TARGET='fn2'):
            suite = surface.form_suite('tls_auth', 'S')
            self.assertEqual(suite.countTestCases(), 1)
            result = unittest.TestResult()
            suite.run(result)
            self.assertEqual(len(result.skipped), 1)
            self.assertIn(surface.SKIP, result.skipped[0][1])

    def test_live_wire_delegates_compressed_commands_and_eof(self):
        import zlib
        from tests.native_harness import Client
        encoder = zlib.compressobj(wbits=-15)
        encoded = encoder.compress(b'211 1 1 1 surface.test\r\n') + encoder.flush(zlib.Z_SYNC_FLUSH)
        client = Client.__new__(Client)
        client.greeting, client.buffer, client.offset = b'200 ready\r\n', bytearray(encoded), 0
        client.sock = mock.Mock()
        client.sock.recv.return_value = b''
        wire = Wire(client)
        wire.establish_compression()
        self.assertEqual(wire.command(b'GROUP surface.test'), b'211 1 1 1 surface.test\r\n')
        decoder = zlib.decompressobj(-15)
        sent = client.sock.sendall.call_args.args[0]
        self.assertEqual(decoder.decompress(sent), b'GROUP surface.test\r\n')
        with self.assertRaises(EOFError):
            wire.line()


if __name__ == '__main__':
    unittest.main()

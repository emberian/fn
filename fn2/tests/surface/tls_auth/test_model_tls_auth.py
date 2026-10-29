"""HU: live TLS/auth sequences over the existing NNTP oracle.

Design note for Astra: Target starts immediately, so this subclass provisions
its Node before starting it. Transport transitions are explicit and happen only
after check/update; Client.starttls() would complete TLS before checking 382.
No second authentication oracle or unrecorded fn1 exemptions live here.

SASL proof/password outcomes and fresh invitation completion remain abstract in
NntpModel (SPEC-MAP E5 and XREDEEM). SCRAM uses the carried independent RFC client
and checks server signatures. PLUS needs an exporter unavailable in Python 3.11
ssl and stays in the carried native; this machine exercises SCRAM-SHA-256.
"""
from contextlib import ExitStack
from dataclasses import dataclass
import base64
import re
import select
import unittest
import uuid

from fn2.tests.model.nntp_model import NntpModel
from fn2.tests.surface import SurfaceCase, Target, live_model_settings, serving

GROUP = 'surface.test'
IDENT = '<hu-cursor@surface.invalid>'
# Only GROUP/STAT observe this stored fixture, not its injection projection.
ARTICLE = (b'From: hu@surface.invalid\r\nNewsgroups: surface.test\r\n'
           b'Subject: HU cursor\r\nMessage-ID: ' + IDENT.encode() +
           b'\r\nDate: Thu, 29 Oct 2026 12:00:00 +0000\r\n\r\nHU\r\n')


class Wire:
    def __init__(self, client):
        self.client = self.io = client
        self.greeting = client.greeting

    def command(self, command):
        return self.io.command(command)

    def line(self):
        return self.io.line()

    def establish_tls(self):
        from tests.native_harness import client_context
        if self.client.pending:
            raise AssertionError('octets followed 382 before ClientHello')
        # A bounded observation, not a proof about all handshake schedules.
        if select.select([self.client.sock], [], [], 0.02)[0]:
            raise AssertionError('server emitted bytes before ClientHello')
        self.client.sock = client_context().wrap_socket(
            self.client.sock, server_hostname=self.client.server_hostname)

    def fail_handshake(self, command):
        """Send NNTP-looking bytes where TLS records are owed, on a throwaway.

        As in the carried STARTTLS native: failure may close/reset or send one
        fatal TLS alert. A timeout is not closure; plaintext is model evidence.
        """
        received = self.client.pending
        self.client.send(command + b'\r\n')
        while True:
            try:
                piece = self.client.sock.recv(1024)
            except ConnectionResetError:
                break  # Allowed malformed-TLS failure, never an NNTP EOF.
            if not piece:
                break
            received += piece
            if len(received) > 7:
                return received
        if received and (len(received) != 7 or received[0:2] != b'\x15\x03'
                         or received[2] not in (1, 2, 3, 4)
                         or received[3:6] != b'\x00\x02\x02'):
            return received
        # Return actual transport bytes separately from the absent NNTP reply.
        self.handshake_failure_bytes = received
        return b''

    def establish_compression(self):
        from tests.test_native_compress import Compressed
        self.io = Compressed(self.client)

    def close(self):
        self.client.close(quit=False)


class TlsAuthTarget(Target):
    """Only public operator verbs and native Client; one fresh Node per example."""
    def __init__(self, case, accounts, policy):
        from tests.native_harness import Node, native_image
        self.case = case
        self.node = Node(case, native_image('FN_NATIVE_HOST'))
        self.node.init(GROUP)
        self.node.use_tls(protected_only=False)
        auth = self.node.root / 'hu-credentials.toml'
        self.node.write_config(extra=(
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n'
            '\n[auth]\nrequired = {}\nprotected_only = {}\npath = "{}"\n').format(
                self.node.tls_port, self.node.cert, self.node.root / 'key.pem',
                str(policy['required']).lower(), str(policy['protected_only']).lower(), auth))
        for login, account in accounts.items():
            secret = account['password'].encode()
            self.node.operator('principal', 'set-password', login,
                *(['--posting'] if account['posting'] else []),
                input=secret + b'\n' + secret + b'\n', expect=0, timeout=30)
        # Isolate the per-session three-failure rule from the separate address
        # budget. This is a public fixture policy, not a server-default claim.
        self.node.operator('policy', 'set', 'exposure-trusted', '127.0.0.1/32',
                           expect=0, timeout=20)
        self.node.start()
        # `store post` is a developer-image selector; the production image takes
        # the operator's live post (as tests/test_native_moderation_outcome.py).
        self.node.post(IDENT, ARTICLE, group=GROUP, expect=0, timeout=30)

    def connect(self, implicit=False):
        from tests.native_harness import Client, client_context
        client = Client(self.node.tls_port if implicit else self.node.port,
                        implicit_tls=client_context() if implicit else None,
                        timeout=5, greeting=None)
        wire = Wire(client)
        self.case.addCleanup(wire.close)
        return wire

    def invite(self):
        result = self.node.operator('account', 'invite', '--expires', '3600',
                                    expect=0, timeout=20)
        codes = re.findall(rb'^[0-9a-f]{32}$', result.stdout, re.M)
        self.case.assertEqual(len(codes), 1, result.stdout + result.stderr)
        return codes[0].decode()


@dataclass
class Session:
    conn: object
    wire: object


def machine(case, target_factory=TlsAuthTarget, traces=None):
    from hypothesis import strategies as st
    from hypothesis.stateful import Bundle, RuleBasedStateMachine, initialize, rule

    class TlsAuthMachine(RuleBasedStateMachine):
        connections = Bundle('connections')

        def __init__(self):
            super().__init__()
            self.cleanup, self.sessions, self.trace = ExitStack(), [], []
            self.serial, self.used_codes = 0, []
            self.resources = unittest.TestCase()
            self.resources.addCleanup = self.cleanup.callback

        @initialize(target=connections, required=st.booleans(), protected=st.booleans(),
                    mode=st.sampled_from(['plain', 'starttls', 'implicit']))
        def setup(self, required, protected, mode):
            # Fresh test literals, never credentials from the environment.
            self.accounts = {name: {'password': 'hu-' + uuid.uuid4().hex, 'posting': posting}  # FAKE-SECRET
                             for name, posting in [('hu-reader', False), ('hu-poster', True)]}
            self.policy = dict(required=required, protected_only=protected, posting=True)
            try:
                self.target = target_factory(self.resources, self.accounts, self.policy)
                self.model = NntpModel({GROUP: {}}, [(IDENT, ARTICLE, [GROUP])],
                                       self.accounts, self.policy)
                # Mandatory witnesses: each live example reaches the third
                # failure for PASS and SASL, independently of generated choices.
                for sasl in (False, True):
                    self.fail_three(sasl)
                self.witnesses()
                return self.open(mode)
            except BaseException:
                self.cleanup.close()
                raise

        def handshake_witness(self):
            # No subsequent commands use this failed transport. Its model stays
            # handshaking (E1 has only a success receipt); at most this one extra
            # model connection per example is outside the four live Bundles.
            conn = self.model.connect(tls=False, implicit_tls=False)
            wire = self.target.connect(False)
            try:
                self.check(conn.greeting(), wire.greeting)
                expected = conn.send(b'STARTTLS\r\n')
                status = wire.command(b'STARTTLS')
                self.check(expected, status, command=b'STARTTLS')
                case.assertTrue(conn.handshaking, 'fixture did not enter TLS handshake')
                command = b'GROUP surface.test'
                expected = conn.send(command + b'\r\n')
                framed = wire.fail_handshake(command)
                self.check(expected, framed, command=command)
                self.trace[-1]['handshake_transport'] = wire.handshake_failure_bytes.hex()
            finally:
                wire.close()

        def witnesses(self):
            """Reach the layering and credential transitions in every example.

            Generated Bundle rules then interleave these operations across
            connections. Fixed witnesses are in addition to the 30 rule steps.
            """
            self.handshake_witness()
            plain = self.open('plain')
            self.compress(plain)  # 480 even when authentication is not required
            self.password(plain, 'right')  # PASS-before-USER / protected-only
            self.step(plain, b'AUTHINFO SASL PLAIN')  # always 483 before TLS
            self.user(plain, 'hu-reader')
            self.step(plain, b'GROUP surface.test', observe=False)
            self.starttls(plain)  # clears cached USER and a selectable cursor
            self.password(plain, 'right')  # cached USER did not cross STARTTLS
            self.starttls(plain)  # twice => 502
            self.login(plain, 'unknown', False)
            self.login(plain, 'hu-reader', False)
            self.login(plain, 'hu-poster', True)
            self.starttls(plain)  # after auth => 502, reading still works
            self.redeem(plain, 'fresh')  # after auth => 502
            self.compress(plain)
            self.quit(plain)

            # A cleartext success gives the after-auth STARTTLS branch with
            # TLS itself still inactive when this profile allows USER/PASS.
            clear = self.open('plain')
            self.login(clear, 'hu-poster', True)
            self.starttls(clear)
            self.compress(clear)
            self.quit(clear)

            protected = self.open('implicit')
            self.redeem(protected, 'pass-first')
            self.redeem(protected, 'fresh')
            self.redeem(protected, 'used')
            self.redeem(protected, 'wrong')
            self.quit(protected)
            unprotected = self.open('plain')
            self.redeem(unprotected, 'wrong')  # 483 under protected-only
            self.quit(unprotected)

            for scram in (False, True):
                protected = self.open('implicit')
                if scram:
                    self.scram(protected, good=True, cancel=True)
                    self.scram(protected, good=False, cancel=False)
                    self.scram(protected, good=True, cancel=False)
                else:
                    self.plain(protected, good=True, cancel=True, initial=False)
                    self.plain(protected, good=False, cancel=False, initial=True)
                    self.plain(protected, good=True, cancel=False, initial=False)
                self.quit(protected)

        def check(self, expected, status, body=None, *, eof=False, command=b'greeting'):
            verdict = expected.check(status, body, eof=eof)
            self.trace.append(dict(command=command.hex(), status=status.hex(),
                                   body=None if body is None else body.hex(), eof=eof,
                                   rule=verdict.rule, detail=verdict.detail))
            case.assertTrue(verdict.ok,
                f'{command!r}: {verdict.rule} ({verdict.spec}): {verdict.detail}; {status!r}')
            expected.update(status, body, eof=eof)

        def step(self, session, command, *, observe=True):
            if isinstance(command, str):
                command = command.encode()
            conn, wire = session.conn, session.wire
            if conn.quit:
                return None
            expected = conn.send(command + b'\r\n')
            status, body = wire.command(command), None
            closing_failure = (status.startswith(b'481') and conn.failed_auth_count == 2
                               and command != b'*')
            if closing_failure:
                status += wire.line()
            eof = closing_failure or command == b'QUIT'
            if eof:
                try:
                    extra = wire.line()
                except EOFError:
                    pass
                except TimeoutError as exc:
                    self.trace.append(dict(command=command.hex(), status=status.hex(),
                                           eof=False, error='mandatory EOF timeout'))
                    raise AssertionError('mandatory EOF not observed') from exc
                else:
                    self.trace.append(dict(command=command.hex(), status=status.hex(),
                                           eof=False, extra=extra.hex()))
                    case.fail(f'mandatory EOF not observed; extra reply {extra!r}')
            if expected.multiline_for(status):
                rows = []
                while True:
                    row = wire.line()
                    rows.append(row)
                    if row == b'.\r\n':
                        break
                body = b''.join(rows)
            self.check(expected, status, body, eof=eof, command=command)
            if status.startswith(b'382'):
                # The model remains handshaking until the actual TLS receipt.
                wire.establish_tls()
                conn.tls_established()
                # Observe reset BEFORE GROUP could overwrite the evidence.
                self.step(session, b'STAT', observe=False)
            elif command == b'COMPRESS DEFLATE' and status.startswith(b'206'):
                wire.establish_compression()
            if eof:
                wire.close()
            if observe and not conn.quit and not conn.sasl:
                self.step(session, b'GROUP surface.test', observe=False)
            return status

        def open(self, mode):
            # Bound simultaneous fixture sockets without limiting the sequence.
            live = [s for s in self.sessions if not s.conn.quit]
            if len(live) >= 4:
                self.step(live[0], b'QUIT')
                live[0].wire.close()
            implicit = mode == 'implicit'
            conn = self.model.connect(tls=False, implicit_tls=implicit)
            wire = self.target.connect(implicit)
            session = Session(conn, wire)
            self.sessions.append(session)
            self.check(conn.greeting(), wire.greeting)
            if mode == 'starttls':
                self.step(session, b'GROUP surface.test', observe=False)
                self.step(session, b'STARTTLS')
            return session

        @rule(target=connections, mode=st.sampled_from(['plain', 'starttls', 'implicit']))
        def connect(self, mode):
            return self.open(mode)

        @rule(session=connections, login=st.sampled_from(['hu-reader', 'hu-poster', 'unknown']))
        def user(self, session, login):
            self.step(session, 'AUTHINFO USER ' + login)

        @rule(session=connections, password=st.sampled_from(['right', 'wrong']))
        def password(self, session, password):
            login = session.conn.username or 'hu-reader'
            secret = self.accounts.get(login, {}).get('password', 'unknown-password')
            self.step(session, 'AUTHINFO PASS ' + (secret if password == 'right' else 'wrong'))

        @rule(session=connections, login=st.sampled_from(['hu-reader', 'hu-poster', 'unknown']),
              good=st.booleans())
        def login(self, session, login, good):
            secret = self.accounts.get(login, {}).get('password', 'unknown-password')
            self.step(session, 'AUTHINFO USER ' + login)
            self.step(session, 'AUTHINFO PASS ' + (secret if good else 'wrong'))

        @rule(session=connections, good=st.booleans(), cancel=st.booleans(), initial=st.booleans())
        def plain(self, session, good, cancel, initial):
            c = session.conn
            if c.quit or not c.tls:
                return
            secret = self.accounts['hu-reader']['password'] if good else 'wrong'
            token = base64.b64encode(b'\0hu-reader\0' + secret.encode())
            if initial and not cancel:
                self.step(session, b'AUTHINFO SASL PLAIN ' + token)
            else:
                status = self.step(session, b'AUTHINFO SASL PLAIN')
                if status.startswith(b'383'):
                    self.step(session, b'*' if cancel else token)

        @rule(session=connections, good=st.booleans(), cancel=st.booleans())
        def scram(self, session, good, cancel):
            from tests.sasl_client import ScramSha256, b64, status_data
            c = session.conn
            if c.quit:
                return
            secret = self.accounts['hu-poster']['password'] if good else 'wrong'
            client = ScramSha256('hu-poster', secret)
            first = self.step(session, 'AUTHINFO SASL SCRAM-SHA-256 ' + b64(client.client_first()))
            if first.startswith(b'383'):
                if cancel:
                    self.step(session, b'*')
                else:
                    final = self.step(session, b64(client.client_final(status_data(first)[1])))
                    if final.startswith(b'283'):
                        case.assertTrue(client.server_final_ok(status_data(final)[1]),
                                        'SCRAM server signature does not match')

        @rule(session=connections)
        def starttls(self, session):
            self.step(session, b'STARTTLS')

        @rule(session=connections)
        def compress(self, session):
            status = self.step(session, b'COMPRESS DEFLATE')
            if status and status.startswith((b'206', b'502')):
                self.step(session, b'STARTTLS')
                self.step(session, b'AUTHINFO USER hu-reader')

        @rule(session=connections, kind=st.sampled_from(['fresh', 'used', 'wrong', 'pass-first']))
        def redeem(self, session, kind):
            if session.conn.quit:
                return
            self.serial += 1
            name = 'hu-invited-' + str(self.serial)
            if kind == 'pass-first':
                self.step(session, b'XREDEEM PASS hu-invitation-password')
                return
            if kind == 'fresh':
                code = self.target.invite()
            elif kind == 'used' and self.used_codes:
                code = self.used_codes[0]
            else:
                code = '0' * 32
            self.step(session, f'XREDEEM {code} {name}')
            status = self.step(session, b'XREDEEM PASS hu-invitation-password')
            if status.startswith(b'281'):
                self.used_codes.append(code)
                # Current connection still has its original credential pin;
                # the fresh one can authenticate the newly created account.
                self.step(session, 'AUTHINFO USER ' + name)
                self.step(session, b'AUTHINFO PASS hu-invitation-password')
                fresh = self.open('implicit')
                self.step(fresh, 'AUTHINFO USER ' + name)
                self.step(fresh, b'AUTHINFO PASS hu-invitation-password')
                self.step(fresh, b'QUIT')

        @rule(sasl=st.booleans())
        def fail_three(self, sasl):
            session = self.open('implicit')
            for _ in range(3):
                if sasl:
                    self.plain(session, good=False, cancel=False, initial=True)
                else:
                    self.login(session, 'hu-reader', good=False)
            case.assertTrue(session.conn.quit, 'three failures did not close the model session')
            session.wire.close()

        @rule(session=connections)
        def quit(self, session):
            self.step(session, b'QUIT')

        def teardown(self):
            try:
                if traces is not None:
                    traces.append(self.trace)
            finally:
                self.cleanup.close()

    return TlsAuthMachine


class TestSurface(SurfaceCase):
    family, form = 'tls_auth', 'S'

    @serving('tls_auth')
    def test_live_state_machine(self):
        from hypothesis.stateful import run_state_machine_as_test
        traces = self.evidence['traces'] = []
        run_state_machine_as_test(machine(self, traces=traces),
                                  settings=live_model_settings('tls_auth'))

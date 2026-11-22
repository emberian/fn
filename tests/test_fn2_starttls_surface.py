#!/usr/bin/env python3
"""Real fn2 STARTTLS and owner-provisioned peer role checks.

Requires the composed native image, including configured TLS admission/timers.
No test passes by inspecting CLI request construction or the standalone C shim.
"""
import argparse
import os
from pathlib import Path
import secrets
import socket
import ssl
import stat
import subprocess
import time

from test_fn2_user_surface import FN, LiveNode, ROOT, run_fn


class Peer:
    def __init__(self, port):
        self.sock = socket.create_connection(('127.0.0.1', port), timeout=5)
        self.sock.settimeout(5)
        self.tls = None
        self.pending = b''
        assert self.line().startswith(b'200 ')

    def close(self):
        self.sock.close()

    def line(self):
        while b'\r\n' not in self.pending:
            if self.tls:
                try:
                    data = self.tls.read(4096)
                except ssl.SSLWantReadError:
                    self.flush()
                    data = self.sock.recv(4096)
                    assert data, 'EOF during encrypted response'
                    self.incoming.write(data)
                    continue
            else:
                data = self.sock.recv(4096)
            assert data, 'EOF during response'
            self.pending += data
        line, self.pending = self.pending.split(b'\r\n', 1)
        return line

    def flush(self):
        while self.outgoing.pending:
            self.sock.sendall(self.outgoing.read())

    def command(self, command):
        data = command + b'\r\n'
        if self.tls:
            assert self.tls.write(data) == len(data)
            self.flush()
        else:
            self.sock.sendall(data)
        return self.line()

    def capabilities(self):
        assert self.command(b'CAPABILITIES').startswith(b'101 ')
        result = []
        while (line := self.line()) != b'.':
            result.append(line)
        return result

    def upgrade(self, cert, pipeline, trailing=b''):
        context = ssl.create_default_context(cafile=str(cert))
        self.incoming, self.outgoing = ssl.MemoryBIO(), ssl.MemoryBIO()
        tls = context.wrap_bio(self.incoming, self.outgoing, server_hostname='localhost')
        try:
            tls.do_handshake()
        except ssl.SSLWantReadError:
            pass
        hello = self.outgoing.read()
        assert hello
        self.sock.sendall(b'STARTTLS\r\n' + (hello if pipeline else b''))
        assert self.line().startswith(b'382 ')
        # The plaintext reader may already have received server TLS bytes.
        if self.pending:
            self.incoming.write(self.pending)
            self.pending = b''
        if not pipeline:
            self.sock.sendall(hello)
        for _ in range(1000):
            try:
                tls.do_handshake()
                # Final handshake flight and application records share one
                # transport write, exceeding the deliberately small BIO.
                if trailing:
                    assert tls.write(trailing) == len(trailing)
                self.flush()
                self.tls = tls
                return
            except ssl.SSLWantReadError:
                self.flush()
                data = self.sock.recv(4096)
                assert data, 'EOF during handshake'
                self.incoming.write(data)
        raise AssertionError('handshake did not finish within bounded exchanges')


def exercise_peer_replay(peer, grant):
    old = b"<replay@example.invalid>"
    fresh = b"<fresh@example.invalid>"

    def article(mid, body):
        return b"\r\n".join([
            b"Path: peer!not-for-mail", b"From: peer@example.invalid",
            b"Subject: peer replay", b"Date: Fri, 30 Oct 2026 12:00:00 +0000",
            b"Newsgroups: local.test", b"Message-ID: " + mid, b"", body, b".",
        ])

    def transfer(mid, body):
        return peer.command(b"TAKETHIS " + mid + b"\r\n" + article(mid, body))

    assert peer.command(b"CHECK " + old) == b"238 " + old
    assert transfer(old, b"original body") == b"239 " + old
    assert transfer(old, b"original body") == b"439 " + old
    assert transfer(old, b"conflicting body") == b"439 " + old
    assert peer.command(b"CHECK " + old) == b"438 " + old
    assert peer.command(b"IHAVE " + old) == b"435 duplicate"
    assert peer.command(b"GROUP local.test") == b"211 1 1 1 local.test"
    assert peer.command(b"BODY 1") == b"222 1 " + old + b" body follows"
    assert [peer.line(), peer.line()] == [b"original body", b"."]
    assert transfer(fresh, b"conflicting body") == b"239 " + fresh
    assert peer.command(b"GROUP local.test") == b"211 2 1 2 local.test"

    ihave = b"<ihave@example.invalid>"
    assert peer.command(b"IHAVE " + ihave).startswith(b"335 ")
    assert peer.command(article(ihave, b"IHAVE body")).startswith(b"235 ")
    rejected = b"<mismatch@example.invalid>"
    assert peer.command(b"IHAVE " + rejected).startswith(b"335 ")
    assert peer.command(article(b"<different@example.invalid>", b"mismatched body")).startswith(b"437 ")
    assert peer.command(b"GROUP local.test") == b"211 3 1 3 local.test"

    # Recheck the destination at transfer after a successful offer.
    pending = b"<stream-policy@example.invalid>"
    assert peer.command(b"CHECK " + pending) == b"238 " + pending
    assert grant("set", "peer-accept", "local.test", "--revoke")["outcome"] == "accepted"
    assert transfer(pending, b"stream policy") == b"439 " + pending
    assert peer.command(b"GROUP local.test") == b"211 3 1 3 local.test"
    assert peer.command(b"CHECK " + pending) == b"238 " + pending
    assert grant("set", "peer-accept", "local.test")["outcome"] == "accepted"
    assert transfer(pending, b"stream policy") == b"239 " + pending
    assert peer.command(b"GROUP local.test") == b"211 4 1 4 local.test"


def exercise_peer_provision(port, cert, control_socket):
    control = ("--control-sock", str(control_socket))
    principal = "test-peer"
    password = secrets.token_hex(24).encode("ascii")
    assert run_fn("principal", "create", principal, *control, as_json=True)["outcome"] == "accepted"
    result = subprocess.run(
        [FN, "principal", "set-password", principal, *control],
        input=password + b"\n" + password + b"\n",
        cwd=ROOT, capture_output=True, timeout=15,
    )
    assert result.returncode == 0, result.stdout

    def grant(action, right, *extra, expect_rc=0):
        return run_fn("grant", action, principal, right, *extra, *control, as_json=True, expect_rc=expect_rc)

    rights = ("peer-feed", "peer-accept", "read", "append")
    scoped = [grant("set", right, "local.test") for right in rights]
    for right, written in zip(rights, scoped):
        found = grant("get", right, "local.test")
        assert found["found"] and found["enabled"] and found["grant"] == written["grant"], found
    assert len({written["grant"] for written in scoped}) == len(scoped)
    assert not grant("get", "peer")["found"]
    denied = grant("set", "peer", "--as", principal, expect_rc=1)
    assert denied["outcome"] == "refused" and denied["reason"] == "access", denied

    def login(peer):
        peer.upgrade(cert, False)
        assert peer.command(b"AUTHINFO USER " + principal.encode("ascii")).startswith(b"381 ")
        assert peer.command(b"AUTHINFO PASS " + password).startswith(b"281 ")

    plaintext = Peer(port)
    try:
        assert plaintext.command(b"MODE STREAM").startswith(b"501 ")
        for verb in (b"CHECK", b"IHAVE", b"TAKETHIS"):
            assert plaintext.command(verb + b" <ungranted@example.invalid>").startswith(b"502 ")
    finally:
        plaintext.close()

    ordinary = Peer(port)
    try:
        login(ordinary)
        assert ordinary.command(b"MODE STREAM").startswith(b"501 ")
        written = grant("set", "peer")
        found = grant("get", "peer")
        assert found["found"] and found["enabled"] and found["grant"] == written["grant"], found
        # The admission role is fixed at authentication. A grant on the
        # control connection cannot add a role to an already open session.
        assert ordinary.command(b"MODE STREAM").startswith(b"501 ")
    finally:
        ordinary.close()

    promoted = Peer(port)
    try:
        login(promoted)
        assert promoted.command(b"MODE STREAM").startswith(b"203 ")
        exercise_peer_replay(promoted, grant)
        revoked = grant("set", "peer", "--revoke")
        found = grant("get", "peer")
        assert found["found"] and not found["enabled"] and found["grant"] == revoked["grant"], found
        assert promoted.command(b"MODE STREAM").startswith(b"501 ")
    finally:
        promoted.close()

    after_revoke = Peer(port)
    try:
        login(after_revoke)
        assert after_revoke.command(b"MODE STREAM").startswith(b"501 ")
        assert grant("set", "peer")["outcome"] == "accepted"
        assert after_revoke.command(b"MODE STREAM").startswith(b"501 ")
    finally:
        after_revoke.close()

    after_regrant = Peer(port)
    try:
        login(after_regrant)
        assert after_regrant.command(b"MODE STREAM").startswith(b"203 ")
    finally:
        after_regrant.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path)
    args = parser.parse_args()
    directory = (args.directory or ROOT / 'build' / f'starttls-{time.time_ns()}').resolve()
    directory.mkdir(parents=True, exist_ok=False)
    cert, key = directory / 'cert.pem', directory / 'key.pem'
    subprocess.run(['openssl', 'req', '-x509', '-newkey', 'ec', '-pkeyopt',
                    'ec_paramgen_curve:prime256v1', '-nodes', '-days', '1',
                    '-subj', '/CN=localhost', '-addext', 'subjectAltName=DNS:localhost',
                    '-keyout', str(key), '-out', str(cert)],
                   check=True, capture_output=True, timeout=15)
    image = directory / 'node.img'
    run_fn('init', str(image), '--size-mb', '8', '--group', 'local.test')
    control_socket = Path(f"/tmp/fn2-pr-{os.getpid()}-{time.time_ns()}.sock")
    node = LiveNode(directory, image, 'tls', [
        '--host', '127.0.0.1', '--port', '0', '--peering', '--control-sock', str(control_socket),
        '--tls-certificate', str(cert),
        '--tls-key', str(key), '--tls-window', '512', '--tls-handshakes', '1', '--tls-handshake-ms', '1000'])
    try:
        port = int(node.wait_marker(b'LISTENING ').split()[1])
        assert node.wait_marker(b"LISTENING-LOCAL ") == f"LISTENING-LOCAL {control_socket}".encode()
        assert stat.S_IMODE(control_socket.stat().st_mode) == 0o600
        grant = run_fn("grant", "set", "anonymous", "read", "local.test",
                       "--control-sock", str(control_socket), as_json=True)
        assert grant["outcome"] == "accepted", grant
        for pipeline in (False, True):
            peer = Peer(port)
            try:
                assert b'STARTTLS' in peer.capabilities()
                assert peer.command(b'GROUP local.test').startswith(b'211 ')
                trailing = (b'GROUP local.test\r\n' * 100) if pipeline else b''
                peer.upgrade(cert, pipeline, trailing)
                for _ in range(100 if pipeline else 0):
                    assert peer.line().startswith(b'211 '), 'buffered ciphertext must survive RX reuse'
                assert b'STARTTLS' not in peer.capabilities()
                assert peer.command(b'STARTTLS').startswith(b'502 ')
                if not pipeline:
                    assert peer.command(b'ARTICLE').startswith(b'412 '), 'TLS must reset group selection'
                assert peer.command(b'GROUP local.test').startswith(b'211 ')
            finally:
                peer.close()
        stalled = Peer(port)
        other = Peer(port)
        try:
            assert stalled.command(b'STARTTLS').startswith(b'382 ')
            assert other.command(b'STARTTLS').startswith(b'580 '), 'admission must refuse exhausted token'
            assert stalled.sock.recv(1) == b'', 'deadline must close stalled handshake'
            other.upgrade(cert, True)
            assert other.command(b'GROUP local.test').startswith(b'211 '), 'expired token must be reusable'
        finally:
            stalled.close()
            other.close()
        exercise_peer_provision(port, cert, control_socket)
    finally:
        node.close()
        for path in (control_socket, Path(f"{control_socket}.groups")):
            path.unlink(missing_ok=True)
    print('PASS STARTTLS and owner-provisioned peer login, grant isolation, and revocation')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

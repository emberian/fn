#!/usr/bin/env python3
"""Real fn2 socket STARTTLS controls; local ephemeral credentials only.

Requires the composed native image, including configured TLS admission/timers.
No test passes by inspecting CLI request construction or the standalone C shim.
"""
import argparse
from pathlib import Path
import socket
import ssl
import subprocess
import time

from test_fn2_user_surface import LiveNode, ROOT, run_fn


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
    node = LiveNode(directory, image, 'tls', [
        '--host', '127.0.0.1', '--port', '0', '--tls-certificate', str(cert),
        '--tls-key', str(key), '--tls-window', '512', '--tls-handshakes', '1', '--tls-handshake-ms', '1000'])
    try:
        port = int(node.wait_marker(b'LISTENING ').split()[1])
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
    finally:
        node.close()
    print('PASS real STARTTLS socket: verified certificate, pipelined input, reset, budget and timeout reuse')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

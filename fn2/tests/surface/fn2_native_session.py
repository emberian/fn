"""A5r's socket session for the surface harness (layer doc fn2/docs/a-pool-host-sim.md 4.1.4).

FN2_SURFACE_SIM_NNTP=fn2.tests.surface.fn2_native_session:session

The same open / send / close / stop as fn2_sim_session.py, over a real TCP connection to the served
core under the native adapter (fn2/host/adapter.lisp) on 127.0.0.1. One node per example. The only
addition to the wire is a control line on the node's stdin: `sync PORT SENT EOF`, answered
`@@FN2SS quiet OUT CLOSED CAP:NONCE@@` at quiescence for that connection; the client then reads its
socket to OUT octets (and EOF when CLOSED), draining it concurrently all along. stop() returns WIRE's
verdict per connection over the clients' own transcripts, and ENVELOPE's over the boundary trace.
"""
import os
import pty
import re
import select
import socket
import subprocess

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))
MARK = re.compile(rb'@@FN2SS (\S+) (\S+) (\S+) (\S+)@@')


class Client:
    def __init__(self, sock, ident):
        self.sock, self.port, self.ident = sock, sock.getsockname()[1], ident
        self.sent, self.received, self.closed = bytearray(), bytearray(), False
        self.incarnation = None   # (index, nonce): the node's capability, bound at open

    def drain(self):
        while not self.closed:
            try:
                data = self.sock.recv(65536)
            except BlockingIOError:
                return
            except ConnectionResetError:
                self.closed = True
                self.sock.close()
                return
            if not data:
                # The node closed: release the descriptor at once (a client
                # the harness never closes must not hold an fd).
                self.closed = True
                self.sock.close()
                return
            self.received += data


def _ready(fds, timeout):
    """poll(2) readiness (no FD_SETSIZE ceiling, unlike select)."""
    p = select.poll()
    for fd in fds:
        p.register(fd, select.POLLIN | select.POLLHUP | select.POLLERR)
    return [fd for fd, _ in p.poll(timeout * 1000)]


class Fn2NativeSession:
    def __init__(self, log=None):
        self.log = open(log, 'wb') if log else None
        master, slave = pty.openpty()
        self.proc = subprocess.Popen([os.path.join(ROOT, 'tools', 'acl2')], cwd=ROOT,
                                     stdin=subprocess.PIPE, stdout=slave, stderr=slave)
        os.close(slave)
        self.out = master
        self.pending = b''
        self.clients = {}
        self._write('(ld "fn2/tests/native-session.lsp" :ld-error-action :error)')
        self._wait('books')
        self._write(':q')
        self._write('(load "fn2/host/native-session-raw.lisp")')
        self._write('(fn2-ns-serve)')
        tag, a, _, _ = self._wait('ready')
        self.port = int(a)

    def _write(self, text):
        self.proc.stdin.write(text.encode() + b'\n')
        self.proc.stdin.flush()

    def _wait(self, want, drain=None):
        """Read the pty to the next marker, draining DRAIN's socket meanwhile."""
        while True:
            m = MARK.search(self.pending)
            if m:
                line_end = self.pending.find(b'\n', m.end())
                self.pending = self.pending[m.end():]
                tag, a, b, c = (x.decode() for x in m.groups())
                if tag != want:
                    raise RuntimeError(f'native session: expected {want}, got {tag} {a} {b} {c}')
                return tag, a, b, c
            sockfd = drain.sock.fileno() if drain and not drain.closed else -1
            ready = _ready([self.out] + ([sockfd] if sockfd >= 0 else []), 120)
            if not ready:
                raise RuntimeError(f'native session: no {want} within 120 s')
            if sockfd >= 0 and sockfd in ready:
                drain.drain()
            if self.out in ready:
                try:
                    chunk = os.read(self.out, 65536)
                except OSError:
                    chunk = b''
                if not chunk:
                    raise RuntimeError('the native session ended unexpectedly')
                if self.log:
                    self.log.write(chunk); self.log.flush()
                if b'HARD ACL2 ERROR' in chunk or b'ACL2 Error' in chunk or b'debugger invoked' in chunk:
                    raise RuntimeError('the native session failed: ' + chunk.decode('latin-1')[-800:])
                self.pending += chunk

    def _sync(self, c, eof, opening=False):
        # A client port is reused over a long session; the node binds it to one
        # capability incarnation at the open, and every later sync means that one.
        self._write(f'open {c.port}' if opening else f'sync {c.port} {len(c.sent)} {1 if eof else 0}')
        _, out, closed, cap = self._wait('quiet', drain=c)
        out, closed = int(out), closed == '1'
        index, nonce = (int(x) for x in cap.split(':'))
        if c.incarnation is None:
            c.incarnation = (index, nonce)
        elif c.incarnation != (index, nonce):
            raise RuntimeError(f'native session: port {c.port} answered for {index}:{nonce}, bound to {c.incarnation}')
        while (len(c.received) < out or (closed and not c.closed)) and not c.closed:
            _ready([c.sock.fileno()], 5)
            c.drain()
        if len(c.received) < out:
            raise RuntimeError(f'native session: port {c.port} read {len(c.received)} of {out}')

    def open(self, peer=False):
        if peer:
            raise NotImplementedError('peer connections arrive with E4 (layer D section 11)')
        sock = socket.create_connection(('127.0.0.1', self.port))
        sock.setblocking(False)
        c = Client(sock, len(self.clients) + 1)
        self.clients[c.ident] = c
        self._sync(c, False, opening=True)
        return c.ident, bytes(c.received)

    def send(self, ident, octets, chunks=None):
        c = self.clients[ident]
        before = len(c.received)
        octets, chunks = bytes(octets), list(chunks or [])
        while octets and not c.closed:
            k = min(chunks.pop(0), len(octets)) if chunks and chunks[0] > 0 else len(octets)
            piece, octets = octets[:k], octets[k:]
            try:
                c.sock.setblocking(True)
                c.sock.sendall(piece)
            except (BrokenPipeError, ConnectionResetError):
                break
            finally:
                c.sock.setblocking(False)
            c.sent += piece
            self._sync(c, False)
        return bytes(c.received[before:]), c.closed

    def close(self, ident):
        c = self.clients[ident]
        before = len(c.received)
        c.drain()
        if c.closed:
            return b''
        if not c.closed:
            try:
                c.sock.shutdown(socket.SHUT_WR)
            except OSError:
                pass
        self._sync(c, True)
        # One session spans every example: release the client's descriptor now
        # (its transcript stays for stop()'s verdicts).
        c.drain()
        if c.sock.fileno() >= 0:
            c.sock.close()
        c.closed = True
        return bytes(c.received[before:])

    def stop(self):
        """WIRE's verdict per connection (ENVELOPE's refusal is every one's), then the process ends."""
        self._write('stop')
        self._wait('served')
        views = ' '.join(f"(({c.incarnation[0]} . {c.incarnation[1]}) ({' '.join(map(str, c.sent))}) "
                         f"({' '.join(map(str, c.received))}) {'t' if c.closed else 'nil'} {c.port} {c.ident})"
                         for c in self.clients.values())
        self._write(f"(fn2-ns-verdicts '({views}))")
        verdicts = {}
        while True:
            m = re.search(rb'@@FN2SS wire (\S+) (.*?)@@', self.pending)
            if m:
                verdicts[int(m.group(1))] = 'ok' if m.group(2).strip() == b':PASS' else m.group(2).decode()
                self.pending = self.pending[m.end():]
                continue
            if b'@@FN2SS stopped' in self.pending:
                break
            ready = _ready([self.out], 300)
            if not ready:
                raise RuntimeError('native session: no verdicts within 300 s')
            chunk = os.read(self.out, 65536)
            if not chunk:
                raise RuntimeError('the native session ended before its verdicts')
            if self.log:
                self.log.write(chunk); self.log.flush()
            self.pending += chunk
        for c in self.clients.values():
            if c.sock.fileno() >= 0:
                c.sock.close()
        self._write('(sb-ext:exit :code 0)')
        self.proc.wait(timeout=60)
        if self.log:
            self.log.close()
        return verdicts


def session(case=None, family='nntp', out='build/surface'):
    """The hook: one native node per example."""
    os.makedirs(os.path.join(ROOT, out), exist_ok=True)
    name = (case.id() if case is not None else 'session').replace('/', '_')[-120:]
    return Fn2NativeSession(log=os.path.join(ROOT, out, f'native-{name}.log'))

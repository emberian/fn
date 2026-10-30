"""Layer D's simulator session for the surface harness (sim_target.py's hook).

FN2_SURFACE_SIM_NNTP=fn2.tests.surface.fn2_sim_session:session

A long-lived ACL2 process (fn2/tests/sim-session.lsp) holds the served fn2 core, its listener
admitting fn2-conn, and the simulator's network; each call is one top-level ACL2 form and each
answer one marker line `@@FN2SS <tag> <hex|-> <closed> <id>@@`. Every call is deterministic given
the seed: FN2_SIM_SEED if set, else a CRC of the case id. The ACL2 books it includes must be
certified in the tree (fn2/tools/certify.sh tests/conn-unit.lisp sim/echo.lisp sim/check-wire.lisp).
"""
import os
import pty
import re
import subprocess
import zlib

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))
MARK = re.compile(rb'@@FN2SS (\S+) (\S+) (\S+) (\S+)@@')


class Fn2SimSession:
    def __init__(self, seed, log=None):
        self.log = open(log, 'wb') if log else None
        # SBCL block-buffers a pipe; a pseudo-terminal makes each answer line arrive when printed.
        master, slave = pty.openpty()
        self.proc = subprocess.Popen([os.path.join(ROOT, 'tools', 'acl2')], cwd=ROOT,
                                     stdin=subprocess.PIPE, stdout=slave, stderr=slave)
        os.close(slave)
        self.out = os.fdopen(master, 'rb', buffering=0)
        self._form('(ld "fn2/tests/sim-session.lsp" :ld-error-action :error)', 'ready')
        self._form(f'(fn2-ss-start {int(seed)} fn2-core fn2-sim fn2-own state)', 'started')

    def _line(self):
        buf = bytearray()
        while True:
            try:
                ch = self.out.read(1)
            except OSError:  # the pseudo-terminal closed with the process
                ch = b''
            if not ch:
                return bytes(buf)
            buf += ch
            if ch == b'\n':
                return bytes(buf)

    def _read(self):
        while True:
            line = self._line()
            if not line:
                raise RuntimeError('the simulator session ended unexpectedly')
            if self.log:
                self.log.write(line); self.log.flush()
            if b'HARD ACL2 ERROR' in line or b'ACL2 Error' in line:
                raise RuntimeError('the simulator session failed: ' + line.decode('latin-1').strip())
            m = MARK.search(line)
            if m:
                tag, hexs, closed, ident = (x.decode() for x in m.groups())
                return tag, (b'' if hexs == '-' else bytes.fromhex(hexs)), closed == '1', ident

    def _form(self, text, want):
        self.proc.stdin.write(text.encode() + b'\n')
        self.proc.stdin.flush()
        tag, octets, closed, ident = self._read()
        if tag != want:
            raise RuntimeError(f'simulator session: expected {want}, got {tag} {ident}')
        return octets, closed, ident

    def open(self, peer=False):
        if peer:
            raise NotImplementedError('peer connections arrive with E4 (layer D section 11)')
        octets, closed, ident = self._form('(fn2-ss-open fn2-core fn2-sim fn2-own state)', 'open')
        return int(ident), octets

    def send(self, ident, octets, chunks=None):
        olist = ' '.join(str(b) for b in octets)
        clist = ' '.join(str(int(c)) for c in (chunks or []))
        octets, closed, _ = self._form(
            f"(fn2-ss-send {int(ident)} '({olist}) '({clist}) fn2-core fn2-sim fn2-own state)", 'reply')
        return octets, closed

    def close(self, ident):
        octets, _, _ = self._form(f'(fn2-ss-close {int(ident)} fn2-core fn2-sim fn2-own state)', 'closed')
        return octets

    def stop(self):
        """WIRE's verdict per connection ('ok' or the failure), then the process ends."""
        self.proc.stdin.write(b'(fn2-ss-stop fn2-core state)\n')
        self.proc.stdin.flush()
        verdicts = {}
        while True:
            line = self._line()
            if not line:
                raise RuntimeError('the simulator session ended before stop')
            if self.log:
                self.log.write(line); self.log.flush()
            for m in re.finditer(rb'@@FN2SS wire (\S+) (.*?)@@', line):
                ident, verdict = m.group(1).decode(), m.group(2).decode().strip()
                verdicts[int(ident)] = 'ok' if verdict == ':PASS' else verdict
            if b'@@FN2SS stopped' in line:
                break
        self.proc.stdin.write(b'(good-bye)\n')
        self.proc.stdin.flush()
        self.proc.wait(timeout=60)
        if self.log:
            self.log.close()
        return verdicts


def session(case=None, family='nntp', out='build/surface'):
    """The hook: one simulated node per example."""
    seed = os.environ.get('FN2_SIM_SEED')
    if seed is None:
        seed = zlib.crc32((case.id() if case is not None else 'fn2').encode()) % 1000003 + 1
    os.makedirs(os.path.join(ROOT, out), exist_ok=True)
    name = (case.id() if case is not None else 'session').replace('/', '_')[-120:]
    return Fn2SimSession(seed, log=os.path.join(ROOT, out, f'sim-{name}.log'))

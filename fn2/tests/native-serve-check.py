"""A5r: the served core on a configured listener, driven the way fn1's Node backend drives a node.

    python3 fn2/tests/native-serve-check.py      (from the repo root; the books certified)

Picks a free port, starts `tools/acl2 < fn2/tests/native-serve.lsp` with FN2_LISTENER_PORT set in a
new session, writes that session leader's PID to build/native-serve-check.pid, waits for `LISTENING
<port>`, reads the greeting, sends CAPABILITIES and QUIT, then SIGTERM to that session's process group
(tools/acl2 is a wrapper whose child is SBCL; a signal to the wrapper alone never reaches the node)
and expects `STOPPED`, ENVELOPE's legality verdict :PASS, and exit 0, and that
nothing listens on the port afterwards. On any failure the group is stopped the same way. A port out of range must be refused: `REFUSED listener-port`, exit 2.
The same node also binds FN2_LISTENER_PATH (build/native-serve-check.sock): the socket file is mode 0600, a
connection on it is the listener's (the reader greeting, QUIT), and the file is gone after the stop. A
relative path must be refused: `REFUSED listener-path`, exit 2.
"""
import os
import signal
import socket
import subprocess
import sys
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))


PIDFILE = os.path.join(ROOT, 'build', 'native-serve-check{}.pid')


def start(env, tag=''):
    script = open(os.path.join(ROOT, 'fn2', 'tests', 'native-serve.lsp'), 'rb')
    proc = subprocess.Popen([os.path.join(ROOT, 'tools', 'acl2')], cwd=ROOT, stdin=script,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            env=dict(os.environ, **env), start_new_session=True)
    os.makedirs(os.path.dirname(PIDFILE), exist_ok=True)
    with open(PIDFILE.format(tag), 'w') as f:
        f.write(f'{proc.pid}\n')       # the session leader: its group is the node
    return proc


def stop_group(proc, sig=signal.SIGTERM):
    """Signal the node's whole group by the leader recorded in PIDFILE (never by pattern)."""
    if proc.poll() is None:
        try:
            os.killpg(proc.pid, sig)
        except ProcessLookupError:
            pass


def wait_line(proc, prefix, seconds=300):
    deadline = time.monotonic() + seconds
    seen = []
    while time.monotonic() < deadline:
        line = proc.stdout.readline()
        if not line:
            break
        seen.append(line)
        if line.startswith(prefix):
            return line, seen
    raise SystemExit(f'no {prefix!r}; last output: {b"".join(seen[-20:])!r}')


def main():
    # A SIGTERM (e.g. from timeout) must still run the finally clauses that stop the nodes.
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    probe = socket.socket()
    probe.bind(('127.0.0.1', 0))
    port = probe.getsockname()[1]
    probe.close()
    path = os.path.join(ROOT, 'build', 'native-serve-check.sock')
    if os.path.exists(path):
        raise SystemExit(f'{path} exists (a previous run\'s node is live, or its stop failed): not removed')
    proc = start({'FN2_LISTENER_PORT': str(port), 'FN2_LISTENER_PATH': path, 'FN2_ENVELOPE_TRACE': '200000'})
    ok = False
    try:
        line, _ = wait_line(proc, b'LISTENING ')
        assert line == f'LISTENING {port}\n'.encode(), line
        line, _ = wait_line(proc, b'LISTENING-LOCAL ')
        assert line == f'LISTENING-LOCAL {path}\n'.encode(), line
        mode = os.stat(path).st_mode & 0o777
        assert mode == 0o600, oct(mode)
        u = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        u.settimeout(30)
        u.connect(path)
        uf = u.makefile('rb')
        greeting = uf.readline()
        assert greeting.startswith(b'201 '), greeting
        u.sendall(b'QUIT\r\n')
        assert uf.readline().startswith(b'205 ')
        assert uf.read() == b''
        u.close()
        c = socket.create_connection(('127.0.0.1', port), timeout=30)
        f = c.makefile('rb')
        greeting = f.readline()
        assert greeting.startswith(b'201 '), greeting
        c.sendall(b'CAPABILITIES\r\n')
        assert f.readline().startswith(b'101 ')
        while f.readline() != b'.\r\n':
            pass
        c.sendall(b'QUIT\r\n')
        assert f.readline().startswith(b'205 ')
        assert f.read() == b''
        c.close()
        stop_group(proc)
        stopped, _ = wait_line(proc, b'STOPPED ')
        envelope, _ = wait_line(proc, b'ENVELOPE ')
        assert envelope.strip() == b'ENVELOPE :PASS', envelope
        assert proc.wait(timeout=60) == 0
        assert not os.path.exists(path), f'{path} left after the stop'
        ok = True
    finally:
        if not ok:
            stop_group(proc, signal.SIGKILL)
    refused = start({'FN2_LISTENER_PORT': '70000'}, '-refused')
    try:
        line, _ = wait_line(refused, b'REFUSED ')
        assert line.strip() == b'REFUSED listener-port', line
        assert refused.wait(timeout=60) == 2
    finally:
        stop_group(refused, signal.SIGKILL)
    refused = start({'FN2_LISTENER_PATH': 'native-serve-check.sock'}, '-refused-path')
    try:
        line, _ = wait_line(refused, b'REFUSED ')
        assert line.strip() == b'REFUSED listener-path', line
        assert refused.wait(timeout=60) == 2
    finally:
        stop_group(refused, signal.SIGKILL)
    # Control: the check's stop ended the node: nothing listens on the port any more.
    try:
        socket.create_connection(('127.0.0.1', port), timeout=5).close()
        raise SystemExit(f'port {port} still accepts after the stop')
    except ConnectionRefusedError:
        pass
    print(f'NATIVE SERVE PASS port={port} {stopped.decode().strip()} {envelope.decode().strip()}; '
          f'port 70000 refused; unix {path} 0600 served and removed; relative path refused')


if __name__ == '__main__':
    sys.exit(main())

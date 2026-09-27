"""tools/wire_stream.py: a client stream's write sends every octet.

The defect (lane input-loop, 2026-09-27): `sock.makefile("rwb",
buffering=0).write(data)` is one `send`; on a socket with a timeout it
returns the count the kernel took, and the large-POST clients ignored it,
so a multi-MiB article arrived as a prefix and the owner waited forever.
"""

from pathlib import Path
import re
import socket
import threading
import time
import unittest

from tools.wire_stream import whole_stream

ROOT = Path(__file__).resolve().parent.parent
LARGE = 8 * 1024 * 1024


class Drain(threading.Thread):
    """Accept one connection, wait DELAY seconds (so the client's send
    buffer fills), then read to EOF."""

    def __init__(self, listener, delay):
        super().__init__(daemon=True)
        self.listener, self.delay, self.received = listener, delay, 0

    def run(self):
        conn, _ = self.listener.accept()
        with conn:
            time.sleep(self.delay)
            while True:
                chunk = conn.recv(1 << 16)
                if not chunk:
                    return
                self.received += len(chunk)


def pair(delay):
    listener = socket.create_server(("127.0.0.1", 0))
    drain = Drain(listener, delay)
    drain.start()
    client = socket.create_connection(listener.getsockname(), timeout=30)
    client.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 64 * 1024)
    return listener, drain, client


class WholeStreamTests(unittest.TestCase):
    def test_large_write_arrives_whole(self):
        listener, drain, client = pair(0.3)
        data = bytes(range(256)) * (LARGE // 256)
        with listener, client:
            stream = whole_stream(client)
            self.assertEqual(stream.write(data), LARGE)
            self.assertEqual(stream.write(memoryview(b".\r\n")), 3)
            stream.close()
            client.shutdown(socket.SHUT_WR)
            drain.join(30)
        self.assertEqual(drain.received, LARGE + 3)

    def test_plain_makefile_write_is_partial(self):
        """The defect the helper replaces, reproduced: one write of 8 MiB on
        a timeout socket whose reader is not yet reading returns a count
        short of the length.  (Guards the test above against passing only
        because this platform never writes partially.)"""
        listener, drain, client = pair(0.3)
        with listener, client:
            raw = client.makefile("rwb", buffering=0)  # the defect, on purpose
            sent = raw.write(b"x" * LARGE)
            raw.close()
            client.shutdown(socket.SHUT_WR)
            drain.join(30)
        self.assertLess(sent, LARGE)
        self.assertEqual(drain.received, sent)

    def test_reads_are_unbuffered(self):
        a, b = socket.socketpair()
        with a, b:
            stream = whole_stream(a)
            b.sendall(b"200 one\r\n200 two\r\n")
            self.assertEqual(stream.readline(), b"200 one\r\n")
            # nothing past the first line was taken from the socket
            self.assertEqual(a.recv(64), b"200 two\r\n")

    def test_close_releases_socket_like_makefile(self):
        a, b = socket.socketpair()
        with b:
            stream = whole_stream(a)
            a.close()                      # deferred while the stream is open
            self.assertNotEqual(a.fileno(), -1)
            stream.close()
            self.assertEqual(a.fileno(), -1)


class NoPartialClientTests(unittest.TestCase):
    """No client in tools/ or tests/ builds the partial-write stream."""

    PARTIAL = re.compile(r'\.makefile\(\s*"[rb]*w[rb]*",\s*buffering=0\s*\)')

    def test_no_unbuffered_writable_makefile(self):
        offenders = []
        for path in sorted(list((ROOT / "tools").rglob("*.py")) + list((ROOT / "tests").rglob("*.py"))):
            if path.name in ("wire_stream.py", "test_wire_stream.py"):
                continue
            text = path.read_text(errors="replace")
            for match in self.PARTIAL.finditer(text):
                offenders.append("%s:%d" % (path.relative_to(ROOT), text.count("\n", 0, match.start()) + 1))
        self.assertEqual(offenders, [], "use tools.wire_stream.whole_stream (writes are sendall)")


if __name__ == "__main__":
    unittest.main()

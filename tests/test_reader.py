"""Socket transcripts for the experimental loopback-only ACL2 reader."""
import os
import select
import socket
import struct
import subprocess
import sys
import time
import unittest


ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GREETING = b"201 fn-nntp experimental reader ready\r\n"


class ReaderProcess:
    def __enter__(self):
        self.proc = subprocess.Popen(
            [sys.executable, "tools/run_reader.py", "--port", "0"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline:
            ready, _, _ = select.select([self.proc.stdout], [], [], 0.2)
            if ready:
                line = self.proc.stdout.readline()
                if line.startswith(b"LISTENING "):
                    self.port = int(line.split()[1])
                    return self
            if self.proc.poll() is not None:
                break
        stderr = self.proc.stderr.read().decode("utf-8", "replace")
        if self.proc.poll() is None:
            self.proc.terminate()
            self.proc.wait(timeout=3)
        raise RuntimeError("reader did not listen: " + stderr)

    def __exit__(self, *unused):
        self.proc.terminate()
        try:
            self.proc.wait(timeout=8)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=3)
        self.proc.stdout.close()
        self.proc.stderr.close()

    def connect(self):
        sock = socket.create_connection(("127.0.0.1", self.port), timeout=5)
        sock.settimeout(2)
        self.assert_bytes(sock, GREETING)
        return sock

    @staticmethod
    def assert_bytes(sock, expected):
        received = b""
        while len(received) < len(expected):
            chunk = sock.recv(len(expected) - len(received))
            if not chunk:
                break
            received += chunk
        if received != expected:
            raise AssertionError("expected {!r}, received {!r}".format(expected, received))


class ReaderSocketTests(unittest.TestCase):
    def setUp(self):
        self.reader = ReaderProcess().__enter__()

    def tearDown(self):
        self.reader.__exit__()

    def test_fragmented_and_coalesced_commands_follow_core_transcript(self):
        sock = self.reader.connect()
        self.addCleanup(sock.close)
        sock.sendall(b"GRO")
        sock.sendall(b"UP fn.letters\r\nSTAT\r\nCAPABILITIES\r\n")
        self.reader.assert_bytes(sock, b"211 1 1 1 fn.letters\r\n")
        self.reader.assert_bytes(sock, b"223 1 <reader@example.invalid> retrieved\r\n")
        self.reader.assert_bytes(
            sock,
            b"101 capability list follows\r\nVERSION 2\r\n"
            b"IMPLEMENTATION fn-nntp-lab\r\n.\r\n")

    def test_quit_replies_then_closes(self):
        sock = self.reader.connect()
        sock.sendall(b"QUIT\r\n")
        self.reader.assert_bytes(sock, b"205 closing connection\r\n")
        self.assertEqual(sock.recv(1), b"")
        sock.close()

    def test_malformed_and_overlimit_input_close(self):
        for payload in (b"STAT\n", b"A" * 513 + b"\r\n"):
            with self.subTest(payload=payload[:8]):
                sock = self.reader.connect()
                sock.sendall(payload)
                self.reader.assert_bytes(sock, b"501 syntax error\r\n")
                self.assertEqual(sock.recv(1), b"")
                sock.close()

    def test_sessions_do_not_leak_selected_group(self):
        first = self.reader.connect()
        first.sendall(b"GROUP fn.letters\r\n")
        self.reader.assert_bytes(first, b"211 1 1 1 fn.letters\r\n")
        first.close()

        second = self.reader.connect()
        self.addCleanup(second.close)
        second.sendall(b"STAT\r\n")
        self.reader.assert_bytes(second, b"412 no newsgroup selected\r\n")

    def test_reset_client_does_not_end_listener(self):
        dropped = socket.create_connection(("127.0.0.1", self.reader.port), timeout=5)
        dropped.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER,
                           struct.pack("ii", 1, 0))
        dropped.close()
        time.sleep(0.1)

        healthy = self.reader.connect()
        self.addCleanup(healthy.close)
        healthy.sendall(b"STAT\r\n")
        self.reader.assert_bytes(healthy, b"412 no newsgroup selected\r\n")


if __name__ == "__main__":
    unittest.main()

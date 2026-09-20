"""The mutable service owner: two readers, a post between them, a stall, a kill."""
import os
import select
import signal
import socket
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# RFC 3977 section 5.1.1: the owner allows posting, so its greeting is 200.
GREETING = b"200 fn-nntp experimental server ready\r\n"


class OwnerProcess:
    def __init__(self, store, control, max_connections=4, tls=None):
        self.store = store
        self.control = control
        self.max_connections = max_connections
        self.tls = tls
        self.proc = None

    def start(self):
        extra = []
        if self.tls is not None:
            extra = ["--tls-cert", str(self.tls[0]), "--tls-key", str(self.tls[1])]
        self.proc = subprocess.Popen(
            [sys.executable, "tools/run_owner.py", "--store", str(self.store),
             "--port", "0", "--control", str(self.control),
             "--max-connections", str(self.max_connections)] + extra,
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        # Recovery loads the owner books and replays the history; on a
        # co-tenant-loaded box that ACL2 startup runs minutes, not seconds.
        deadline = time.monotonic() + 300
        seen = 0
        # Read the raw descriptor: a BufferedReader.readline() after select
        # slurps both banner lines into its buffer on one read, the next
        # select then never fires, and the second line is never seen.
        fd = self.proc.stdout.fileno()
        pending = b""
        while time.monotonic() < deadline:
            ready, _, _ = select.select([fd], [], [], 0.2)
            if ready:
                chunk = os.read(fd, 4096)
                if not chunk:
                    break
                pending += chunk
                while b"\n" in pending:
                    line, pending = pending.split(b"\n", 1)
                    if line.startswith(b"LISTENING "):
                        self.port = int(line.split()[1])
                        seen += 1
                    elif line.startswith(b"CONTROL "):
                        seen += 1
                    if seen == 2:
                        return self
            if self.proc.poll() is not None:
                break
        # Stop before reading stderr: reading a live process blocks.
        proc = self.proc
        self.proc = None
        if proc.poll() is None:
            proc.terminate()
        try:
            proc.wait(timeout=15)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait(timeout=5)
        error = proc.stderr.read().decode("utf-8", "replace")
        proc.stdout.close()
        proc.stderr.close()
        raise RuntimeError("owner did not start: " + error)

    def stderr(self):
        try:
            return self.proc.stderr.read().decode("utf-8", "replace")
        except (OSError, ValueError, AttributeError):
            return ""

    def stop(self):
        if self.proc is None:
            return
        if self.proc.poll() is None:
            self.proc.terminate()
        try:
            self.proc.wait(timeout=15)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=5)
        self.proc.stdout.close()
        self.proc.stderr.close()
        self.proc = None

    def kill(self):
        """The crash: no shutdown, no flush, the owner simply dies."""
        self.proc.kill()
        self.proc.wait(timeout=5)
        self.proc.stdout.close()
        self.proc.stderr.close()
        self.proc = None

    def connect(self):
        sock = socket.create_connection(("127.0.0.1", self.port), timeout=5)
        sock.settimeout(10)
        assert_bytes(sock, GREETING)
        return sock

    def control_line(self, line, payload=b""):
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
            sock.settimeout(60)
            sock.connect(str(self.control))
            sock.sendall(line + b"\n" + payload)
            reply = b""
            while not reply.endswith(b"\n"):
                chunk = sock.recv(4096)
                if not chunk:
                    break
                reply += chunk
            return reply.strip()

    def post(self, msgid, payload, groups=("fn.letters",)):
        line = "POST {} {} - {}".format(msgid, ",".join(groups), len(payload)).encode()
        return self.control_line(line, payload)


def assert_bytes(sock, expected):
    received = b""
    while len(received) < len(expected):
        chunk = sock.recv(len(expected) - len(received))
        if not chunk:
            break
        received += chunk
    if received != expected:
        raise AssertionError("expected {!r}, received {!r}".format(expected, received))


class OwnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-owner-")
        self.store = Path(self.temp.name) / "store"
        self.control = Path(self.temp.name) / "owner.sock"
        self.payload = Path(self.temp.name) / "article"
        self.store_command("init")
        self.owner = None

    def tearDown(self):
        if self.owner is not None:
            self.owner.stop()
        self.temp.cleanup()

    def store_command(self, command, *args, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(self.store), command,
             *map(str, args)], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode != expected:
            self.fail("store {} returned {}\nstdout={}\nstderr={}".format(
                command, result.returncode, result.stdout, result.stderr))
        return result

    def start_owner(self, **kwargs):
        self.owner = OwnerProcess(self.store, self.control, **kwargs).start()
        return self.owner

    def test_two_readers_keep_their_pins_across_a_post_until_advanced(self):
        owner = self.start_owner()
        first = owner.connect()
        self.addCleanup(first.close)
        self.assertTrue(owner.post("<one@example.invalid>",
                                   b"Message-ID: <one@example.invalid>\r\n\r\none\r\n")
                        .startswith(b"committed sequence=0 charge="))
        second = owner.connect()
        self.addCleanup(second.close)
        # The reader that opened before the post still sees an empty group;
        # the reader that opened after it sees the article.
        first.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(first, b"211 0 ")
        first.recv(64)
        second.sendall(b"GROUP fn.letters\r\nSTAT 1\r\n")
        assert_bytes(second, b"211 1 1 1 fn.letters\r\n")
        assert_bytes(second, b"223 1 <one@example.invalid> retrieved\r\n")
        # A second post while both readers are open; neither moves.
        self.assertTrue(owner.post("<two@example.invalid>",
                                   b"Message-ID: <two@example.invalid>\r\n\r\ntwo\r\n")
                        .startswith(b"committed sequence=1 charge="))
        self.assertEqual(owner.control_line(b"VERSION"), b"version 2")
        connections = owner.control_line(b"CONNECTIONS")
        self.assertIn(b":0", connections)
        self.assertIn(b":1", connections)
        second.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(second, b"211 1 1 1 fn.letters\r\n")
        # Advancing the first reader moves it to the newest version only.
        advanced = owner.control_line(b"ADVANCE ALL")
        self.assertTrue(advanced.startswith(b"advanced "))
        first.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(first, b"211 2 1 2 fn.letters\r\n")
        second.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(second, b"211 2 1 2 fn.letters\r\n")
        # The CLI without the owner is refused (the owner holds the writer lock);
        # through the owner it commits.
        self.payload.write_bytes(b"Message-ID: <cli@example.invalid>\r\n\r\ncli\r\n")
        blocked = self.store_command("post", "--message-id", "<cli@example.invalid>",
                                     "--payload", self.payload, "--group", "fn.letters",
                                     expected=1)
        self.assertIn(b"already locked", blocked.stderr)
        via_owner = self.store_command("post", "--owner", self.control,
                                       "--message-id", "<cli@example.invalid>",
                                       "--payload", self.payload, "--group", "fn.letters")
        self.assertIn(b"committed sequence=2", via_owner.stdout)
        duplicate = self.store_command("post", "--owner", self.control,
                                       "--message-id", "<cli@example.invalid>",
                                       "--payload", self.payload, "--group", "fn.letters")
        self.assertIn(b"duplicate", duplicate.stdout)

    def test_a_stalled_reader_does_not_block_a_post(self):
        owner = self.start_owner(max_connections=2)
        stalled = owner.connect()
        self.addCleanup(stalled.close)
        # The stalled reader sends a command and never reads its reply, then
        # sends nothing more; the owner must keep serving the post path.
        stalled.sendall(b"GROUP fn.letters\r\n")
        started = time.monotonic()
        self.assertTrue(owner.post("<stall@example.invalid>",
                                   b"Message-ID: <stall@example.invalid>\r\n\r\nstall\r\n")
                        .startswith(b"committed sequence=0 charge="))
        self.assertLess(time.monotonic() - started, 60)
        # The bound on connections is enforced by the owner: a third connection
        # (bound 2, one live reader plus one control-path-free slot) is closed
        # without a greeting once the bound is reached.
        second = owner.connect()
        self.addCleanup(second.close)
        third = socket.create_connection(("127.0.0.1", owner.port), timeout=5)
        third.settimeout(5)
        self.assertEqual(third.recv(1), b"")
        third.close()

    def test_a_killed_owner_reopens_with_every_completed_post_durable(self):
        owner = self.start_owner()
        for index in range(3):
            msgid = "<durable{}@example.invalid>".format(index)
            self.assertTrue(
                owner.post(msgid, "Message-ID: {}\r\n\r\n{}\r\n".format(msgid, index).encode())
                .startswith("committed sequence={} charge=".format(index).encode()))
        owner.kill()
        self.owner = None
        reopened = self.start_owner()
        self.assertEqual(reopened.control_line(b"VERSION"), b"version 3")
        reader = reopened.connect()
        self.addCleanup(reader.close)
        reader.sendall(b"GROUP fn.letters\r\nARTICLE 3\r\n")
        assert_bytes(reader, b"211 3 1 3 fn.letters\r\n")
        assert_bytes(reader, b"220 3 <durable2@example.invalid> article follows\r\n"
                     b"Message-ID: <durable2@example.invalid>\r\n\r\n2\r\n.\r\n")
        # The plain CLI sees the same three transactions after the owner exits.
        reopened.stop()
        self.owner = None
        status = self.store_command("status")
        self.assertIn(b"transactions=3 articles=3", status.stdout)

    def test_clock_and_group_facts_go_through_the_owner(self):
        owner = self.start_owner()
        self.assertEqual(owner.control_line(b"OBSERVE"), b"observed")
        self.assertEqual(owner.control_line(b"DECLARE-GROUP fn.new"), b"declared")
        self.assertEqual(owner.control_line(b"DECLARE-GROUP fn.new"), b"refused")


if __name__ == "__main__":
    unittest.main()


def self_signed(directory):
    """A throwaway certificate for the TLS listener test, or None."""
    cert = Path(directory) / "fn-test.pem"
    key = Path(directory) / "fn-test.key"
    result = subprocess.run(
        ["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes",
         "-keyout", str(key), "-out", str(cert), "-days", "1",
         "-subj", "/CN=localhost",
         "-addext", "subjectAltName=DNS:localhost,IP:127.0.0.1"],
        capture_output=True)
    if result.returncode != 0 or not cert.exists() or not key.exists():
        return None
    return cert, key


class OwnerTlsTests(unittest.TestCase):
    """RFC 4642 section 2.3's security layer is a HOST facility.

    This test exercises exactly that host facility and claims nothing about
    the model: the owner wraps the accepted socket with Python's `ssl`, and
    the same greeting and the same reply stream come back through it.  What
    the book proves about STARTTLS -- the capability label, 382, 502, 580,
    and the discarded state -- is in tests/acl2/nntp-auth-tests.lisp and is
    not what runs here.
    """

    def test_the_listener_serves_nntp_through_tls_with_a_self_signed_cert(self):
        import ssl
        with tempfile.TemporaryDirectory() as directory:
            material = self_signed(directory)
            if material is None:
                self.skipTest("openssl is not available to make a test certificate")
            cert, key = material
            store = Path(directory) / "store"
            control = Path(directory) / "control.sock"
            subprocess.run([sys.executable, "tools/run_store.py", "init",
                            "--store", str(store), "--group", "fn.letters"],
                           cwd=ROOT, check=True, capture_output=True)
            owner = OwnerProcess(store, control, tls=(cert, key)).start()
            try:
                context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
                context.load_verify_locations(cafile=str(cert))
                context.check_hostname = False
                with socket.create_connection(("127.0.0.1", owner.port), 30) as raw:
                    with context.wrap_socket(raw) as sock:
                        sock.settimeout(60)
                        self.assertEqual(sock.recv(len(GREETING)), GREETING)
                        sock.sendall(b"CAPABILITIES\r\n")
                        block = b""
                        while not block.endswith(b"\r\n.\r\n"):
                            chunk = sock.recv(4096)
                            if not chunk:
                                break
                            block += chunk
                        self.assertTrue(block.startswith(b"101 "), block[:64])
                        # RFC 4642 section 2.1: no STARTTLS label, because
                        # this connection already carries a TLS layer.  The
                        # owner does not yet pass that bit to the book, so
                        # the label is absent for the other reason -- no
                        # certificate is configured in the served session.
                        # Recorded in specs/nntp-audit.md.
                        self.assertNotIn(b"\r\nSTARTTLS\r\n", block)
                        sock.sendall(b"QUIT\r\n")
                        self.assertTrue(sock.recv(64).startswith(b"205 "))
            finally:
                owner.stop()

    def test_a_plaintext_client_cannot_speak_to_the_tls_listener(self):
        with tempfile.TemporaryDirectory() as directory:
            material = self_signed(directory)
            if material is None:
                self.skipTest("openssl is not available to make a test certificate")
            cert, key = material
            store = Path(directory) / "store"
            control = Path(directory) / "control.sock"
            subprocess.run([sys.executable, "tools/run_store.py", "init",
                            "--store", str(store), "--group", "fn.letters"],
                           cwd=ROOT, check=True, capture_output=True)
            owner = OwnerProcess(store, control, tls=(cert, key)).start()
            try:
                with socket.create_connection(("127.0.0.1", owner.port), 30) as sock:
                    sock.settimeout(30)
                    sock.sendall(b"CAPABILITIES\r\n")
                    # The handshake fails and the owner drops the connection
                    # before any NNTP octet: no greeting is ever sent.
                    self.assertEqual(sock.recv(64), b"")
            finally:
                owner.stop()

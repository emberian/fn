"""The mutable service owner: two readers, a post between them, a stall, a kill."""
import os
import select
import signal
import socket
import shutil
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
    def __init__(self, store, control, max_connections=4, tls=None, inject_fault=None):
        self.store = store
        self.control = control
        self.max_connections = max_connections
        self.tls = tls
        # TEST ONLY (tools/run_owner.py OWNER_FAULTS): one unexpected
        # exception at a named point in the serve loop, once.
        self.inject_fault = inject_fault
        self.proc = None

    def start(self):
        extra = []
        if self.inject_fault is not None:
            extra += ["--inject-fault", self.inject_fault]
        if self.tls is not None:
            # `--implicit-tls` is what these two tests mean by "the TLS
            # listener": NNTPS, the handshake before the greeting.  A
            # configured certificate WITHOUT it is now offered through RFC
            # 4642 STARTTLS instead (tests/test_auth.py covers that), so
            # the flag has to be explicit here.
            extra = ["--tls-cert", str(self.tls[0]), "--tls-key", str(self.tls[1]),
                     "--implicit-tls"]
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

    def stop_reading_stderr(self):
        """Stop the owner and answer what it wrote to stderr.

        `stop' closes the pipes, and reading them while the process is live
        blocks, so a test that needs to see how a fault was RECORDED -- as
        opposed to how it was answered on the wire -- ends the owner here.
        """
        if self.proc is None:
            return ""
        if self.proc.poll() is None:
            self.proc.terminate()
        try:
            self.proc.wait(timeout=15)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=5)
        text = self.proc.stderr.read().decode("utf-8", "replace")
        self.proc.stdout.close()
        self.proc.stderr.close()
        self.proc = None
        return text

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


def read_line(sock):
    """One CRLF-terminated status line."""
    data = b""
    while not data.endswith(b"\r\n"):
        chunk = sock.recv(1)
        if not chunk:
            break
        data += chunk
    return data.decode("ascii", "replace").strip()


def read_block(sock):
    """A multi-line block up to its terminating dot (RFC 3977 section 3.1.1)."""
    data = b""
    while not data.endswith(b"\r\n.\r\n"):
        chunk = sock.recv(4096)
        if not chunk:
            break
        data += chunk
    return [line for line in data.decode("ascii", "replace").split("\r\n")
            if line and line != "."]


class OwnerFixture(unittest.TestCase):
    """A store, an owner process and the store CLI: the fixture, no tests."""

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


class OwnerTests(OwnerFixture):
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

    def test_live_group_reconfiguration_is_durable_and_uses_a_pinned_client(self):
        owner = self.start_owner()
        first = owner.connect()
        second = owner.connect()
        self.addCleanup(first.close)
        self.addCleanup(second.close)
        # Both readers remain open.  The first client's pinned generation is
        # the ACL2 authorization for this event; no Python config table is
        # consulted.  The durable record is committed before fn-ocfg publishes
        # its next generation, and the other reader stays a separate pin.
        self.assertEqual(owner.control_line(b"CONNECTIONS"), b"connections 0:0 1:0")
        self.assertEqual(owner.control_line(b"RECONFIGURE 0 create fn.live"),
                         b"configured generation=2")
        self.assertEqual(owner.control_line(b"CONNECTIONS"), b"connections 0:0 1:0")
        owner.kill()
        self.owner = None
        reopened = self.start_owner()
        reader = reopened.connect()
        self.addCleanup(reader.close)
        # Recovery replays the durable configuration history into fn-ocfg.  A
        # second create is refused by the same ACL2 admissibility predicate;
        # it does not depend on a copied Python group table.
        self.assertEqual(reopened.control_line(b"RECONFIGURE 0 create fn.live"),
                         b"refused group-exists")


if __name__ == "__main__":
    unittest.main()


def self_signed(directory):
    """A throwaway certificate for the TLS listener test, or None."""
    cert = Path(directory) / "fn-test.pem"
    key = Path(directory) / "fn-test.key"
    if shutil.which("openssl") is None:
        return None
    result = subprocess.run(
        ["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes",
         "-keyout", str(key), "-out", str(cert), "-days", "1",
         "-subj", "/CN=localhost",
         "-addext", "subjectAltName=DNS:localhost,IP:127.0.0.1"],
        capture_output=True)
    if result.returncode != 0 or not cert.exists() or not key.exists():
        # openssl is installed and refused.  Until 2026-09-21 this returned
        # None here too and the test skipped saying "openssl is not
        # available", which was not the predicate: an openssl too old for
        # `-addext`, a full disk and a broken `req` all read as an absent
        # dependency.  A tool that is present and fails is a failure.
        raise RuntimeError(
            "openssl is installed and would not make a test certificate: {}"
            .format(result.stderr.decode("utf-8", "replace")[-500:]))
    return cert, key


class SubmissionCrashCutTests(OwnerFixture):
    """The intent protocol's five named process-death cuts use the real host."""

    def setUp(self):
        super().setUp()
        self.payload.write_bytes(
            b"From: seed@example.invalid\r\nSubject: seed\r\n"
            b"Newsgroups: fn.letters\r\nMessage-ID: <seed@example.invalid>\r\n"
            b"\r\nSeed.\r\n")
        self.store_command("post", "--message-id", "<seed@example.invalid>",
                           "--payload", str(self.payload), "--group", "fn.letters")
        reservation = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        reservation.bind(("127.0.0.1", 0))
        peer_port = reservation.getsockname()[1]
        reservation.close()
        self.store_command(
            "peer", "add", "cut-peer", "--path-identity",
            "cut-peer.example.invalid", "--nntp",
            "127.0.0.1:{}".format(peer_port), "--outbound-groups", "fn.*",
            "--source-address", "192.0.2.40")

    @staticmethod
    def article(msgid):
        return (b"From: cut@example.invalid\r\nSubject: cut\r\n"
                b"Newsgroups: fn.letters\r\nMessage-ID: " + msgid.encode() +
                b"\r\n\r\nCut.\r\n")

    def cut(self, point, code, msgid, payload=None):
        owner = self.start_owner(inject_fault=point)
        reply = owner.post(msgid, payload if payload is not None else self.article(msgid))
        self.assertEqual(reply, b"")
        self.assertEqual(owner.proc.wait(timeout=30), code)
        owner.stop()
        self.owner = None

    def recovered_version(self, expected):
        owner = self.start_owner()
        self.assertEqual(owner.control_line(b"VERSION"),
                         "version {}".format(expected).encode())
        owner.stop()
        self.owner = None

    def test_precommit_resolution_and_response_cuts_recover_without_loss(self):
        self.cut("preintent-cut", 90, "<preintent@example.invalid>")
        self.recovered_version(1)

        self.cut("intent-barrier-cut", 91, "<intent@example.invalid>")
        self.recovered_version(1)
        journal = self.store / "feed" / "cut-peer.fnfd"
        self.assertTrue(journal.is_file())
        self.assertGreater(journal.stat().st_size, 0)

        # Seed predates the peer, so this duplicate has a new target and
        # reaches a real durable abort record rather than the empty-target
        # duplicate fast path.
        self.cut("abort-barrier-cut", 93, "<seed@example.invalid>",
                 self.payload.read_bytes())
        self.recovered_version(1)

        self.cut("commit-barrier-cut", 92, "<commit@example.invalid>")
        self.recovered_version(2)

        self.cut("response-cut", 94, "<response@example.invalid>")
        self.recovered_version(3)

    def test_an_ambiguous_store_result_is_reported_then_fences_the_owner(self):
        owner = self.start_owner(inject_fault="store-uncertain")
        reply = owner.post("<uncertain@example.invalid>",
                           self.article("<uncertain@example.invalid>"))
        self.assertTrue(reply.startswith(b"uncertain:"), reply)
        self.assertEqual(owner.proc.wait(timeout=30), 3)
        owner.stop()
        self.owner = None

        # This process cut happened after link(2), so ordinary process-death
        # recovery finds the complete article and resolves the retained intent
        # as a commit. No second mutation occurred in the uncertain image.
        self.recovered_version(2)

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
                self.skipTest("openssl is not on PATH, so no test certificate can be made")
            cert, key = material
            store = Path(directory) / "store"
            control = Path(directory) / "control.sock"
            # `--store` is a GLOBAL argument and must precede the
            # subcommand; with it after, run_store exits 5 on a usage error
            # and both TLS tests errored in setUp rather than running.
            subprocess.run([sys.executable, "tools/run_store.py", "--store",
                            str(store), "init", "--group", "fn.letters"],
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
                self.skipTest("openssl is not on PATH, so no test certificate can be made")
            cert, key = material
            store = Path(directory) / "store"
            control = Path(directory) / "control.sock"
            # `--store` is a GLOBAL argument and must precede the
            # subcommand; with it after, run_store exits 5 on a usage error
            # and both TLS tests errored in setUp rather than running.
            subprocess.run([sys.executable, "tools/run_store.py", "--store",
                            str(store), "init", "--group", "fn.letters"],
                           cwd=ROOT, check=True, capture_output=True)
            owner = OwnerProcess(store, control, tls=(cert, key)).start()
            try:
                with socket.create_connection(("127.0.0.1", owner.port), 30) as sock:
                    sock.settimeout(30)
                    sock.sendall(b"CAPABILITIES\r\n")
                    # The handshake fails and the owner drops the
                    # connection before any NNTP octet: no greeting is ever
                    # sent.  The drop reaches the client as an orderly
                    # close or as a reset depending on whether the kernel
                    # still had unread data queued; both mean the same
                    # thing here and the assertion is about what was
                    # SERVED, which is nothing.
                    try:
                        served = sock.recv(64)
                    except ConnectionResetError:
                        served = b""
                    self.assertEqual(served, b"")
            finally:
                owner.stop()


# The reply books/owner-fault.lisp renders for a host fault.  It is asserted
# as octets, not parsed: nothing in tools/ writes a status line.
FAULT_LINE = (b"403 internal fault; this connection is closed "
              b"and the server continues\r\n")


class OwnerSurvivesAFaultTests(OwnerFixture):
    """One connection's host fault must not end the service (w11/owner-survival).

    Until 2026-09-21 an exception raised anywhere under `Owner.serve' unwound
    out of `main' and the owner process EXITED, so one peer's input ended the
    service for every connection.  tools/v0_matrix.py measured the cost of
    that on persvati: node B died inside `Owner.drain' on the first IHAVE,
    and 22 transit rows, 4 feed rows, 6 crash rows and 1 concurrency row of
    the 190-row matrix read `not-built' behind that single death.

    These two tests are the thing that had never been tested: a fault is
    injected on ONE connection and the OTHER connection is asserted to still
    be served.  The reply the faulted connection gets is ACL2's
    (`fn-own-fault', books/owner-fault.lisp), and it is the fourth outcome --
    distinct from 240, from both 441s and from the served 403 -- so it can
    never be read as an acceptance or as a refusal.
    """

    ARTICLE = (b"From: poster@example.invalid\r\nSubject: hello\r\n"
               b"Newsgroups: fn.letters\r\n\r\nHello, news.\r\n.\r\n")

    def setUp(self):
        # OwnerFixture's store, plus one article so a read-back has something
        # to be read back against.
        super().setUp()
        self.payload.write_bytes(b"Message-ID: <seed@example.invalid>\r\n"
                                 b"Subject: seed\r\n\r\nSeed body\r\n")
        self.store_command("post", "--message-id", "<seed@example.invalid>",
                           "--payload", str(self.payload), "--group", "fn.letters")

    @staticmethod
    def read_until_eof(sock):
        received = b""
        while True:
            chunk = sock.recv(4096)
            if not chunk:
                return received
            received += chunk

    def test_a_fault_in_a_served_read_costs_that_connection_and_nothing_else(self):
        owner = self.start_owner(inject_fault="served-read")
        faulting = owner.connect()
        self.addCleanup(faulting.close)
        surviving = owner.connect()
        self.addCleanup(surviving.close)
        # The first read raises; the connection is answered with ACL2's
        # fault line and closed, and the server does NOT exit.
        faulting.sendall(b"DATE\r\n")
        self.assertEqual(self.read_until_eof(faulting), FAULT_LINE)
        # THE POINT OF THE LANE: the other connection, open across the
        # fault, is served normally afterwards -- and it is served at the
        # pin it already had, so the fault did not disturb its state either.
        surviving.sendall(b"DATE\r\n")
        assert_bytes(surviving, b"111 ")
        surviving.recv(64)
        surviving.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(surviving, b"211 1 1 1 fn.letters\r\n")
        # A connection opened AFTER the fault is served too.
        later = owner.connect()
        self.addCleanup(later.close)
        later.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(later, b"211 1 1 1 fn.letters\r\n")
        # The control channel still answers, so the process is the same one.
        self.assertEqual(owner.control_line(b"VERSION"), b"version 1")
        # The fault is RECORDED distinctly: FAULT, naming the site, the
        # connection and the exception type -- never `refused', never
        # `uncertain', which are answers about an article.
        recorded = owner.stop_reading_stderr()
        self.owner = None
        self.assertIn("FAULT served-read cid=", recorded)
        self.assertIn("RuntimeError", recorded)

    def test_a_fault_carrying_a_submission_leaves_the_post_path_open(self):
        owner = self.start_owner(inject_fault="drain")
        poster = owner.connect()
        self.addCleanup(poster.close)
        reader = owner.connect()
        self.addCleanup(reader.close)
        # The poster's article reaches the writer step and the host faults
        # while carrying it: this is the exact shape of the crash the v0
        # matrix found, where `Owner.drain' raised and the process died.
        poster.sendall(b"POST\r\n")
        assert_bytes(poster, b"340 send article to be posted\r\n")
        poster.sendall(self.ARTICLE)
        self.assertEqual(self.read_until_eof(poster), FAULT_LINE)
        # The reader that was open across it is untouched.
        reader.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(reader, b"211 1 1 1 fn.letters\r\n")
        # THE WRITER IS NOT WEDGED.  `fn-own-take-submission' moves a
        # submission into the durable path only when nothing is in flight,
        # so a fault that left the faulted submission in flight would cost
        # EVERY connection the post path.  A second connection posts and
        # reaches 240 (fn-own-fault-clears-the-faulted-submission).
        second = owner.connect()
        self.addCleanup(second.close)
        second.sendall(b"POST\r\n")
        assert_bytes(second, b"340 send article to be posted\r\n")
        second.sendall(self.ARTICLE)
        assert_bytes(second, b"240 article received OK\r\n")
        # And the faulted article was NOT committed: the group holds the
        # seed and the second poster's article, and nothing else
        # (fn-own-fault-is-not-a-store-event).
        self.assertEqual(owner.control_line(b"VERSION"), b"version 2")
        second.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(second, b"211 2 1 2 fn.letters\r\n")
        recorded = owner.stop_reading_stderr()
        self.owner = None
        self.assertIn("FAULT drain cid=", recorded)


class ConnectionReleaseTests(OwnerFixture):
    """A connection the BOOK said closes must leave the owner's table.

    `fn-served-closingp` is true of the effects after QUIT's 205. The host
    used to set `conn.closing`, arm the socket for write and never drop it,
    so the socket stayed open and the entry stayed in `fn-own-conns` for
    the lifetime of the process. N QUITs cost N permanent slots; at
    `--max-connections` `fn-own-open` answers NIL and every later accept
    was closed with no greeting and no log line. That is what made a node
    refuse every connection for the 90 s of a gate deadline while `kill -0`
    said it was alive.
    """

    def test_a_quit_releases_the_owners_connection_slot(self):
        owner = self.start_owner(max_connections=2)
        # Three times the bound. Before the fix the third connect answered
        # with an immediate close and the table never shrank.
        for attempt in range(6):
            sock = owner.connect()
            sock.sendall(b"QUIT\r\n")
            self.assertTrue(read_line(sock).startswith("205"),
                            "QUIT {} was not answered 205".format(attempt))
            sock.close()
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline:
                if owner.control_line(b"CONNECTIONS") == b"connections":
                    break
                time.sleep(0.1)
            self.assertEqual(
                owner.control_line(b"CONNECTIONS"), b"connections",
                "the owner still held a connection after QUIT {}".format(attempt))

    def test_a_socket_closed_without_quit_also_releases_the_slot(self):
        """The control that isolates the defect to the `closing` path."""
        owner = self.start_owner(max_connections=2)
        for attempt in range(6):
            sock = owner.connect()
            sock.close()
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline:
                if owner.control_line(b"CONNECTIONS") == b"connections":
                    break
                time.sleep(0.1)
            self.assertEqual(
                owner.control_line(b"CONNECTIONS"), b"connections",
                "the owner still held a connection after close {}".format(attempt))

class TransitPortTests(OwnerFixture):
    """The role of an inbound connection is the peer table's, not the client's.

    specs/peering.md 1.1: a connection whose source address matches a
    configured record's `auth-source-address` row opens as transit
    (`fn-own-open-peer` -> `fn-served-open-peer`), and every other connection
    opens as a reader (`fn-own-open` -> `fn-served-open`).  The decision is
    ACL2's -- `fn-owner-peer-for-address` reads the record -- and the host
    only passes it the source address it got from the socket.

    Without this, node B answers every transit offer `502 transit is not
    permitted on this connection`, which is the model correctly answering a
    READER question, and no article can cross between two fn nodes in either
    direction.
    """

    def peer_record(self, name="b", address="127.0.0.1", port=119):
        """One `peer add`, the shape tools/twonode_gate.py writes."""
        self.store_command("peer", "add", name,
                           "--path-identity", "{}.gate.example.invalid".format(name),
                           "--nntp", "127.0.0.1:{}".format(port),
                           "--inbound-groups", "fn.*",
                           "--outbound-groups", "fn.*",
                           "--streaming",
                           "--source-address", address)

    def probe(self, owner, msgid="<transit-probe@example.invalid>"):
        """What this connection is told it may do, and what an offer draws."""
        sock = owner.connect()
        try:
            sock.sendall(b"CAPABILITIES\r\n")
            status = read_line(sock)
            capabilities = read_block(sock) if status.startswith("101") else []
            sock.sendall("IHAVE {}\r\n".format(msgid).encode())
            offer = read_line(sock)
        finally:
            sock.close()
        return capabilities, offer

    def test_a_reader_connection_is_refused_the_transit_commands(self):
        """The control: with no peer record, 127.0.0.1 is an ordinary client."""
        owner = self.start_owner()
        unused_capabilities, offer = self.probe(owner)
        self.assertTrue(offer.startswith("502"), offer)

    def test_a_connection_from_a_configured_peer_address_opens_as_transit(self):
        self.peer_record(address="127.0.0.1")
        owner = self.start_owner()
        unused_capabilities, offer = self.probe(owner)
        # 335 is "send it".  What this asserts is the accept decision: the
        # answer is no longer the reader's 502, so the session the book is
        # stepping is fn-served-open-peer's.  The transfer decision itself is
        # fn-peer-decide-transfer's and is not probed here.
        self.assertTrue(offer.startswith("335"), offer)

    def test_a_record_for_a_different_address_does_not_open_transit(self):
        """The tooth for the address: a peer table is not a blanket permit."""
        self.peer_record(address="10.99.99.99")
        owner = self.start_owner()
        unused_capabilities, offer = self.probe(owner)
        self.assertTrue(offer.startswith("502"), offer)

    def test_the_capability_block_names_the_effective_transit_commands(self):
        """RFC 3977 §5.2 names the transit commands this peer may use."""
        self.peer_record(address="127.0.0.1")
        owner = self.start_owner()
        capabilities, offer = self.probe(owner)
        self.assertTrue(offer.startswith("335"), offer)
        self.assertIn("IHAVE", capabilities)
        self.assertIn("STREAMING", capabilities)

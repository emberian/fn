"""AUTHINFO (RFC 4643) and STARTTLS (RFC 4642) against a live fn owner.

Narrow, and every assertion is about what the SERVER said, never about what
this file computed.  The verifier in the credential file is derived by ACL2
(`books/auth-secret.lisp` through `tools/auth_secret.py`); the digest is
never recomputed here, so a test that passed because Python and ACL2 agreed
on a wrong answer cannot exist.

The self-signed certificate is generated into the temporary directory by
`certificate()` and is never committed.
"""
import importlib.util
import os
import select
import socket
import ssl
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

GREETING_POSTING = b"200 fn-nntp experimental server ready\r\n"
GREETING_READER = b"201 fn-nntp experimental reader ready\r\n"


def nntplib_available():
    """`nntplib` was removed from the standard library in Python 3.13.

    The round trip against an independent client is evidence this lane
    wants, so when it is absent the test is SKIPPED and said to be skipped;
    it is never quietly replaced by fn talking to itself.
    """
    return importlib.util.find_spec("nntplib") is not None


def openssl_available():
    try:
        subprocess.run(["openssl", "version"], check=True, capture_output=True,
                       timeout=30)
    except (OSError, subprocess.SubprocessError):
        return False
    return True


def certificate(directory):
    """A self-signed certificate for 127.0.0.1, made here and never committed."""
    cert = Path(directory) / "tls.crt"
    key = Path(directory) / "tls.key"
    subprocess.run(
        ["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes",
         "-keyout", str(key), "-out", str(cert), "-days", "1",
         "-subj", "/CN=127.0.0.1",
         "-addext", "subjectAltName=IP:127.0.0.1"],
        check=True, capture_output=True, timeout=120)
    return cert, key


class Owner:
    """One `tools/run_owner.py`, started with an AUTHINFO policy."""

    def __init__(self, store, control, auth_file=None, required=False,
                 protected_only=False, tls=None):
        self.store = store
        self.control = control
        self.auth_file = auth_file
        self.required = required
        self.protected_only = protected_only
        self.tls = tls
        self.proc = None
        self.port = None

    def start(self):
        argv = [sys.executable, "tools/run_owner.py", "--store", str(self.store),
                "--port", "0", "--control", str(self.control),
                "--max-connections", "4"]
        if self.auth_file is not None:
            argv += ["--auth-file", str(self.auth_file)]
        if self.required:
            argv.append("--auth-required")
        if self.protected_only:
            argv.append("--auth-protected-only")
        if self.tls is not None:
            argv += ["--tls-cert", str(self.tls[0]), "--tls-key", str(self.tls[1])]
        self.proc = subprocess.Popen(argv, cwd=ROOT, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE)
        deadline = time.monotonic() + 600
        seen = 0
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
        error = self.drain_stderr()
        self.stop()
        raise RuntimeError("owner did not start: " + error)

    def drain_stderr(self):
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
            self.proc.wait(timeout=20)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=5)
        for stream in (self.proc.stdout, self.proc.stderr):
            try:
                stream.close()
            except (OSError, ValueError):
                pass
        self.proc = None


class Client:
    """A line client, so the transcript in the evidence file is the real one."""

    def __init__(self, port):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=30)
        self.sock.settimeout(30)
        self.buffer = b""
        self.transcript = []
        self.greeting = self.line()

    def line(self):
        while b"\r\n" not in self.buffer:
            chunk = self.sock.recv(4096)
            if not chunk:
                raise AssertionError("the server closed before a reply line")
            self.buffer += chunk
        line, self.buffer = self.buffer.split(b"\r\n", 1)
        self.transcript.append(b"S: " + line)
        return line + b"\r\n"

    def block(self):
        """A multi-line block, up to the lone dot."""
        lines = []
        while True:
            line = self.line()
            if line == b".\r\n":
                return lines
            lines.append(line)

    def send(self, text):
        self.transcript.append(b"C: " + text.encode("ascii"))
        self.sock.sendall(text.encode("ascii") + b"\r\n")

    def command(self, text):
        self.send(text)
        return self.line()

    def starttls(self):
        reply = self.command("STARTTLS")
        if not reply.startswith(b"382 "):
            return reply
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        context.check_hostname = False
        context.verify_mode = ssl.CERT_NONE
        self.sock = context.wrap_socket(self.sock, server_hostname="127.0.0.1")
        self.buffer = b""
        return reply

    def close(self):
        try:
            self.sock.close()
        except OSError:
            pass


class AuthTests(unittest.TestCase):
    """The reader path with a credential set by `fn principal set-password`."""

    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="fn-auth-")
        cls.root = Path(cls.temp.name)
        cls.store = cls.root / "store"
        cls.control = cls.root / "owner.sock"
        cls.auth = cls.root / "auth.toml"
        cls.config = cls.root / "fn.toml"
        run(["python3", "tools/run_store.py", "--store", str(cls.store),
             "init", "--group", "fn.letters"])
        cls.config.write_text(
            '[store]\npath = "{}"\n\n[auth]\npath = "{}"\n'
            .format(cls.store, cls.auth), encoding="utf-8")
        # The verifier is ACL2's; this is the only place a password is typed.
        run(["bin/fn", "--config", str(cls.config), "principal", "set-password",
             "alice", "--password", "correct-horse", "--posting"])
        run(["bin/fn", "--config", str(cls.config), "principal", "set-password",
             "reader", "--password", "read-only", "--no-posting"])

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def setUp(self):
        self.owner = None

    def tearDown(self):
        if self.owner is not None:
            self.owner.stop()

    def serve(self, **kwargs):
        self.owner = Owner(self.store, self.control, auth_file=self.auth,
                           **kwargs).start()
        return self.owner

    # -- the credential file ---------------------------------------------
    def test_set_password_writes_a_verifier_and_no_secret(self):
        text = self.auth.read_text(encoding="utf-8")
        self.assertIn("[login.\"alice\"]", text)
        self.assertIn("salt = ", text)
        self.assertIn("digest = ", text)
        self.assertNotIn("correct-horse", text)
        self.assertNotIn("secret = ", text)
        self.assertEqual(oct(self.auth.stat().st_mode & 0o777), "0o600")

    def test_a_cleartext_credential_file_is_refused_by_name(self):
        legacy = self.root / "legacy.toml"
        legacy.write_text('[login."bob"]\nprincipal = "{}"\n'
                          'secret = "hunter2"\nposting = true\n'.format("aa" * 32),
                          encoding="utf-8")
        config = self.root / "legacy-fn.toml"
        config.write_text('[store]\npath = "{}"\n\n[auth]\npath = "{}"\n'
                          .format(self.store, legacy), encoding="utf-8")
        result = subprocess.run(
            ["bin/fn", "--config", str(config), "principal", "set-password",
             "carol", "--password", "x"],
            cwd=ROOT, capture_output=True, timeout=600)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"cleartext-credential", result.stdout + result.stderr)

    # -- the served path --------------------------------------------------
    def test_login_and_wrong_password(self):
        owner = self.serve(required=True)
        client = Client(owner.port)
        self.addCleanup(client.close)
        # RFC 4643 section 2.3.2: PASS before USER is 482.
        self.assertTrue(client.command("AUTHINFO PASS correct-horse")
                        .startswith(b"482 "))
        # A wrong password is 481 and leaves the connection unauthenticated.
        self.assertTrue(client.command("AUTHINFO USER alice").startswith(b"381 "))
        self.assertTrue(client.command("AUTHINFO PASS wrong").startswith(b"481 "))
        self.assertTrue(client.command("GROUP fn.letters").startswith(b"480 "))
        # The right password is 281 and the gate opens.
        self.assertTrue(client.command("AUTHINFO USER alice").startswith(b"381 "))
        self.assertTrue(client.command("AUTHINFO PASS correct-horse")
                        .startswith(b"281 "))
        self.assertTrue(client.command("GROUP fn.letters").startswith(b"211 "))
        self.transcript = client.transcript

    def test_post_before_and_after_login_under_required(self):
        owner = self.serve(required=True)
        client = Client(owner.port)
        self.addCleanup(client.close)
        self.assertTrue(client.command("POST").startswith(b"480 "))
        client.command("AUTHINFO USER alice")
        self.assertTrue(client.command("AUTHINFO PASS correct-horse")
                        .startswith(b"281 "))
        self.assertTrue(client.command("POST").startswith(b"340 "))

    def test_posting_follows_the_credential_flag(self):
        owner = self.serve(required=True)
        client = Client(owner.port)
        self.addCleanup(client.close)
        client.command("AUTHINFO USER reader")
        self.assertTrue(client.command("AUTHINFO PASS read-only")
                        .startswith(b"281 "))
        # Authenticated, gate passed, and still refused: the credential was
        # enrolled without the posting flag (RFC 3977 section 6.3.1.1).
        self.assertTrue(client.command("POST").startswith(b"440 "))
        # And the capability block does not promise what it will refuse.
        self.assertTrue(client.command("CAPABILITIES").startswith(b"101 "))
        labels = [line.strip() for line in client.block()]
        self.assertNotIn(b"POST", labels)

    def test_protected_only_refuses_authinfo_before_tls(self):
        owner = self.serve(required=True, protected_only=True)
        client = Client(owner.port)
        self.addCleanup(client.close)
        self.assertTrue(client.command("AUTHINFO USER alice").startswith(b"483 "))
        # And the capability block does not offer AUTHINFO it would refuse.
        self.assertTrue(client.command("CAPABILITIES").startswith(b"101 "))
        labels = [line.strip() for line in client.block()]
        self.assertNotIn(b"AUTHINFO USER", labels)

    def test_starttls_is_580_without_a_certificate(self):
        owner = self.serve(required=False)
        client = Client(owner.port)
        self.addCleanup(client.close)
        self.assertTrue(client.command("STARTTLS").startswith(b"580 "))
        self.assertTrue(client.command("CAPABILITIES").startswith(b"101 "))
        labels = [line.strip() for line in client.block()]
        self.assertNotIn(b"STARTTLS", labels)

    @unittest.skipUnless(openssl_available(), "openssl is not on PATH")
    def test_starttls_then_login(self):
        cert = certificate(self.root)
        owner = self.serve(required=True, protected_only=True, tls=cert)
        client = Client(owner.port)
        self.addCleanup(client.close)
        self.assertTrue(client.command("CAPABILITIES").startswith(b"101 "))
        self.assertIn(b"STARTTLS", [line.strip() for line in client.block()])
        self.assertTrue(client.starttls().startswith(b"382 "))
        # Inside TLS the protocol state is reset and AUTHINFO is allowed.
        self.assertTrue(client.command("AUTHINFO USER alice").startswith(b"381 "))
        self.assertTrue(client.command("AUTHINFO PASS correct-horse")
                        .startswith(b"281 "))
        # RFC 4642 section 2.1: the label is gone once the layer is up, and a
        # second STARTTLS is 502.
        self.assertTrue(client.command("CAPABILITIES").startswith(b"101 "))
        labels = [line.strip() for line in client.block()]
        self.assertNotIn(b"STARTTLS", labels)
        self.assertTrue(client.command("STARTTLS").startswith(b"502 "))

    @unittest.skipUnless(openssl_available(), "openssl is not on PATH")
    @unittest.skipUnless(nntplib_available(),
                         "nntplib was removed from the standard library in 3.13")
    def test_nntplib_starttls_and_login(self):
        import nntplib  # noqa: PLC0415  (guarded by the skip above)
        cert = certificate(self.root)
        owner = self.serve(required=True, protected_only=True, tls=cert)
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        context.check_hostname = False
        context.verify_mode = ssl.CERT_NONE
        with nntplib.NNTP("127.0.0.1", owner.port, timeout=30) as client:
            client.starttls(context)
            client.login("alice", "correct-horse")
            _, count, first, last, name = client.group("fn.letters")
            self.assertEqual(name, "fn.letters")


def run(argv):
    result = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=900)
    if result.returncode != 0:
        raise RuntimeError("{} failed: {}".format(
            " ".join(argv), (result.stdout + result.stderr).decode("utf-8", "replace")))
    return result


if __name__ == "__main__":
    unittest.main()

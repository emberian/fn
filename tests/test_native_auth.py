"""AUTHINFO through the installed native operator/owner, with no Python server."""
import os
from pathlib import Path
import select
import socket
import subprocess
import sys
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    return env


def free_loopback_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


class NativeAuthTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.access(IMAGE, os.X_OK):
            raise unittest.SkipTest(
                "native host image missing: {} (tools/build_native_host.sh)".format(IMAGE))

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-auth-")
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.store = root / "store"
        self.auth = root / "credentials.toml"
        self.config = root / "fn.toml"
        self.port = free_loopback_port()
        initialized = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "init", "fn.test"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.config.write_text(
            '[store]\npath = "{}"\n\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '\n[auth]\nrequired = true\nprotected_only = false\npath = "{}"\n'
            .format(self.store, self.port, self.auth), encoding="ascii")
        enrolled = subprocess.run(
            [sys.executable, "bin/fn", "--config", str(self.config),
             "principal", "set-password", "native-reader",
             "--password", "correct-horse", "--posting"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=600, check=False)
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())

    def start(self):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run", "--once"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment())
        line = wait_for_announcement(process, b"LISTENING ")
        if not line.startswith(b"LISTENING "):
            diagnostic = stop_and_diagnostics(process)
            process.stdout.close()
            process.stderr.close()
            self.fail("native authenticated owner failed: {} {}".format(
                line, diagnostic))
        return process

    def test_generated_credential_gates_reader_and_does_not_grant_transit(self):
        process = self.start()
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"201 "))

                stream.write(b"GROUP fn.test\r\n")
                self.assertTrue(stream.readline().startswith(b"480 "))

                # Transit authority remains the peer record's.  A reader
                # login policy neither authorizes nor intercepts IHAVE.
                stream.write(b"IHAVE <reader-is-not-peer@example.invalid>\r\n")
                self.assertTrue(stream.readline().startswith(b"502 "))

                stream.write(b"AUTHINFO USER native-reader\r\n")
                self.assertTrue(stream.readline().startswith(b"381 "))
                stream.write(b"AUTHINFO PASS wrong\r\n")
                self.assertTrue(stream.readline().startswith(b"481 "))
                stream.write(b"GROUP fn.test\r\n")
                self.assertTrue(stream.readline().startswith(b"480 "))

                stream.write(b"AUTHINFO USER native-reader\r\n")
                self.assertTrue(stream.readline().startswith(b"381 "))
                stream.write(b"AUTHINFO PASS correct-horse\r\n")
                self.assertTrue(stream.readline().startswith(b"281 "))
                stream.write(b"GROUP fn.test\r\n")
                self.assertTrue(stream.readline().startswith(b"211 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            self.assertEqual(process.wait(timeout=60), 0,
                             process.stderr.read().decode("utf-8", "replace"))
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()

    def test_restricted_command_before_login_is_480_and_leaves_no_article(self):
        # P1 (b) on the image: fn-served-dispatch-of-a-gated-command-is-480-
        # and-changes-nothing says a restricted command before the login is
        # answered 480 and the connection -- wire framing included -- is the
        # one it arrived on.  Observed here as: POST is 480 and never 340, the
        # article a client sends anyway is read as command lines and none of
        # them is accepted, and after the run the store holds no article under
        # that Message-ID.  The same client, logged in, posts a second
        # article, which the store then holds: the refusal is the gate's, not
        # a store that accepts nothing.
        refused = "<p1-before-login@example.invalid>"
        posted = "<p1-after-login@example.invalid>"

        def article(message_id):
            return [b"From: Native Reader <reader@example.invalid>",
                    b"Newsgroups: fn.test",
                    b"Subject: P1 gate",
                    b"Message-ID: " + message_id.encode("ascii"),
                    b"",
                    b"P1 gate body."]

        process = self.start()
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"201 "))

                stream.write(b"POST\r\n")
                self.assertTrue(stream.readline().startswith(b"480 "))
                # A client that ignores the 480 and sends the article: the wire
                # never entered article mode, so each non-empty line is a
                # command, answered on its own and never accepted.
                for line in article(refused) + [b"."]:
                    if not line:
                        continue
                    stream.write(line + b"\r\n")
                    reply = stream.readline()
                    self.assertFalse(reply.startswith((b"240 ", b"340 ")), reply)
                    self.assertTrue(reply[:1] in (b"4", b"5"), reply)
                for command in (b"ARTICLE " + refused.encode("ascii"),
                                b"STAT " + refused.encode("ascii"),
                                b"GROUP fn.test"):
                    stream.write(command + b"\r\n")
                    self.assertTrue(stream.readline().startswith(b"480 "), command)

                stream.write(b"AUTHINFO USER native-reader\r\n")
                self.assertTrue(stream.readline().startswith(b"381 "))
                stream.write(b"AUTHINFO PASS correct-horse\r\n")
                self.assertTrue(stream.readline().startswith(b"281 "))
                stream.write(b"POST\r\n")
                self.assertTrue(stream.readline().startswith(b"340 "))
                for line in article(posted):
                    stream.write(line + b"\r\n")
                stream.write(b".\r\n")
                self.assertTrue(stream.readline().startswith(b"240 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            self.assertEqual(process.wait(timeout=60), 0,
                             process.stderr.read().decode("utf-8", "replace"))
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()

        def inspect(message_id):
            return subprocess.run(
                [str(IMAGE), "--fn", "store", str(self.store), "inspect",
                 message_id], cwd=ROOT, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, env=environment(), timeout=180,
                check=False)

        held = inspect(posted)
        self.assertEqual(held.returncode, 0, held.stderr.decode())
        self.assertNotEqual(inspect(refused).returncode, 0)

    def test_protected_only_is_refused_before_listener(self):
        text = self.config.read_text(encoding="ascii").replace(
            "protected_only = false", "protected_only = true")
        protected = Path(self.temporary.name) / "protected.toml"
        protected.write_text(text, encoding="ascii")
        result = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(protected), "run", "--once"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(result.returncode, 5, result.stderr.decode())
        self.assertNotIn(b"LISTENING ", result.stdout)
        self.assertIn(b"unsupported-profile", result.stderr.lower())

    def test_legacy_cleartext_registry_is_refused_before_listener(self):
        self.auth.write_text(
            '[login."legacy"]\nsecret = "never-read"\n', encoding="ascii")
        result = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(self.config), "run", "--once"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(result.returncode, 1, result.stderr.decode())
        self.assertNotIn(b"LISTENING ", result.stdout)
        self.assertIn(b"cleartext-credential", result.stderr.lower())


if __name__ == "__main__":
    unittest.main()

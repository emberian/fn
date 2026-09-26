"""SCN-094: an invitation-code account, redeemed over TLS, once, across a
crash (PRF-164, NNT-034; PKT-439, PKT-440).

One node A on loopback with an implicit-TLS listener and `[auth]
protected_only = true` and no auth.toml.  The operator runs `account invite`
(the code is printed once); a friend's client, over TLS, sends `XREDEEM CODE
LOGIN` and `XREDEEM PASS PASSWORD` and is answered 281; on a new connection
AUTHINFO USER/PASS as LOGIN is 281 and a POST is 240.  The same code for
another login is 482; the same exchange again is 281 (the resume).  A second
code is redeemed on a developer image with FN_ACCOUNT_TEST_STOP_AFTER_PUBLISH:
the owner dies after the publication and before the reply; after a restart
the account logs in and the retried exchange answers 281.  Plaintext XREDEEM
on the protected listener is 483.  `account list` names both logins and
never a code.  Finally, when FN_OLD_IMAGE names an image from before accounts
(the deployed bbf52159), it refuses to open the store (PKT-440, witnessed).

The decisions are ACL2's: books/nntp-auth.lisp fn-auth-xredeem and
fn-auth-redeem-outcome, books/accounts.lisp fn-acct-redeem-bounded-plan and
fn-acct-redeem-word, run by host/native/admin.lisp fnn-owner-account-redeem.

FN_FRIEND_FN, when set, is `bin/fn` from an unpacked release tarball
(tests/friends_tarball.sh): the node then runs that installed image for
every step except the developer-image crash cut.

Run: FN_NATIVE_HOST=<developer launcher> python3 -m unittest -v tests.test_native_friends_accounts
"""

import os
from pathlib import Path
import re
import select
import signal
import socket
import ssl
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = (Path(IMAGE_TEXT) if IMAGE_TEXT else
         next((p for p in (ROOT / "build" / "fn-host-developer", ROOT / "build" / "fn-host")
               if p.is_file()), None))
FRIEND_FN = os.environ.get("FN_FRIEND_FN")
OLD_IMAGE = os.environ.get("FN_OLD_IMAGE")
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))
DEVELOPER = bool(IMAGE is not None and "developer" in IMAGE.name)


def environment(command, extra=None):
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    if FRIEND_FN and command[0] == FRIEND_FN:
        env.pop("FN_NATIVE_HOST", None)
    env.update(extra or {})
    return env


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def text(result):
    return (result.stdout + result.stderr).decode("utf-8", "replace").strip()


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a native launcher")
class NativeFriendsAccountsTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-accounts-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.image = [str(IMAGE), "--fn"]
        self.node = [FRIEND_FN] if FRIEND_FN else self.image
        self.store = self.root / "store"
        self.port, self.tls_port = free_port(), free_port()
        cert, key = self.root / "cert.pem", self.root / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout",
                        str(key), "-out", str(cert), "-days", "2", "-nodes",
                        "-subj", "/CN=127.0.0.1"], check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.config = self.root / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
            '[auth]\nprotected_only = true\n'.format(
                self.store, self.port, self.tls_port, cert, key,
                self.root / "control.sock"), encoding="ascii")
        self.process = None
        self.ok(self.node, "init", "local.general")

    def operator(self, command, *words):
        result = subprocess.run([*command, "operator", str(self.config), *words],
                                cwd=ROOT, env=environment(command),
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=240, check=False)
        print("NATIVE-ACCOUNTS", " ".join(words[:2]), "->", result.returncode)
        return result

    def ok(self, command, *words):
        result = self.operator(command, *words)
        self.assertEqual(result.returncode, 0, text(result))
        return result

    def start(self, command, extra=None):
        self.process = subprocess.Popen(
            [*command, "operator", str(self.config), "run"], cwd=ROOT,
            env=environment(command, extra), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0)
        self.addCleanup(self.reap)
        seen = 0
        for _ in range(6):
            self.assertTrue(select.select([self.process.stdout], [], [], 240)[0])
            if self.process.stdout.readline().startswith(b"LISTENING"):
                seen += 1
                if seen == 2:
                    return
        self.fail("owner readiness output was malformed")

    def stop(self):
        self.process.send_signal(signal.SIGTERM)
        self.assertEqual(self.process.wait(timeout=60), 0)
        log = self.process.stderr.read().decode("utf-8", "replace")
        self.reap()
        return log

    def reap(self):
        process, self.process = self.process, None
        if process is None:
            return
        if process.poll() is None:
            process.send_signal(signal.SIGKILL)
            process.wait(timeout=10)
        for stream in (process.stdout, process.stderr):
            if stream and not stream.closed:
                stream.close()

    def tls(self):
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        context.check_hostname = False
        context.verify_mode = ssl.CERT_NONE
        raw = socket.create_connection(("127.0.0.1", self.tls_port), timeout=60)
        stream = context.wrap_socket(raw).makefile("rwb", buffering=0)
        stream.readline()
        return stream

    def exchange(self, stream, line):
        stream.write(line.encode("ascii") + b"\r\n")
        reply = stream.readline().decode("ascii", "replace").strip()
        print("NATIVE-ACCOUNTS", line.split()[0], line.split()[1] if " " in line else "",
              "->", reply[:3])
        return reply

    def redeem(self, code, login, password):
        stream = self.tls()
        first = self.exchange(stream, "XREDEEM {} {}".format(code, login))
        if not first.startswith("381"):
            return first
        return self.exchange(stream, "XREDEEM PASS " + password)

    def login_and_post(self, login, password, message_id):
        stream = self.tls()
        self.assertTrue(self.exchange(stream, "AUTHINFO USER " + login).startswith("381"))
        reply = self.exchange(stream, "AUTHINFO PASS " + password)
        if not reply.startswith("281"):
            return reply
        self.assertTrue(self.exchange(stream, "POST").startswith("340"))
        stream.write(("From: {}@friend.example\r\nNewsgroups: local.general\r\n"
                      "Subject: hello\r\nMessage-ID: {}\r\n\r\nbody\r\n.\r\n"
                      .format(login, message_id)).encode("ascii"))
        return stream.readline().decode("ascii", "replace").strip()

    def invite(self, command):
        result = self.ok(command, "account", "invite", "--expires", "3600")
        codes = re.findall(rb"^[0-9a-f]{32}$", result.stdout, re.M)
        self.assertEqual(len(codes), 1, text(result))
        return codes[0].decode("ascii")

    def test_a_friend_redeems_a_code_once_across_a_crash(self):
        self.start(self.node)
        code = self.invite(self.node)
        # Cleartext on the protected listener: 483, nothing taken.
        with socket.create_connection(("127.0.0.1", self.port), timeout=60) as raw:
            plain = raw.makefile("rwb", buffering=0)
            plain.readline()
            self.assertTrue(self.exchange(plain, "XREDEEM {} robin".format(code))
                            .startswith("483"))
        self.assertTrue(self.redeem(code, "robin", "correct-horse").startswith("281"))
        reply = self.login_and_post("robin", "correct-horse", "<robin-1@friend.example>")
        self.assertTrue(reply.startswith("240"), reply)
        self.assertTrue(self.redeem(code, "mallory", "x").startswith("482"))
        self.assertTrue(self.redeem(code, "robin", "correct-horse").startswith("281"))
        self.assertTrue(self.redeem("0" * 32, "eve", "x").startswith("482"))
        listed = self.ok(self.node, "account", "list").stdout.decode("ascii")
        self.assertIn("redeemed robin ", listed)
        self.assertNotIn(code, listed)
        # The crash cut between the publication and the reply (developer image).
        second = self.invite(self.node)
        log = self.stop()
        self.assertNotIn(code, log)
        self.assertNotIn(second, log)
        if DEVELOPER:
            self.start(self.image, {"FN_ACCOUNT_TEST_STOP_AFTER_PUBLISH": "1"})
            stream = self.tls()
            self.assertTrue(self.exchange(stream, "XREDEEM {} robin2".format(second))
                            .startswith("381"))
            stream.write(b"XREDEEM PASS battery-staple\r\n")
            try:
                lost = stream.readline()
            except (OSError, ssl.SSLError):
                lost = b""
            self.assertEqual(lost, b"")
            self.assertEqual(self.process.wait(timeout=60), 137)
            self.reap()
            self.start(self.node)
            self.assertTrue(self.redeem(second, "robin2", "battery-staple")
                            .startswith("281"))
            reply = self.login_and_post("robin2", "battery-staple",
                                        "<robin2-1@friend.example>")
            self.assertTrue(reply.startswith("240"), reply)
            self.stop()
        # PKT-440: an image from before accounts refuses this store.
        if OLD_IMAGE:
            old = subprocess.run([OLD_IMAGE, "--fn", "operator", str(self.config),
                                  "status"], cwd=ROOT, env=environment([OLD_IMAGE]),
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 timeout=240, check=False)
            print("NATIVE-ACCOUNTS old-image status ->", old.returncode, text(old)[-200:])
            self.assertNotEqual(old.returncode, 0)

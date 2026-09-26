"""Native witness: a friend's node receives a cancel through the ordinary feed
(PKT-400, PRF-163), with the keys `peer keygen` made (PKT-402), the peers set
up by invite/accept/confirm and a live `peer add` (PKT-403), and the bare
`fn` and `fn --version` a stranger types first.

Two nodes on loopback, A (the author) and F (the friend).  Each makes its
key directory with `peer keygen`; A invites F with its own address, F
accepts, A confirms.  While both owners run, each replaces the other's
record with a live `peer add`: A feeds F `local.*` and F takes `local.*`
from A.  Neither wildmat names `control.cancel`.  A authors a signed article
T in local.general and then its signed cancel C (Newsgroups local.general,
filed at A in control.cancel).  Before PKT-400 C was offered under
control.cancel alone and never left A; now F withdraws T (430).

The decisions are ACL2's: the feed's groups books/owner.lisp
fn-own-sub-feed-groups (keystone fn-own-submission-offers-a-control-article-
under-its-newsgroups-and-filing-group), the keygen grammar
books/native-operator.lisp, the help text fn-nop-help-text.

FN_FRIEND_FN, when set, is the friend's `bin/fn` from an unpacked release
tarball (tests/friends_tarball.sh): F then runs that installed image, and
`fn --version` must print its source revision.

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest -v tests.test_native_friends_feed
"""

import os
from pathlib import Path
import re
import select
import shutil
import signal
import socket
import stat
import subprocess
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
FRIEND_FN = os.environ.get("FN_FRIEND_FN")
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))
EXIT_OK, EXIT_REFUSED = 0, 1


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    return env


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def text(result):
    return (result.stdout + result.stderr).decode("utf-8", "replace").strip()


def article(message_id, subject, control=None):
    lines = ["From: author@a.example", "Newsgroups: local.general",
             "Subject: " + subject, "Date: Sat, 26 Sep 2026 09:00:00 +0000",
             "Message-ID: " + message_id]
    if control:
        lines.append("Control: " + control)
    return ("\r\n".join(lines) + "\r\n\r\nbody\r\n").encode("ascii")


class Node:
    def __init__(self, test, base, name, command):
        self.test, self.name, self.command = test, name, command
        self.root = base / name
        self.root.mkdir()
        self.store, self.control = self.root / "store", self.root / "control.sock"
        self.port = free_port()
        self.config = self.root / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        self.process = None
        self.ok("init", "local.general", "control.cancel")
        self.ok("policy", "set", "path-identity", name + ".example")

    def run(self, *words):
        return subprocess.run([*self.command, *map(str, words)], cwd=ROOT,
                              env=environment(), stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=240, check=False)

    def operator(self, *words):
        result = self.run("operator", self.config, *words)
        print("NATIVE-FRIENDS", self.name, " ".join(map(str, words[:2])), "->",
              result.returncode)
        return result

    def ok(self, *words):
        result = self.operator(*words)
        self.test.assertEqual(result.returncode, EXIT_OK, text(result))
        return result

    def start(self):
        self.process = subprocess.Popen(
            [*self.command, "operator", str(self.config), "run"], cwd=ROOT,
            env=environment(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            bufsize=0)
        self.test.addCleanup(self.reap)
        for _ in range(4):
            self.test.assertTrue(select.select([self.process.stdout], [], [], 240)[0],
                                 "owner {} did not become ready".format(self.name))
            if self.process.stdout.readline().startswith(b"LISTENING "):
                return
        self.test.fail("owner {} readiness output was malformed".format(self.name))

    def stop(self):
        self.process.send_signal(signal.SIGTERM)
        self.test.assertEqual(self.process.wait(timeout=60), EXIT_OK)
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

    def article_status(self, message_id):
        with socket.create_connection(("127.0.0.1", self.port), timeout=30) as client:
            stream = client.makefile("rwb", buffering=0)
            stream.readline()
            stream.write(b"STAT " + message_id.encode("ascii") + b"\r\n")
            return stream.readline().decode("ascii", "replace").strip()

    def await_status(self, message_id, code, seconds=90):
        deadline = time.monotonic() + seconds
        while True:
            status = self.article_status(message_id)
            if status.startswith(code) or time.monotonic() > deadline:
                print("NATIVE-FRIENDS", self.name, "STAT", message_id, "->", status)
                return status
            time.sleep(0.5)


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a native launcher")
class NativeFriendsFeedTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-friends-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.image = [str(IMAGE), "--fn"]
        self.friend = [FRIEND_FN] if FRIEND_FN else self.image

    def test_bare_fn_and_version(self):
        for command in (self.image, self.friend):
            bare = subprocess.run(command, cwd=ROOT, env=environment(),
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  timeout=120, check=False)
            print("NATIVE-FRIENDS bare fn ->", bare.returncode, text(bare)[:120])
            self.assertEqual(bare.returncode, EXIT_OK, text(bare))
            self.assertIn("usage: fn operator CONFIG", bare.stdout.decode())
            version = subprocess.run([*command, "--version"], cwd=ROOT, env=environment(),
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     timeout=120, check=False)
            print("NATIVE-FRIENDS fn --version ->", version.returncode, text(version))
            if command is self.friend and FRIEND_FN:
                self.assertEqual(version.returncode, EXIT_OK, text(version))
            if version.returncode == EXIT_OK:
                self.assertRegex(version.stdout.decode(), r"^fn [0-9a-f]{40}\n$")
            else:
                self.assertEqual(version.returncode, EXIT_REFUSED, text(version))
                self.assertIn("records no source revision", text(version))

    def test_a_cancel_reaches_the_friend_through_the_ordinary_feed(self):
        a = Node(self, self.base, "a", self.image)
        f = Node(self, self.base, "f", self.friend)
        keys_a, keys_f = self.base / "keys-a", self.base / "keys-f"
        made = a.ok("peer", "keygen", keys_a)
        principal_a = re.search(r"principal ([0-9a-f]{64})", text(made)).group(1)
        f.ok("peer", "keygen", keys_f)
        self.assertEqual(stat.S_IMODE(keys_a.stat().st_mode), 0o700)
        for name in ("ed-public.bin", "ed-secret.bin", "ml-private.pem",
                     "ml-public.pem", "token.bin", "principal.bin"):
            self.assertEqual(stat.S_IMODE((keys_a / name).stat().st_mode) & 0o077, 0,
                             name)
        self.assertEqual(len((keys_a / "ed-secret.bin").read_bytes()), 64)
        self.assertEqual((keys_a / "principal.bin").read_bytes().hex(), principal_a)
        again = a.operator("peer", "keygen", keys_a)
        self.assertEqual(again.returncode, EXIT_REFUSED, text(again))
        self.assertIn("never overwrites", text(again))

        a.start()
        f.start()
        invitation, acceptance = self.base / "invitation", self.base / "acceptance"
        a.ok("peer", "invite", "f", "local.*", "127.0.0.1", f.port, "a.example",
             keys_a, invitation, "127.0.0.1", a.port)
        f.ok("peer", "accept", invitation, keys_f, "f.example", "-", acceptance)
        a.ok("peer", "confirm", acceptance, invitation)
        # PKT-403: live `peer add` on running owners; neither wildmat names
        # control.cancel.
        a.ok("peer", "add", "f", "f.example", "127.0.0.1", f.port, "-", "local.*",
             "127.0.0.1", "true")
        f.ok("peer", "add", "a.example", "a.example", "127.0.0.1", a.port, "local.*",
             "-", "127.0.0.1", "true")

        enrol = a.run("hybrid-enroll", a.control, "1", keys_a / "principal.bin",
                      keys_a / "ed-public.bin", keys_a / "ml-public.pem")
        self.assertEqual(enrol.returncode, EXIT_OK, text(enrol))

        def author(stem, message_id, control=None):
            source = self.base / (stem + ".eml")
            source.write_bytes(article(message_id, "friends " + stem, control))
            signed = a.run("hybrid-sign", keys_a / "principal.bin",
                           keys_a / "ed-public.bin", keys_a / "ed-secret.bin",
                           keys_a / "ml-public.pem", keys_a / "ml-private.pem", source)
            self.assertEqual(signed.returncode, EXIT_OK, text(signed))
            parts = dict(line.split() for line in signed.stdout.decode().splitlines())
            ed, ml = self.base / (stem + ".ed"), self.base / (stem + ".ml")
            ed.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            posted = a.run("hybrid-author", a.control, "1", source, ed, ml,
                           keys_a / "ml-public.pem")
            print("NATIVE-FRIENDS a hybrid-author", stem, "->", posted.returncode)
            self.assertEqual(posted.returncode, EXIT_OK, text(posted))

        target = "<friends-t@a.example>"
        author("target", target)
        self.assertTrue(f.await_status(target, "223").startswith("223"))
        cancel = "<friends-c@a.example>"
        author("cancel", cancel, "cancel " + target)
        self.assertTrue(a.await_status(target, "430").startswith("430"))
        withdrawn = f.await_status(target, "430")
        arrived = f.await_status(cancel, "223")
        a_log, f_log = a.stop(), f.stop()
        for line in a_log.splitlines():
            if "feed" in line or "cancel" in line:
                print("NATIVE-FRIENDS a-log", line[:200])
        self.assertTrue(arrived.startswith("223"), arrived)
        self.assertTrue(withdrawn.startswith("430"), withdrawn)


if __name__ == "__main__":
    unittest.main()

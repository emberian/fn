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
import re
import stat
import sys
import time
import unittest

from tests.native_harness import EXIT_OK, EXIT_REFUSED, ROOT, Client, Node, article, native_image

sys.path.insert(0, str(ROOT / "tools"))
import release_sequence  # noqa: E402
IMAGE = native_image("FN_NATIVE_HOST", "build/fn-host-developer")
if not os.environ.get("FN_NATIVE_HOST") and not IMAGE.is_file():
    IMAGE = ROOT / "build" / "fn-host"
FRIEND_FN = os.environ.get("FN_FRIEND_FN")
SMALL_PROFILE = ("--max-transactions", "16384", "--max-history-octets", "8388608",
                 "--max-record-octets", "196608", "--max-article-octets", "32768",
                 "--max-groups-per-article", "16", "--max-open-suffix", "128")
READY = bool(IMAGE.is_file() and os.access(IMAGE, os.X_OK))


def text(result):
    return (result.stdout + result.stderr).decode("utf-8", "replace").strip()


def friend_article(message_id, subject, control=None):
    return article(message_id, groups="local.general", subject=subject,
                   sender="author@a.example", date="Sat, 26 Sep 2026 09:00:00 +0000",
                   headers=["Control: " + control] if control else ())


class Peer(Node):
    """One node of the pair: initialized with the two groups and its path identity."""

    def __init__(self, case, name, friend=None):
        super().__init__(case, IMAGE, launcher=friend, name=name)
        small = SMALL_PROFILE if friend else ()
        self.ok("init", *small, "local.general", "control.cancel")
        self.ok("policy", "set", "path-identity", name + ".example")

    def operator(self, *words, **options):
        result = super().operator(*words, timeout=240, **options)
        print("NATIVE-FRIENDS", self.name, " ".join(map(str, words[:2])), "->",
              result.returncode)
        return result

    def ok(self, *words):
        result = self.operator(*words)
        self.case.assertEqual(result.returncode, EXIT_OK, text(result))
        return result

    def run(self, *words):
        return self.invoke(*words, timeout=240)

    def stop(self):
        process = self.process
        super().stop()
        return process.stderr.since(0).decode("utf-8", "replace")

    def article_status(self, message_id):
        with Client(self.port, timeout=30, greeting=None) as client:
            return client.command("STAT " + message_id).decode("ascii", "replace").strip()

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
    def test_bare_fn_and_version(self):
        own = Node(self, IMAGE, listener=False, control=False)
        friend = Node(self, IMAGE, launcher=FRIEND_FN, listener=False, control=False)
        for node, is_friend in ((own, False), (friend, True)):
            bare = node.invoke(timeout=120)
            print("NATIVE-FRIENDS bare fn ->", bare.returncode, text(bare)[:120])
            self.assertEqual(bare.returncode, EXIT_OK, text(bare))
            self.assertIn("usage: fn operator CONFIG {help|init|", bare.stdout.decode())
            version = node.invoke("--version", timeout=120)
            print("NATIVE-FRIENDS fn --version ->", version.returncode, text(version))
            if is_friend and FRIEND_FN:
                self.assertEqual(version.returncode, EXIT_OK, text(version))
            if version.returncode == EXIT_OK:
                printed = re.fullmatch(r"fn ([0-9]+(?:\.[0-9]+)+) \(([0-9a-f]{12})\)\n",
                                       version.stdout.decode())
                self.assertIsNotNone(printed, version.stdout)
                release_sequence.position(printed.group(1))
            else:
                self.assertEqual(version.returncode, EXIT_REFUSED, text(version))
                self.assertIn("records no source revision", text(version))

    def test_a_cancel_reaches_the_friend_through_the_ordinary_feed(self):
        a = Peer(self, "a")
        f = Peer(self, "f", friend=FRIEND_FN)
        self.base = a.root.parent
        keys_a, keys_f = self.base / "keys-a", self.base / "keys-f"
        made = a.ok("peer", "keygen", keys_a)
        principal_a = re.search(r"principal ([0-9a-f]{64})", text(made)).group(1)
        f.ok("peer", "keygen", keys_f)
        self.assertEqual(stat.S_IMODE(keys_a.stat().st_mode), 0o700)
        # The secret halves and their public twins are 0600; token.bin and
        # principal.bin are genesis's (public words the invitation carries).
        for name in ("ed-public.bin", "ed-secret.bin", "ml-private.pem",
                     "ml-public.pem"):
            self.assertEqual(stat.S_IMODE((keys_a / name).stat().st_mode) & 0o077, 0,
                             name)
        self.assertEqual(len((keys_a / "ed-secret.bin").read_bytes()), 64)
        self.assertEqual((keys_a / "principal.bin").read_bytes().hex(), principal_a)
        again = a.operator("peer", "keygen", keys_a)
        self.assertEqual(again.returncode, EXIT_REFUSED, text(again))
        self.assertIn("never overwrites", text(again))

        a.start()
        f.start()
        # A's own principal signs its articles: enrolled at A as keyring
        # generation 1, before the confirm enrols F.
        enrol = a.run("hybrid-enroll", a.control, "1", keys_a / "principal.bin",
                      keys_a / "ed-public.bin", keys_a / "ml-public.pem")
        self.assertEqual(enrol.returncode, EXIT_OK, text(enrol))
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


        def author(stem, message_id, control=None):
            source = self.base / (stem + ".eml")
            source.write_bytes(friend_article(message_id, "friends " + stem, control))
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

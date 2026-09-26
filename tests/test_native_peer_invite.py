"""Native witness for peering invitations (PRF-097, specs/peering.md section 9).

`fn operator CONFIG peer genesis|invite|accept|confirm` on running owners:
the operator plan is books/native-operator.lisp's; the three live verbs reach
the owner as hybrid control requests 9, 10 and 11 (host/native/peer-invite.lisp),
whose decisions are books/peer-invite.lisp's `fn-pinv-issue-plan`,
`fn-pinv-accept-step`, `fn-pinv-confirm-plan` and `fn-pinv-confirm-step`.
Every node is a fresh store; key directories are generated with OpenSSL
(`FN_OPENSSL`, 3.5 or later for ML-DSA-65) and their principals by `peer
genesis`.  The crash case needs a developer image (the
FN_PEER_TEST_STOP_AFTER_CONSUME selector).

Run: FN_NATIVE_HOST=<launcher> FN_OPENSSL=<openssl> \
     python3 -m unittest -v tests.test_native_peer_invite
"""

import os
from pathlib import Path
import select
import shutil
import signal
import subprocess
import tempfile
import unittest

from tests import test_native_live_reconfiguration as live

ROOT = live.ROOT
IMAGE = live.IMAGE
EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN = 0, 1, 3
OPENSSL = os.environ.get("FN_OPENSSL", "openssl")


def openssl(*args):
    subprocess.run([OPENSSL, *args], check=True, stdout=subprocess.PIPE,
                   stderr=subprocess.PIPE)


def keygen(directory):
    directory.mkdir(parents=True)
    der, pub = directory / "ed-private.der", directory / "ed-public.der"
    openssl("genpkey", "-algorithm", "ED25519", "-outform", "DER", "-out", str(der))
    openssl("pkey", "-inform", "DER", "-in", str(der), "-pubout", "-outform", "DER",
            "-out", str(pub))
    seed, public = der.read_bytes()[-32:], pub.read_bytes()[-32:]
    (directory / "ed-public.bin").write_bytes(public)
    (directory / "ed-secret.bin").write_bytes(seed + public)
    der.unlink()
    pub.unlink()
    openssl("genpkey", "-algorithm", "ML-DSA-65", "-out", str(directory / "ml-private.pem"))
    openssl("pkey", "-in", str(directory / "ml-private.pem"), "-pubout", "-out",
            str(directory / "ml-public.pem"))
    return directory


def out(result):
    return (result.stdout + result.stderr).decode("utf-8", "replace").strip()


class Node:
    def __init__(self, test, root, name, env=None):
        self.test, self.name = test, name
        self.root = root / name
        self.root.mkdir()
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.port = live.free_port()
        self.config = self.root / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        self.env = dict(live.environment(), **(env or {}))
        self.process = None
        test.assertEqual(self.operator("init", "fn.test").returncode, EXIT_OK)

    def operator(self, *words, timeout=240):
        return subprocess.run([str(IMAGE), "--fn", "operator", str(self.config), *words],
                              cwd=ROOT, env=live.environment(), stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=timeout, check=False)

    def start(self, env=None):
        self.process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"], cwd=ROOT,
            env=dict(self.env, **(env or {})), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0)
        self.test.addCleanup(self.reap)
        for _ in range(4):
            self.test.assertTrue(select.select([self.process.stdout], [], [], 240)[0],
                                 "owner {} did not become ready".format(self.name))
            if self.process.stdout.readline().startswith(b"LISTENING "):
                return self
            if self.process.poll() is not None:
                self.test.fail("owner {} failed: {}".format(
                    self.name, self.process.stderr.read().decode("utf-8", "replace")))
        self.test.fail("owner {} readiness output was malformed".format(self.name))

    def stop(self):
        self.process.send_signal(signal.SIGTERM)
        self.test.assertEqual(self.process.wait(timeout=60), EXIT_OK)
        self.reap()

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

    def key_history(self):
        result = subprocess.run([str(IMAGE), "--fn", "hybrid-key-history", str(self.store)],
                                cwd=ROOT, env=live.environment(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=240, check=False)
        self.test.assertEqual(result.returncode, EXIT_OK, out(result))
        return result.stdout.decode("ascii").splitlines()


@unittest.skipUnless(live.executable(IMAGE) and shutil.which(OPENSSL),
                     "set FN_NATIVE_HOST to a native launcher and FN_OPENSSL to openssl 3.5")
class NativePeerInviteTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-peer-invite-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def keys(self, name, node):
        directory = keygen(self.root / ("keys-" + name))
        result = node.operator("peer", "genesis", str(directory))
        self.assertEqual(result.returncode, EXIT_OK, out(result))
        principal = (directory / "principal.bin").read_bytes().hex()
        print("NATIVE-PEER-INVITE genesis", name, principal)
        return directory, principal

    def run_ok(self, node, *words):
        result = node.operator(*words)
        print("NATIVE-PEER-INVITE", node.name, " ".join(words[:2]), "->", result.returncode)
        self.assertEqual(result.returncode, EXIT_OK, out(result))
        return result

    def refused(self, node, words, reason):
        result = node.operator(*words)
        print("NATIVE-PEER-INVITE", node.name, " ".join(words[:2]), "->",
              result.returncode, "expected", reason)
        self.assertEqual(result.returncode, EXIT_REFUSED, out(result))
        return result

    def owner_log(self, node):
        return node.process.stderr.read().decode("utf-8", "replace")

    def test_invite_accept_confirm_and_the_refusals(self):
        a, b, c = (Node(self, self.root, n) for n in ("A", "B", "C"))
        keys_a, pa = self.keys("a", a)
        keys_b, pb = self.keys("b", b)
        keys_c, pc = self.keys("c", c)
        for node in (a, b, c):
            node.start()
        inv = self.root / "inv1"
        self.run_ok(a, "peer", "invite", "nodeB", "fn.*", "127.0.0.1", str(b.port),
                    "a.example", str(keys_a), str(inv), "-", "-")
        acc = self.root / "acc1"
        self.run_ok(b, "peer", "accept", str(inv), str(keys_b), "b.example", "-", str(acc))
        # The same invitation again at B: A is already B's current enrolment.
        self.refused(b, ("peer", "accept", str(inv), str(keys_b), "b.example", "-",
                         str(self.root / "acc1-again")), "already-enrolled")
        # A tampered acceptance: one octet of the signed body changed.
        tampered = self.root / "acc1-tampered"
        data = acc.read_bytes()
        at = data.index(b"Acceptor-Path: b.example")
        tampered.write_bytes(data[:at + 15] + b"c" + data[at + 16:])
        self.refused(a, ("peer", "confirm", str(tampered), str(inv)), "unverified")
        # PRF-124: another invitation A issued, presented with this acceptance.
        inv_other = self.root / "inv-other"
        self.run_ok(a, "peer", "invite", "nodeX", "fn.*", "127.0.0.1", "11999",
                    "a.example", str(keys_a), str(inv_other), "-", "-")
        self.refused(a, ("peer", "confirm", str(acc), str(inv_other)), "another-invitation")
        self.assertNotIn("nodeB", out(a.operator("peer", "list")))
        self.run_ok(a, "peer", "confirm", str(acc), str(inv))
        # PRF-124: the confirm's one record configured B as a peer of A, bound
        # to B's principal.
        listed = out(a.operator("peer", "list"))
        print("NATIVE-PEER-INVITE A peer list after confirm:", listed)
        self.assertIn("nodeB", listed)
        self.assertIn(pb, listed)
        # A second confirm of the same acceptance.
        self.refused(a, ("peer", "confirm", str(acc), str(inv)), "already-confirmed")
        # A replayed nonce: C accepts the consumed invitation (C enrols A),
        # and A refuses C's acceptance.
        acc_c = self.root / "acc-c"
        self.run_ok(c, "peer", "accept", str(inv), str(keys_c), "c.example", "-", str(acc_c))
        self.refused(a, ("peer", "confirm", str(acc_c), str(inv)), "invitation-consumed")
        # An invitation presented to confirm is not an acceptance.
        self.refused(a, ("peer", "confirm", str(inv), str(inv)), "document-kind")
        for node in (a, b, c):
            node.stop()
        history_a, history_b = a.key_history(), b.key_history()
        print("NATIVE-PEER-INVITE A key history:", history_a)
        print("NATIVE-PEER-INVITE B key history:", history_b)
        self.assertEqual([line for line in history_a if pb in line],
                         ["generation=1 state=active principal={}".format(pb)])
        self.assertFalse([line for line in history_a if pc in line])
        self.assertEqual([line for line in history_b if pa in line],
                         ["generation=1 state=active principal={}".format(pa)])

    def test_an_acceptance_of_an_invitation_this_node_never_issued(self):
        a, d, e = (Node(self, self.root, n) for n in ("A", "D", "E"))
        keys_a, _ = self.keys("a", a)
        keys_f, _ = self.keys("f", d)
        keys_e, _ = self.keys("e", e)
        for node in (a, d, e):
            node.start()
        # D invites under A's own keys; A never recorded that nonce.
        foreign = self.root / "inv-d"
        self.run_ok(d, "peer", "invite", "nodeE", "fn.*", "127.0.0.1", str(e.port),
                    "d.example", str(keys_a), str(foreign), "-", "-")
        acc_e = self.root / "acc-e"
        self.run_ok(e, "peer", "accept", str(foreign), str(keys_e), "e.example", "-",
                    str(acc_e))
        self.refused(a, ("peer", "confirm", str(acc_e), str(foreign)), "no-such-invitation")
        for node in (a, d, e):
            node.stop()

    def test_a_crash_between_consumption_and_enrolment_enrols_once(self):
        a2, b2 = Node(self, self.root, "A2"), Node(self, self.root, "B2")
        keys_g, _ = self.keys("g", a2)
        keys_h, ph = self.keys("h", b2)
        a2.start(env={"FN_PEER_TEST_STOP_AFTER_CONSUME": "1"})
        b2.start()
        inv = self.root / "inv-crash"
        self.run_ok(a2, "peer", "invite", "nodeB2", "fn.*", "127.0.0.1", str(b2.port),
                    "a2.example", str(keys_g), str(inv), "-", "-")
        acc = self.root / "acc-crash"
        self.run_ok(b2, "peer", "accept", str(inv), str(keys_h), "b2.example", "-", str(acc))
        died = a2.operator("peer", "confirm", str(acc), str(inv))
        print("NATIVE-PEER-INVITE A2 confirm with the stop ->", died.returncode)
        self.assertNotEqual(died.returncode, EXIT_OK, out(died))
        self.assertEqual(a2.process.wait(timeout=60), 137)
        a2.reap()
        self.assertFalse([line for line in a2.key_history() if ph in line])
        a2.start()
        # The one record is durable: the peer exists before the enrolment.
        listed = out(a2.operator("peer", "list"))
        print("NATIVE-PEER-INVITE A2 peer list after the stop:", listed)
        self.assertIn("nodeB2", listed)
        self.run_ok(a2, "peer", "confirm", str(acc), str(inv))
        self.refused(a2, ("peer", "confirm", str(acc), str(inv)), "already-confirmed")
        a2.stop()
        b2.stop()
        history = a2.key_history()
        print("NATIVE-PEER-INVITE A2 key history:", history)
        self.assertEqual(len([line for line in history if ph in line]), 1)

    def test_accept_configures_the_inviter_and_resumes_after_a_cut(self):
        """PRF-160: an invitation naming the inviter's address configures the
        inviter as a peer at the accepting node in one configuration record
        before the enrolment; a death between the two leaves the peer and no
        enrolment, and the next accept enrols once without a second record."""
        a, b = Node(self, self.root, "A3"), Node(self, self.root, "B3")
        keys_a, pa = self.keys("a3", a)
        keys_b, pb = self.keys("b3", b)
        a.start()
        b.start(env={"FN_PEER_TEST_STOP_AFTER_CONFIGURE": "1"})
        inv = self.root / "inv-addressed"
        self.run_ok(a, "peer", "invite", "nodeB3", "fn.*", "127.0.0.1", str(b.port),
                    "a3.example", str(keys_a), str(inv), "127.0.0.1", str(a.port))
        body = inv.read_bytes()
        self.assertIn("Inviter-Host: 127.0.0.1".encode(), body)
        self.assertIn("Inviter-Port: {}".format(a.port).encode(), body)
        acc = self.root / "acc-addressed"
        died = b.operator("peer", "accept", str(inv), str(keys_b), "b3.example", "-",
                          str(acc))
        print("NATIVE-PEER-INVITE B3 accept with the stop ->", died.returncode)
        self.assertNotEqual(died.returncode, EXIT_OK, out(died))
        self.assertEqual(b.process.wait(timeout=60), 137)
        b.reap()
        self.assertFalse(acc.exists())
        self.assertFalse([line for line in b.key_history() if pa in line])
        b.start()
        listed = out(b.operator("peer", "list"))
        print("NATIVE-PEER-INVITE B3 peer list after the stop:", listed)
        self.assertIn("a3.example path-identity=a3.example address=127.0.0.1 port={}"
                      .format(a.port), listed)
        self.assertIn(pa, listed)
        self.run_ok(b, "peer", "accept", str(inv), str(keys_b), "b3.example", "-", str(acc))
        again = out(b.operator("peer", "list"))
        self.assertEqual(again, listed)
        self.refused(b, ("peer", "accept", str(inv), str(keys_b), "b3.example", "-",
                         str(self.root / "acc-again")), "already-enrolled")
        self.run_ok(a, "peer", "confirm", str(acc), str(inv))
        listed_a = out(a.operator("peer", "list"))
        print("NATIVE-PEER-INVITE A3 peer list after confirm:", listed_a)
        self.assertIn("nodeB3", listed_a)
        self.assertIn(pb, listed_a)
        a.stop()
        b.stop()
        history = b.key_history()
        print("NATIVE-PEER-INVITE B3 key history:", history)
        self.assertEqual([line for line in history if pa in line],
                         ["generation=1 state=active principal={}".format(pa)])

    def hybrid(self, *words):
        result = subprocess.run([str(IMAGE), "--fn", *words], cwd=ROOT,
                                env=live.environment(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=240, check=False)
        self.assertEqual(result.returncode, EXIT_OK, out(result))
        return result

    def stop_with_log(self, node):
        node.process.send_signal(signal.SIGTERM)
        self.assertEqual(node.process.wait(timeout=60), EXIT_OK)
        log = node.process.stderr.read().decode("utf-8", "replace")
        node.reap()
        return log

    def test_a_succeeded_friend_is_confirmed_under_its_current_keys(self):
        """PKT-211 (PRF-179): B enrolled at A under its genesis keys and then
        succeeded (generation 2, the same principal and token, new keys).  A
        invites B; B accepts signing with its CURRENT keys; A confirms: the
        consumption and peer record, and nothing to enrol (B is already
        current at those keys).  B's superseded genesis keys are refused
        `not-current-keys` at A, and a node that never enrolled B refuses the
        current keys `genesis`."""
        a, b, c = (Node(self, self.root, n) for n in ("A4", "B4", "C4"))
        keys_a, _ = self.keys("a4", a)
        keys_b, pb = self.keys("b4", b)
        keys_c, _ = self.keys("c4", c)
        keys_b2 = keygen(self.root / "keys-b4-next")
        for name in ("principal.bin", "token.bin"):
            shutil.copy(keys_b / name, keys_b2 / name)
        for node in (a, b, c):
            node.start()
        for keys in (keys_b, keys_b2):
            self.hybrid("hybrid-enroll-next", str(a.control), str(keys_b / "principal.bin"),
                        str(keys / "ed-public.bin"), str(keys / "ml-public.pem"))
        before = [line for line in a.key_history() if pb in line]
        print("NATIVE-PEER-INVITE A4 key history before:", before)
        self.assertIn("generation=2 state=active principal={}".format(pb), before)
        inv = self.root / "inv-succeeded"
        self.run_ok(a, "peer", "invite", "nodeB4", "fn.*", "127.0.0.1", str(b.port),
                    "a4.example", str(keys_a), str(inv), "-", "-")
        acc = self.root / "acc-succeeded"
        self.run_ok(b, "peer", "accept", str(inv), str(keys_b2), "b4.example", "-", str(acc))
        self.run_ok(a, "peer", "confirm", str(acc), str(inv))
        listed = out(a.operator("peer", "list"))
        print("NATIVE-PEER-INVITE A4 peer list after confirm:", listed)
        self.assertIn("nodeB4", listed)
        self.assertIn(pb, listed)
        self.refused(a, ("peer", "confirm", str(acc), str(inv)), "already-confirmed")
        # The superseded keys: a fresh node D accepts another invitation of A
        # under B's genesis key set; A refuses it.
        d = Node(self, self.root, "D4")
        d.start()
        inv_old = self.root / "inv-old-keys"
        self.run_ok(a, "peer", "invite", "nodeD4", "fn.*", "127.0.0.1", str(d.port),
                    "a4.example", str(keys_a), str(inv_old), "-", "-")
        acc_old = self.root / "acc-old-keys"
        self.run_ok(d, "peer", "accept", str(inv_old), str(keys_b), "d4.example", "-",
                    str(acc_old))
        self.refused(a, ("peer", "confirm", str(acc_old), str(inv_old)), "not-current-keys")
        # C never enrolled B: B's current keys do not bind B's principal there.
        inv_c = self.root / "inv-c4"
        self.run_ok(c, "peer", "invite", "nodeB4", "fn.*", "127.0.0.1", str(b.port),
                    "c4.example", str(keys_c), str(inv_c), "-", "-")
        acc_c = self.root / "acc-c4"
        self.run_ok(b, "peer", "accept", str(inv_c), str(keys_b2), "b4.example", "-",
                    str(acc_c))
        self.refused(c, ("peer", "confirm", str(acc_c), str(inv_c)), "genesis")
        log_a, log_c = self.stop_with_log(a), self.stop_with_log(c)
        for node in (b, d):
            node.stop()
        self.assertIn("peer confirm: the acceptor's current keys; nothing to enrol", log_a)
        self.assertIn("peer confirm refused: not-current-keys", log_a)
        self.assertIn("peer confirm refused: genesis", log_c)
        after = [line for line in a.key_history() if pb in line]
        print("NATIVE-PEER-INVITE A4 key history after:", after)
        self.assertEqual(after, before)


if __name__ == "__main__":
    unittest.main()

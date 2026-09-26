"""Native witness for key statements (PRF-098, SCN-053, NNT-014).

One node, driven through its public surfaces: `hybrid-enroll` over the
control socket, `operator CONFIG control grant P keys fn.keys`, served POST
of FN-Authorship carriers rendered by `hybrid-sign-carrier`, an IHAVE from a
configured peer whose carried-source list names a principal this node has
not enrolled, and `hybrid-key-history` with the owner stopped.  The kill
case starts a developer image with
FN_NATIVE_KEY_STATEMENT_FAULT=statement-committed:kill, which dies after the
statement's kind-4 commit and before its key change (books/key-statements.lisp
`fn-ks-cut`); the restart's recovery makes the change (`fn-ks-recover`).

Run: FN_NATIVE_HOST=<developer launcher> FN_TEST_OPENSSL=<openssl 3.5>
python3 -m unittest -v tests.test_native_key_statements
"""

import os
from pathlib import Path
import socket
import subprocess
import tempfile
import time
import unittest

from tests.native_process import wait_for_announcement, stop_and_diagnostics

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host-developer"))
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")

P = bytes([85]) * 32
Q = bytes([102]) * 32
# RFC 8032 section 7.1, tests 1, 2 and 3: (seed, public).
ED_OLD = ("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
          "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
ED_NEW = ("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
          "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")
ED_Q = ("c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
        "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025")
POP_TAG = b"fn-key-succession-pop-v1"


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def hex_lines(name, octets):
    text = octets.hex()
    return b"".join("{}: {}\r\n".format(name, text[i:i + 64]).encode("ascii")
                    for i in range(0, len(text), 64))


def witness(*words):
    print("NATIVE-KEY-STATEMENT-WITNESS", *words, flush=True)


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "set FN_NATIVE_HOST to a developer launcher")
class NativeKeyStatementTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-key-statements-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.env = dict(os.environ)
        self.env.pop("FN_NATIVE_KEY_STATEMENT_FAULT", None)
        self.keys = {}
        for name, (seed, public) in (("old", ED_OLD), ("new", ED_NEW), ("q", ED_Q)):
            self.keys[name] = self.key_set(name, seed, public)
        self.principal_file = self.write("principal-p.bin", P)
        self.q_file = self.write("principal-q.bin", Q)

    # -- files and processes --------------------------------------------------
    def write(self, name, octets):
        path = self.root / name
        path.write_bytes(octets)
        return path

    def run_ok(self, argv, expected=0, env=None, timeout=180):
        result = subprocess.run([str(a) for a in argv], cwd=ROOT, env=env or self.env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
        self.assertEqual(result.returncode, expected,
                         "{} -> {}\n{}\n{}".format(argv, result.returncode,
                                                   result.stdout.decode("utf-8", "replace"),
                                                   result.stderr.decode("utf-8", "replace")))
        return result

    def fn(self, *args, expected=0):
        return self.run_ok([IMAGE, "--fn", *args], expected=expected)

    def key_set(self, name, seed, public):
        ed_public = self.write(name + "-ed.pub", bytes.fromhex(public))
        ed_secret = self.write(name + "-ed.sec", bytes.fromhex(seed + public))
        ml_private = self.root / (name + "-ml.pem")
        ml_public = self.root / (name + "-ml.pub.pem")
        self.run_ok([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", ml_private])
        self.run_ok([OPENSSL, "pkey", "-in", ml_private, "-pubout", "-out", ml_public])
        der = self.run_ok([OPENSSL, "pkey", "-pubin", "-in", ml_public,
                           "-outform", "DER"]).stdout
        return {"ed_public": ed_public, "ed_secret": ed_secret,
                "ed_raw": bytes.fromhex(public), "ml_private": ml_private,
                "ml_public": ml_public, "ml_raw": der[-1952:]}

    def node(self, name, groups=("fn.test", "fn.keys")):
        root = self.root / name
        root.mkdir()
        store = root / "store"
        self.fn("store", store, "init", *groups)
        node = {"root": root, "store": store, "port": free_port(),
                "control": root / "control.sock", "log": root / "service.log",
                "config": root / "fn.toml"}
        node["config"].write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                store, node["port"], node["control"], node["log"]), encoding="ascii")
        return node

    def start(self, node, env=None):
        proc = subprocess.Popen([str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
                                cwd=ROOT, env=env or self.env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        wait_for_announcement(proc, b"LISTENING ")
        node["process"] = proc
        return proc

    def stop(self, node):
        diagnostic = stop_and_diagnostics(node["process"], timeout=60)
        self.assertEqual(node["process"].returncode, 0, diagnostic)

    def log(self, node):
        return node["log"].read_text("utf-8", "replace") if node["log"].exists() else ""

    def history(self, node):
        return self.fn("hybrid-key-history", node["store"]).stdout.decode().splitlines()

    # -- articles -------------------------------------------------------------
    def carrier(self, principal_file, keys, source, stem):
        source_path = self.write(stem + ".src", source)
        out = self.root / (stem + ".carrier")
        self.fn("hybrid-sign-carrier", principal_file, keys["ed_public"], keys["ed_secret"],
                keys["ml_public"], keys["ml_private"], source_path, out)
        return out.read_bytes()

    @staticmethod
    def header(msgid, group, subject):
        return ("From: keys@example.invalid\r\nDate: Fri, 25 Sep 2026 12:00:00 +0000\r\n"
                "Newsgroups: {}\r\nSubject: {}\r\nMessage-ID: {}\r\n\r\n".format(
                    group, subject, msgid)).encode("ascii")

    def succession(self, msgid, principal, old, new):
        pop_source = POP_TAG + b"\n" + msgid.encode("ascii") + b"\n" + old["ed_raw"]
        pop = self.fn("hybrid-sign", self.principal_file, new["ed_public"], new["ed_secret"],
                      new["ml_public"], new["ml_private"],
                      self.write("pop-" + str(abs(hash(msgid))) + ".src", pop_source))
        sigs = dict(line.split() for line in pop.stdout.decode().splitlines())
        return (self.header(msgid, "fn.keys", "fn-key-statement")
                + b"FN-Key-Statement: succession-v1\r\n"
                + hex_lines("FN-Key-Principal", principal)
                + hex_lines("FN-Key-Old-Ed25519", old["ed_raw"])
                + hex_lines("FN-Key-New-Ed25519", new["ed_raw"])
                + hex_lines("FN-Key-New-ML-DSA-65", new["ml_raw"])
                + hex_lines("FN-Key-PoP-Ed25519", bytes.fromhex(sigs["ed25519"]))
                + hex_lines("FN-Key-PoP-ML-DSA-65", bytes.fromhex(sigs["ml-dsa-65"])))

    def revocation(self, msgid, principal):
        return (self.header(msgid, "fn.keys", "fn-key-statement")
                + b"FN-Key-Statement: revocation-v1\r\n"
                + hex_lines("FN-Key-Principal", principal))

    def ordinary(self, msgid):
        return self.header(msgid, "fn.test", "ordinary") + b"body\r\n"

    def post(self, node, article, expect_reply=True):
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=60) as sock:
            stream = sock.makefile("rwb", buffering=0)
            greeting = stream.readline()
            self.assertTrue(greeting.startswith(b"200 "), greeting)
            stream.write(b"POST\r\n")
            self.assertTrue(stream.readline().startswith(b"340 "))
            for line in article.splitlines(keepends=True):
                stream.write(b"." + line if line.startswith(b".") else line)
            stream.write(b".\r\n")
            reply = stream.readline()
        if expect_reply:
            self.assertTrue(reply, "no POST reply")
        return reply

    def ihave(self, node, msgid, article):
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=60) as sock:
            stream = sock.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"IHAVE " + msgid.encode("ascii") + b"\r\n")
            offered = stream.readline()
            self.assertTrue(offered.startswith(b"335 "), offered)
            for line in article.splitlines(keepends=True):
                stream.write(b"." + line if line.startswith(b".") else line)
            stream.write(b".\r\n")
            return stream.readline()

    def enrol_and_grant(self, node):
        old = self.keys["old"]
        self.fn("hybrid-enroll", node["control"], "1", self.principal_file,
                old["ed_public"], old["ml_public"])
        self.fn("operator", node["config"], "control", "grant", P.hex(), "keys", "fn.keys")

    # -- cases ----------------------------------------------------------------
    def test_succession_revocation_and_carried_statement(self):
        b = self.node("b")
        self.fn("operator", b["config"], "peer", "add", "a", "a.example.invalid",
                "127.0.0.1", str(free_port()), "fn.*", "-", "source-address", "127.0.0.1",
                "true", "carries", Q.hex())
        # PRF-099: a carrying boundary carries nothing without a budget.
        self.fn("operator", b["config"], "peer", "budget", "a", "1048576", "16")
        self.start(b)
        try:
            self.enrol_and_grant(b)
            old, new = self.keys["old"], self.keys["new"]
            # Succession: signed by the old keys, PoP by the new.
            statement = self.carrier(self.principal_file, old,
                                     self.succession("<succession@keys.invalid>", P, old, new),
                                     "succession")
            reply = self.post(b, statement)
            witness("succession POST", reply.strip())
            self.assertTrue(reply.startswith(b"240 "), reply)
            self.assertIn("key-statement enrol-successor committed", self.log(b))
            # An article under the old keys is refused; under the new, accepted.
            refused = self.post(b, self.carrier(self.principal_file, old,
                                                self.ordinary("<old-key@keys.invalid>"), "oldart"))
            accepted = self.post(b, self.carrier(self.principal_file, new,
                                                 self.ordinary("<new-key@keys.invalid>"), "newart"))
            witness("old-key POST", refused.strip(), "new-key POST", accepted.strip())
            self.assertTrue(refused.startswith(b"441 "), refused)
            self.assertTrue(accepted.startswith(b"240 "), accepted)
            # A carried statement (Q is not enrolled here; the peer carries Q)
            # is stored and declines.
            q = self.keys["q"]
            carried = (b"Path: a.example.invalid!not-for-mail\r\n"
                       + self.carrier(self.q_file, q,
                                      self.revocation("<carried@keys.invalid>", Q), "carried"))
            carried_reply = self.ihave(b, "<carried@keys.invalid>", carried)
            witness("carried IHAVE", carried_reply.strip())
            self.assertTrue(carried_reply.startswith(b"235 "), carried_reply)
            self.assertIn("key-statement declined carried", self.log(b))
            # Revocation, signed by the current (new) keys.
            revocation = self.carrier(self.principal_file, new,
                                      self.revocation("<revocation@keys.invalid>", P),
                                      "revocation")
            revoked_reply = self.post(b, revocation)
            witness("revocation POST", revoked_reply.strip())
            self.assertTrue(revoked_reply.startswith(b"240 "), revoked_reply)
            self.assertIn("key-statement revoke committed", self.log(b))
            late = self.post(b, self.carrier(self.principal_file, new,
                                             self.ordinary("<late@keys.invalid>"), "late"))
            witness("after-revocation POST", late.strip())
            self.assertTrue(late.startswith(b"441 "), late)
        finally:
            self.stop(b)
        history = self.history(b)
        witness("history", history)
        self.assertEqual(history, [
            "generation=3 state=revoked principal=" + P.hex(),
            "generation=2 state=retired principal=" + P.hex(),
            "generation=1 state=retired principal=" + P.hex()])
        witness("log", [line for line in self.log(b).splitlines() if "key-statement" in line])

    def test_kill_at_the_cut_and_recovery_at_open(self):
        c = self.node("c")
        self.start(c)
        try:
            self.enrol_and_grant(c)
        finally:
            self.stop(c)
        env = dict(self.env)
        env["FN_NATIVE_KEY_STATEMENT_FAULT"] = "statement-committed:kill"
        proc = self.start(c, env)
        old, new = self.keys["old"], self.keys["new"]
        statement = self.carrier(self.principal_file, old,
                                 self.succession("<cut@keys.invalid>", P, old, new), "cut")
        reply = self.post(c, statement, expect_reply=False)
        proc.wait(timeout=60)
        witness("cut POST reply", reply, "owner exit", proc.returncode)
        self.assertEqual(proc.returncode, -9)
        self.assertNotIn("key-statement", self.log(c))
        # The statement is durable; its key change is not.
        cut_history = self.history(c)
        witness("history at the cut", cut_history)
        self.assertEqual(cut_history, ["generation=1 state=active principal=" + P.hex()])
        # The open's recovery executes the newest record.
        self.start(c)
        self.stop(c)
        lines = [line for line in self.log(c).splitlines() if "key-statement" in line]
        witness("log after recovery", lines)
        self.assertEqual(lines, ["key-statement enrol-successor committed at-open"])
        recovered = self.history(c)
        witness("history after recovery", recovered)
        self.assertEqual(recovered, ["generation=2 state=active principal=" + P.hex(),
                                     "generation=1 state=retired principal=" + P.hex()])
        # A second open: the newest record is the key change; nothing runs.
        self.start(c)
        self.stop(c)
        lines = [line for line in self.log(c).splitlines() if "key-statement" in line]
        self.assertEqual(lines, ["key-statement enrol-successor committed at-open"])
        self.assertEqual(self.history(c), recovered)
        witness("second open: unchanged")

    def test_a_decline_across_a_restart_with_a_grant_added(self):
        """Packet 7 (PRF-124): a statement that declined for want of a `keys'
        grant, then a grant added live, then a restart.  Under the recorded
        disposition (books/key-statements.lisp fn-ks-statement-rows, no
        policy switch) the open decides the statement under the grants in
        force at its txid and it declines again; under the pre-packet
        behaviour the open's live grant made it act.  FN_KS_REOPEN_EXPECT=acts
        runs the trace against a pre-packet image (the old behaviour is not a
        supported configuration; its model is the counterexample fixture in
        tests/acl2/key-statements-tests.lisp)."""
        expect = os.environ.get("FN_KS_REOPEN_EXPECT", "declines")
        d = self.node("d")
        self.start(d)
        try:
            old = self.keys["old"]
            self.fn("hybrid-enroll", d["control"], "1", self.principal_file,
                    old["ed_public"], old["ml_public"])
            new = self.keys["new"]
            statement = self.carrier(self.principal_file, old,
                                     self.succession("<declined@keys.invalid>", P, old, new),
                                     "declined")
            reply = self.post(d, statement)
            witness("statement POST without a grant", reply.strip())
            self.assertTrue(reply.startswith(b"240 "), reply)
            declined = [line for line in self.log(d).splitlines() if "key-statement" in line]
            witness("log at acceptance", declined)
            self.assertEqual(len(declined), 1)
            self.assertIn("key-statement declined", declined[0])
            # The grant the statement lacked, added live after it.
            self.fn("operator", d["config"], "control", "grant", P.hex(), "keys", "fn.keys")
        finally:
            self.stop(d)
        self.assertEqual(self.history(d), ["generation=1 state=active principal=" + P.hex()])
        self.start(d)
        self.stop(d)
        lines = [line for line in self.log(d).splitlines() if "key-statement" in line]
        history = self.history(d)
        witness("log after the restart", lines)
        witness("history after the restart", history)
        if expect == "acts":
            self.assertEqual(lines[1:], ["key-statement enrol-successor committed at-open"])
            self.assertEqual(history, ["generation=2 state=active principal=" + P.hex(),
                                       "generation=1 state=retired principal=" + P.hex()])
        else:
            self.assertEqual(len(lines), 2)
            self.assertTrue(lines[1].startswith("key-statement declined")
                            and lines[1].endswith(" at-open"), lines)
            self.assertEqual(history, ["generation=1 state=active principal=" + P.hex()])
            # And again: the disposition is a function of durable records.
            self.start(d)
            self.stop(d)
            again = [line for line in self.log(d).splitlines() if "key-statement" in line]
            witness("log after a second restart", again)
            self.assertEqual(again[2:], [lines[1]])
            self.assertEqual(self.history(d), history)

    def test_an_accepted_statement_cut_then_its_grant_revoked(self):
        """PRF-140 (books/key-statements.lisp
        fn-ks-accepted-statement-finishes-under-its-admission-context): a
        succession accepted under a `keys' grant, the process killed at the
        cut (statement durable, key change not), the grant revoked while the
        node is down, a restart.  The open finishes the change under the
        configuration at the statement's txid (the grant), not today's (no
        grant): `enrol-successor committed at-open'."""
        e = self.node("e")
        self.start(e)
        try:
            self.enrol_and_grant(e)
        finally:
            self.stop(e)
        env = dict(self.env)
        env["FN_NATIVE_KEY_STATEMENT_FAULT"] = "statement-committed:kill"
        proc = self.start(e, env)
        old, new = self.keys["old"], self.keys["new"]
        statement = self.carrier(self.principal_file, old,
                                 self.succession("<admitted@keys.invalid>", P, old, new),
                                 "admitted")
        reply = self.post(e, statement, expect_reply=False)
        proc.wait(timeout=60)
        witness("cut POST reply", reply, "owner exit", proc.returncode)
        self.assertEqual(proc.returncode, -9)
        self.assertNotIn("key-statement", self.log(e))
        self.assertEqual(self.history(e), ["generation=1 state=active principal=" + P.hex()])
        # Today's configuration: the grant the statement was accepted under
        # is revoked (a configuration record later than the statement),
        # offline.  The killed owner left its control socket behind, and the
        # operator hands a plan to a socket it finds (refused: nobody
        # listens), so the harness removes the dead owner's socket first
        # (recorded in planning/evidence/key-replay-fixture-2026-09-26.md).
        self.assertTrue(e["control"].is_socket())
        e["control"].unlink()
        self.fn("operator", e["config"], "control", "revoke", P.hex(), "keys", "fn.keys")
        listing = self.fn("operator", e["config"], "control", "list")
        witness("control list after the revoke", listing.stdout.decode("utf-8", "replace").strip())
        self.start(e)
        self.stop(e)
        lines = [line for line in self.log(e).splitlines() if "key-statement" in line]
        history = self.history(e)
        witness("log after the restart", lines)
        witness("history after the restart", history)
        self.assertEqual(lines, ["key-statement enrol-successor committed at-open"])
        self.assertEqual(history, ["generation=2 state=active principal=" + P.hex(),
                                   "generation=1 state=retired principal=" + P.hex()])
        # A second open: the change is the newest record; nothing runs, and
        # today's missing grant never undoes or re-decides it.
        self.start(e)
        self.stop(e)
        again = [line for line in self.log(e).splitlines() if "key-statement" in line]
        witness("log after a second restart", again)
        self.assertEqual(again, lines)
        self.assertEqual(self.history(e), history)


if __name__ == "__main__":
    unittest.main()

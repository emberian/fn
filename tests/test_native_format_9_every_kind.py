"""Format 9 -> 10 for every record kind a format-9 node writes (SCN-190,
PRF-355; lane format10-import).

Opt-in: FN_FORMAT9_HOST names a format-9 DEVELOPER image (the release before
format 10), FN_NATIVE_DEVELOPER_HOST the format-10 image under test,
FN_TEST_OPENSSL an OpenSSL 3.5 (ML-DSA-65 test keys).

test_every_translatable_kind: the format-9 image builds a store through its
public surfaces holding every kind it writes -- plain articles (served POST),
keyring snapshots (hybrid-enroll; a key statement's succession and its
revocation), verified signed composites (the succession and revocation
statements, an article under the successor keys), a D23 carried composite
(IHAVE from a peer whose boundary carries an unenrolled principal), a revoked
composite (transit after the revocation), consumer events (register, which
bootstraps) and the topic administrator's install -- and exports it.  The
format-10 image imports the archive and:

* every record's octets are the archive's, except the content identities,
  which are checked here by an independent computation (tools/blake3_ref.py,
  books/identity.lisp's profile): an article's two identities; a composite's
  content subject, its embedded article's two identities and its
  authored-source identity; keyring, consumer and topic-install records are
  byte-identical (STO-028's definition, per kind);
* what the kinds assert is served the same: `HDR :fn-verified' of each
  signed article (verified / carried / revoked, the principal and keyring
  generation) and `hybrid-key-history' are equal before and after.

test_a_topic_anchor_is_refused_by_name: a format-9 store holding a topic
anchor (the format-9 fixtures under tests/fixtures/topic-history-format-9/)
exports, and the format-10 import refuses it
`reason=record-translation signed-format-9-identity sequence=N`, exit 1, with
no store published at the target.
"""
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import blake3_ref  # noqa: E402
from tests.native_process import wait_for_announcement, stop_and_diagnostics  # noqa: E402
from tests.test_native_format_9_migration import (  # noqa: E402
    cbor_items, expected_identities, identity, SUBJECT)
from tests.test_native_key_statements import (  # noqa: E402
    P, Q, ED_OLD, ED_NEW, ED_Q, POP_TAG, free_port, hex_lines)
from tools.wire_stream import whole_stream  # noqa: E402
import socket  # noqa: E402

F9 = os.environ.get("FN_FORMAT9_HOST")
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
READY = bool(F9 and Path(F9).is_file() and IMAGE.is_file())
TOPIC9 = ROOT / "tests" / "fixtures" / "topic-history-format-9"
TOPIC = ROOT / "tests" / "fixtures" / "topic-history"
TOPIC_ED_PUBLIC = bytes.fromhex(ED_OLD[1])
TOPIC_ED_SECRET = bytes.fromhex(ED_OLD[0] + ED_OLD[1])


def witness(*words):
    print("NATIVE-F9-EVERY-KIND-WITNESS", *words, flush=True)


def source_id(source):
    """The raw subject identity of an authored source (fn-hsig-authored-source-id)."""
    import struct
    return bytes.fromhex(identity(SUBJECT, SUBJECT + b"\x00" + struct.pack(">I", len(source))
                                  + source).decode())


@unittest.skipUnless(READY, "set FN_FORMAT9_HOST (a format-9 developer image) and a format-10 "
                     "FN_NATIVE_DEVELOPER_HOST")
class FormatNineEveryKindTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-f9-every-kind-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_NATIVE_KEY_STATEMENT_FAULT", None)
        self.image = Path(F9)

    # -- processes ------------------------------------------------------------
    def run_image(self, image, *args, expected=None, timeout=600):
        r = subprocess.run([str(image), "--fn", *map(str, args)], cwd=ROOT, env=self.env,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
        out = (r.stdout + r.stderr).decode("utf-8", "replace")
        if expected is not None:
            self.assertEqual(r.returncode, expected, "{} {} -> {}\n{}".format(
                Path(image).name, args, r.returncode, out[-3000:]))
        return r.returncode, out, r.stdout

    def fn(self, *args, expected=0):
        return self.run_image(self.image, *args, expected=expected)

    def write(self, name, octets):
        path = self.tmp / name
        path.write_bytes(octets)
        return path

    def openssl(self, *args):
        r = subprocess.run([OPENSSL, *map(str, args)], stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, check=True)
        return r.stdout

    def key_set(self, name, seed, public):
        ml_private = self.tmp / (name + "-ml.pem")
        ml_public = self.tmp / (name + "-ml.pub.pem")
        self.openssl("genpkey", "-algorithm", "ML-DSA-65", "-out", ml_private)
        self.openssl("pkey", "-in", ml_private, "-pubout", "-out", ml_public)
        der = self.openssl("pkey", "-pubin", "-in", ml_public, "-outform", "DER")
        return {"ed_public": self.write(name + "-ed.pub", bytes.fromhex(public)),
                "ed_secret": self.write(name + "-ed.sec", bytes.fromhex(seed + public)),
                "ed_raw": bytes.fromhex(public), "ml_private": ml_private,
                "ml_public": ml_public, "ml_raw": der[-1952:]}

    def node(self, name, groups):
        root = self.tmp / name
        root.mkdir()
        store = root / "store"
        self.fn("store", store, "init", *groups)
        node = {"root": root, "store": store, "port": free_port(),
                "control": root / "control.sock", "log": root / "service.log",
                "config": root / "fn.toml"}
        self.write_config(node, store)
        return node

    @staticmethod
    def write_config(node, store):
        node["config"].write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                store, node["port"], node["control"], node["log"]), encoding="ascii")

    def start(self, node):
        proc = subprocess.Popen([str(self.image), "--fn", "operator", str(node["config"]), "run"],
                                cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        wait_for_announcement(proc, b"LISTENING ", timeout=180)
        node["process"] = proc

    def stop(self, node):
        diagnostic = stop_and_diagnostics(node["process"], timeout=60)
        self.assertEqual(node["process"].returncode, 0, diagnostic)

    def live_log(self, node, needle, timeout=30):
        deadline = time.monotonic() + timeout
        while True:
            text = node["log"].read_text("utf-8", "replace") if node["log"].exists() else ""
            if needle in text or time.monotonic() > deadline:
                return text
            time.sleep(0.05)

    # -- articles -------------------------------------------------------------
    def carrier(self, principal_file, keys, source, stem):
        out = self.tmp / (stem + ".carrier")
        self.fn("hybrid-sign-carrier", principal_file, keys["ed_public"], keys["ed_secret"],
                keys["ml_public"], keys["ml_private"], self.write(stem + ".src", source), out)
        return out.read_bytes()

    @staticmethod
    def header(msgid, group, subject):
        return ("From: keys@example.invalid\r\nDate: Fri, 25 Sep 2026 12:00:00 +0000\r\n"
                "Newsgroups: {}\r\nSubject: {}\r\nMessage-ID: {}\r\n\r\n".format(
                    group, subject, msgid)).encode("ascii")

    def succession(self, msgid, old, new):
        pop_source = POP_TAG + b"\n" + msgid.encode("ascii") + b"\n" + old["ed_raw"]
        _, _, stdout = self.fn("hybrid-sign", self.p_file, new["ed_public"], new["ed_secret"],
                               new["ml_public"], new["ml_private"],
                               self.write("pop.src", pop_source))
        sigs = dict(line.split() for line in stdout.decode().splitlines())
        return (self.header(msgid, "fn.keys", "fn-key-statement")
                + b"FN-Key-Statement: succession-v1\r\n"
                + hex_lines("FN-Key-Principal", P)
                + hex_lines("FN-Key-Old-Ed25519", old["ed_raw"])
                + hex_lines("FN-Key-New-Ed25519", new["ed_raw"])
                + hex_lines("FN-Key-New-ML-DSA-65", new["ml_raw"])
                + hex_lines("FN-Key-PoP-Ed25519", bytes.fromhex(sigs["ed25519"]))
                + hex_lines("FN-Key-PoP-ML-DSA-65", bytes.fromhex(sigs["ml-dsa-65"])))

    def revocation(self, msgid, principal):
        return (self.header(msgid, "fn.keys", "fn-key-statement")
                + b"FN-Key-Statement: revocation-v1\r\n" + hex_lines("FN-Key-Principal", principal))

    def ordinary(self, msgid):
        return self.header(msgid, "fn.test", "ordinary") + b"body\r\n"

    def nntp(self, node, command, article=None):
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=60) as sock:
            stream = whole_stream(sock)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(command + b"\r\n")
            first = stream.readline()
            if article is None:
                lines = [first]
                if first[:3] in (b"225",):
                    while True:
                        line = stream.readline()
                        if line in (b".\r\n", b""):
                            break
                        lines.append(line)
                return lines
            self.assertTrue(first[:3] in (b"340", b"335"), first)
            for line in article.splitlines(keepends=True):
                stream.write(b"." + line if line.startswith(b".") else line)
            stream.write(b".\r\n")
            return stream.readline()

    def post(self, node, article):
        return self.nntp(node, b"POST", article)

    def ihave(self, node, msgid, article):
        return self.nntp(node, b"IHAVE " + msgid.encode("ascii"), article)

    def verified(self, node, msgids):
        return {m: b"".join(self.nntp(node, b"HDR :fn-verified " + m.encode("ascii")))
                for m in msgids}

    def archive_records(self, archive):
        names = sorted(p.name for p in (archive / "records").iterdir())
        return names, [(archive / "records" / n).read_bytes() for n in names]

    # -- the case -------------------------------------------------------------
    def test_every_translatable_kind(self):
        self.p_file = self.write("principal-p.bin", P)
        q_file = self.write("principal-q.bin", Q)
        old = self.key_set("old", *ED_OLD)
        new = self.key_set("new", *ED_NEW)
        q = self.key_set("q", *ED_Q)
        b = self.node("b", ("fn.test", "fn.keys"))
        self.fn("operator", b["config"], "peer", "add", "a", "a.example.invalid",
                "127.0.0.1", str(free_port()), "fn.*", "-", "source-address", "127.0.0.1",
                "true", "carries", Q.hex())
        self.fn("operator", b["config"], "peer", "budget", "a", "1048576", "16")
        signed = []
        self.start(b)
        try:
            self.fn("hybrid-enroll", b["control"], "1", self.p_file, old["ed_public"],
                    old["ml_public"])
            self.fn("operator", b["config"], "control", "grant", P.hex(), "keys", "fn.keys")
            reply = self.post(b, self.ordinary("<plain@f9.invalid>"))
            self.assertTrue(reply.startswith(b"240 "), reply)
            reply = self.post(b, self.carrier(self.p_file, old,
                                              self.succession("<succession@f9.invalid>", old, new),
                                              "succession"))
            self.assertTrue(reply.startswith(b"240 "), reply)
            self.assertIn("key-statement enrol-successor committed",
                          self.live_log(b, "key-statement enrol-successor committed"))
            reply = self.post(b, self.carrier(self.p_file, new, self.ordinary("<new-key@f9.invalid>"),
                                              "newart"))
            self.assertTrue(reply.startswith(b"240 "), reply)
            carried = (b"Path: a.example.invalid!not-for-mail\r\n"
                       + self.carrier(q_file, q, self.revocation("<carried@f9.invalid>", Q),
                                      "carried"))
            reply = self.ihave(b, "<carried@f9.invalid>", carried)
            self.assertTrue(reply.startswith(b"235 "), reply)
            reply = self.post(b, self.carrier(self.p_file, new,
                                              self.revocation("<revocation@f9.invalid>", P),
                                              "revocation"))
            self.assertTrue(reply.startswith(b"240 "), reply)
            self.assertIn("key-statement revoke committed",
                          self.live_log(b, "key-statement revoke committed"))
            relayed = (b"Path: a.example.invalid!not-for-mail\r\n"
                       + self.carrier(self.p_file, new, self.ordinary("<revoked@f9.invalid>"),
                                      "revokedtransit"))
            reply = self.ihave(b, "<revoked@f9.invalid>", relayed)
            self.assertTrue(reply.startswith(b"235 "), reply)
            signed = ["<succession@f9.invalid>", "<new-key@f9.invalid>", "<carried@f9.invalid>",
                      "<revocation@f9.invalid>", "<revoked@f9.invalid>"]
            served9 = self.verified(b, signed)
            # Consumer events: register bootstraps the consumer history.
            rc, out, _ = self.run_image(self.image, "consumer", "register", b["control"],
                                        "worker", "fn.test", self.tmp / "worker.token")
            self.assertEqual(rc, 0, out)
            # The topic administrator's install.
            rc, out, _ = self.run_image(self.image, "topic", "install", b["control"])
            self.assertEqual(rc, 0, out)
        finally:
            self.stop(b)
        witness("served format 9", served9)
        history9 = self.fn("hybrid-key-history", b["store"])[1]
        a9 = self.tmp / "archive-9"
        self.fn("operator", b["config"], "store", "export", a9)

        # Format 10 imports it.
        self.image = IMAGE
        c = {"root": self.tmp / "c", "port": free_port()}
        c["root"].mkdir()
        c.update(store=c["root"] / "store", control=c["root"] / "control.sock",
                 log=c["root"] / "service.log", config=c["root"] / "fn.toml")
        self.write_config(c, c["store"])
        rc, out, _ = self.run_image(IMAGE, "operator", c["config"], "store", "import", a9)
        witness("import", rc, out.strip()[-400:])
        self.assertEqual(rc, 0, out)
        self.assertNotIn("Guard-checking", out)
        # The node secret is not in the archive (it keys the posting-account
        # value): a migration creates a new one (or copies the old file).
        self.fn("store", c["store"], "node-secret", "create")
        history10 = self.fn("hybrid-key-history", c["store"])[1]
        self.assertEqual(history10, history9)
        self.assertEqual(len(history9.splitlines()), 3, history9)
        self.start(c)
        try:
            served10 = self.verified(c, signed)
        finally:
            self.stop(c)
        witness("served format 10", served10)
        self.assertEqual(served10, served9)

        # Per kind, against an independent computation.
        a10 = self.tmp / "archive-10"
        self.fn("operator", c["config"], "store", "export", a10)
        names9, records9 = self.archive_records(a9)
        names10, records10 = self.archive_records(a10)
        self.assertEqual(names10, names9)
        kinds = {}
        for old_octets, new_octets in zip(records9, records10):
            it9, it10 = cbor_items(old_octets), cbor_items(new_octets)
            kind = self.check_record(it9, it10, old_octets, new_octets)
            kinds[kind] = kinds.get(kind, 0) + 1
        witness("kinds", sorted(kinds.items()))
        for kind in ("article", "composite-verified", "composite-carried", "keyring",
                     "consumer", "topic-install"):
            self.assertIn(kind, kinds, kinds)
        self.assertGreaterEqual(kinds["keyring"], 3, kinds)

    def check_article(self, it9, it10):
        self.assertEqual(len(it9), len(it10))
        end = 8 + it9[7][1]
        o, s = expected_identities(it9[5][1], it9[6][1])
        self.assertEqual(it10[end], ("b", o))
        self.assertEqual(it10[end + 1], ("b", s))
        keep = [i for i in range(len(it9)) if i not in (end, end + 1)]
        self.assertEqual([it9[i] for i in keep], [it10[i] for i in keep])
        return s

    def check_record(self, it9, it10, old, new):
        if it9[0] == ("b", b"fn-r"):
            self.check_article(it9, it10)
            return "article"
        if it9[0] == ("b", b"fn-e") and it9[2] == ("u", 4):
            # The accepted composite (books/stx-accept-records.lisp items):
            # 8 content subject, 9 article record, 10 verdict, [11 source,
            # 12 authored id].
            self.assertEqual(len(it9), len(it10))
            s = self.check_article(cbor_items(it9[9][1]), cbor_items(it10[9][1]))
            self.assertEqual(it10[8], ("b", s))
            keep = [i for i in range(len(it9)) if i not in (8, 9, 12)]
            self.assertEqual([it9[i] for i in keep], [it10[i] for i in keep])
            if len(it9) == 13:
                self.assertEqual(it10[12], ("b", source_id(it9[11][1])))
                return "composite-carried" if it9[6] == ("u", 0) else "composite-verified"
            return "composite-legacy"
        self.assertEqual(old, new)
        if it9[0] == ("b", b"fn-e"):
            return {2: "verdict", 3: "keyring"}.get(it9[2][1], "fn-e-%d" % it9[2][1])
        if it9[0] == ("b", b"fnce"):
            return "consumer"
        if it9[0] == ("b", b"fnto"):
            return "topic-install"
        return "other"

    def test_a_topic_anchor_is_refused_by_name(self):
        principal = self.write("principal.bin", bytes([85]) * 32)
        ed_public = self.write("topic-ed.pub", TOPIC_ED_PUBLIC)
        ed_secret = self.write("topic-ed.sec", TOPIC_ED_SECRET)
        ml_public = TOPIC / "ml-dsa-65-test-public.pem"
        ml_private = TOPIC / "ml-dsa-65-test-private.pem"
        t = self.node("t", ("fn.test",))
        self.start(t)
        try:
            self.fn("hybrid-enroll", t["control"], "1", principal, ed_public, ml_public)
            _, _, stdout = self.fn("hybrid-sign", principal, ed_public, ed_secret, ml_public,
                                   ml_private, TOPIC9 / "matched-root.source")
            parts = dict(line.split() for line in stdout.decode().splitlines())
            self.fn("hybrid-author", t["control"], "1", TOPIC9 / "matched-root.source",
                    self.write("root.ed.sig", bytes.fromhex(parts["ed25519"])),
                    self.write("root.ml.sig", bytes.fromhex(parts["ml-dsa-65"])), ml_public)
            self.fn("topic", "install", t["control"])
            _, out, _ = self.fn("topic", "anchor", t["control"], "1", "1")
            self.assertIn("topic accepted", out)
        finally:
            self.stop(t)
        a9 = self.tmp / "archive-t9"
        self.fn("operator", t["config"], "store", "export", a9)
        names, records = self.archive_records(a9)
        anchors = [n for n, r in zip(names, records)
                   if cbor_items(r)[0] == ("b", b"fnto") and cbor_items(r)[2] == ("u", 0)]
        self.assertEqual(len(anchors), 1, names)
        self.image = IMAGE
        d = {"root": self.tmp / "d", "port": free_port()}
        d["root"].mkdir()
        d.update(store=d["root"] / "store", control=d["root"] / "control.sock",
                 log=d["root"] / "service.log", config=d["root"] / "fn.toml")
        self.write_config(d, d["store"])
        rc, out, _ = self.run_image(IMAGE, "operator", d["config"], "store", "import", a9)
        witness("topic import", rc, out.strip()[-400:])
        self.assertEqual(rc, 1, out)
        match = re.search(r"reason=record-translation signed-format-9-identity sequence=(\d+)",
                          out)
        self.assertIsNotNone(match, out)
        self.assertFalse(d["store"].exists())
        self.assertEqual([p.name for p in d["root"].iterdir() if p.name.startswith("store")], [])


if __name__ == "__main__":
    unittest.main()

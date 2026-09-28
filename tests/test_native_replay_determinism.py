"""Replay determinism: the owner's state is a function of the log (lane proto-determinism).

fn is event-sourced: the record log (and the config/ records) is the truth,
and an open folds it into the owner's state.  If that fold is deterministic,
the state after a log prefix is a function of the prefix, and anyone holding
the log can recompute and check a snapshot (a peer catching up, a bisect for
the event that broke an invariant, a bug reproduced by replay).  This module
makes that a test, over a store built by a mixed workload (NNTP POSTs with and
without a Message-ID, cross-posts, operator posts, an operator withdrawal and
the cancel the node injects for it, group create/describe, motd, retention and
capacity configuration, an account invitation, consumer bootstrap/register/
ack, and -- when FN_TEST_OPENSSL makes ML-DSA-65 keys -- a hybrid key
enrollment and a signed post), and over the registered fixture n1k-2k
(test f: a reclaim is reproduced from its recorded instant, PKT-857):

(a) `store ROOT digest' (ACL2's digest of the folded state's LOGICAL value,
    books/state-digest.lisp; host/store-node-host.lisp
    fn-store-sn-replay-digest-report) prints the same lines for two copies of the
    store, each opened by full replay in its own process, twice;
(b) `store ROOT checkpoint' on each copy writes byte-identical checkpoint
    files, and the digest of the open from that checkpoint equals the digest
    of the full replay (fn-sco-store-open-of-extended-capture);
(c) the served view (LIST ACTIVE, LIST NEWSGROUPS, and per group GROUP, OVER,
    ARTICLE and HEAD by number for every article) is the same octets from an
    owner on each copy.

Two boxes: with FN_DETERMINISM_EXPORT=DIR the mixed store (a tar) and the
digest lines are written to DIR; with FN_DETERMINISM_EXPECT=DIR a run on
another box (the same image) opens that tar and compares its digest lines with
the exported ones (planning/evidence/proto-determinism-2026-09-27.md).
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest

from tests.native_harness import Client, Node, class_case, environment, native_image, run

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
FIXTURES = Path(os.environ.get("FN_DETERMINISM_FIXTURES", "/tank/fn/scratch/fixtures"))
FIXTURE = os.environ.get("FN_DETERMINISM_FIXTURE", "n1k-2k")
EXPORT = os.environ.get("FN_DETERMINISM_EXPORT")
EXPECT = os.environ.get("FN_DETERMINISM_EXPECT")
TIMEOUT = int(os.environ.get("FN_DETERMINISM_TIMEOUT", "900"))


def article(msgid, groups, subject, body, extra=b""):
    head = b"From: det@example.invalid\r\nNewsgroups: " + groups.encode("ascii") + b"\r\n"
    head += b"Subject: " + subject.encode("ascii") + b"\r\n"
    if msgid:
        head += b"Message-ID: " + msgid.encode("ascii") + b"\r\n"
    return head + extra + b"\r\n" + body


MULTI = (b"215", b"220", b"221", b"222", b"224", b"225", b"230", b"231", b"101")


def exchange(client, line):
    """The reply to LINE, a multi-line block included, as the octets sent."""
    status = exchange(client, line)
    out = [status]
    if status[:3] in MULTI:
        while True:
            ln = client.line()
            out.append(ln)
            if ln == b".\r\n":
                break
    return b"".join(out)


def post(client, data):
    """The final POST reply, or the first when it was not 340."""
    first, final = post(client, data)
    return first if final is None else final


def node_at(case, store, root):
    """A node serving STORE (anywhere) from the scratch tree ROOT."""
    node = Node(case, IMAGE, root=root)
    node.store_path = store
    node.write_config()
    return node


def digest_lines(stdout):
    """The digest lines and the open line of `store ROOT digest'."""
    lines = stdout.splitlines()
    digests = [ln for ln in lines if ln.startswith("digest ")]
    opens = [ln for ln in lines if ln.startswith("open=")]
    return digests, opens


def cross_box(name, value):
    """With FN_DETERMINISM_EXPORT, write VALUE (a hex digest) as NAME; with
    FN_DETERMINISM_EXPECT, answer the value the other box wrote (or None)."""
    if EXPORT:
        Path(EXPORT).mkdir(parents=True, exist_ok=True)
        (Path(EXPORT) / name).write_text(value + "\n", encoding="ascii")
    if EXPECT and (Path(EXPECT) / name).exists():
        return (Path(EXPECT) / name).read_text(encoding="ascii").strip()
    return None


def differing(a, b):
    return [(x, y) for x, y in zip(a, b) if x != y] + (
        [("<length>", "{} vs {}".format(len(a), len(b)))] if len(a) != len(b) else [])


@unittest.skipUnless(IMAGE.exists(), "build/fn-host-developer is required")
class NativeReplayDeterminismTests(unittest.TestCase):
    """One mixed store, built once; each test copies it."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="fn-determinism-")
        cls.base = Path(cls.temporary.name)
        cls.env = environment()
        cls.workload = []
        if EXPECT:
            with tarfile.open(Path(EXPECT) / "mixed-store.tar") as tar:
                tar.extractall(cls.base / "imported", filter="tar")
            cls.store = cls.base / "imported" / "store"
        else:
            cls.store = cls.build_mixed_store()

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    # -- process helpers ----------------------------------------------------

    @classmethod
    def run_native(cls, *args, expected=0, env=None):
        result = run([IMAGE, "--fn", *args], env=env or cls.env, timeout=TIMEOUT)
        if expected is not None and result.returncode != expected:
            raise AssertionError("native {} returned {}\nstdout={}\nstderr={}".format(
                args, result.returncode, result.stdout.decode("utf-8", "replace"),
                result.stderr.decode("utf-8", "replace")))
        return result

    @classmethod
    def step(cls, label, result):
        """Record one workload step and whether it was accepted (a native
        call's exit code, with its last stderr line when it is not 0)."""
        if isinstance(result, subprocess.CompletedProcess):
            tail = result.stderr.decode("utf-8", "replace").strip().splitlines()[-1:]
            result = result.returncode if result.returncode == 0 else [result.returncode] + tail
        cls.workload.append((label, result))

    # -- the mixed workload -------------------------------------------------

    @classmethod
    def build_mixed_store(cls):
        node = Node(class_case(cls), IMAGE, root=cls.base / "mixed")
        store, config, port, control = node.store_path, node.config, node.port, node.control
        cls.run_native("operator", config, "init", "fn.letters", "fn.test", "control.cancel")
        node.start(timeout=TIMEOUT)
        try:
            client = Client(port, timeout=120, greeting=None)
            try:
                for i in range(12):
                    groups = ("fn.test", "fn.letters", "fn.test,fn.letters")[i % 3]
                    reply = post(client, article("<det-{}@example.invalid>".format(i), groups,
                                                "det {}".format(i),
                                                "body {}\r\n.dot line\r\n".format(i).encode() * (1 + i)))
                    cls.step("nntp post {}".format(i), reply[:3].decode())
                # RFC 8315: a post with a Cancel-Lock, then its cancel by key.
                key = base64.b64encode(hashlib.sha256(b"det secret").digest()).decode("ascii")
                lock = base64.b64encode(hashlib.sha256(key.encode("ascii")).digest()).decode("ascii")
                cls.step("nntp post locked", post(client, article(
                    "<det-locked@example.invalid>", "fn.test", "locked", b"locked\r\n",
                    extra=("Cancel-Lock: sha256:" + lock + "\r\n").encode("ascii")))[:3].decode())
                cls.step("nntp cancel by key", post(client, article(
                    "<det-cancel@example.invalid>", "fn.test",
                    "cmsg cancel <det-locked@example.invalid>", b"cancel\r\n",
                    extra=("Control: cancel <det-locked@example.invalid>\r\n"
                           "Cancel-Key: sha256:" + key + "\r\n").encode("ascii")))[:3].decode())
                # No Message-ID: the node generates one (a recorded value).
                cls.step("nntp post generated-id",
                         post(client, article(None, "fn.test", "generated", b"no id\r\n"))[:3].decode())
            finally:
                client.close()
            for i in range(2):
                payload = cls.base / "operator-{}.eml".format(i)
                payload.write_bytes(article("<det-op-{}@example.invalid>".format(i), "fn.letters",
                                            "operator {}".format(i), b"operator body\r\n",
                                            extra=b"Date: Thu, 24 Sep 2026 12:00:00 +0000\r\n"))
                cls.step("operator post {}".format(i), cls.run_native(
                    "operator", config, "post", "--message-id",
                    "<det-op-{}@example.invalid>".format(i), "--payload", payload,
                    "--group", "fn.letters", expected=None))
            for label, words in (
                    ("withdraw", ("article", "withdraw", "<det-4@example.invalid>",
                                  "--reason", "determinism")),
                    ("group create", ("group", "create", "fn.extra")),
                    ("group describe", ("group", "describe", "fn.extra", "an", "extra", "group")),
                    ("motd", ("motd", "set", "determinism", "motd")),
                    ("retention", ("retention", "set", "release-after", "30")),
                    ("capacity", ("capacity", "4000000000")),
                    ("account invite", ("account", "invite"))):
                cls.step(label, cls.run_native("operator", config, *words, expected=None))
            for label, words in (
                    ("consumer bootstrap", ("consumer", "bootstrap", control)),
                    ("consumer register", ("consumer", "register", control, "worker", "fn.test",
                                           cls.base / "worker.fncu")),
                    ("consumer ack", ("consumer", "ack", control, cls.base / "worker.fncu"))):
                cls.step(label, cls.run_native(*words, expected=None))
            cls.hybrid(control)
            client = Client(port, timeout=120, greeting=None)
            try:
                for i in range(3):
                    reply = post(client, article("<det-extra-{}@example.invalid>".format(i),
                                                "fn.extra,fn.test", "extra {}".format(i),
                                                b"after the reconfiguration\r\n"))
                    cls.step("nntp post extra {}".format(i), reply[:3].decode())
            finally:
                client.close()
        finally:
            node.stop(grace=120)
        return store

    @classmethod
    def hybrid(cls, control):
        """A hybrid key enrollment (a key statement) and a signed post, when
        FN_TEST_OPENSSL can make ML-DSA-65 keys."""
        openssl = os.environ.get("FN_TEST_OPENSSL")
        if not openssl:
            cls.step("hybrid", "skipped: FN_TEST_OPENSSL unset")
            return
        d = cls.base / "hybrid"
        d.mkdir()
        principal, ed_public, ed_secret = d / "principal.bin", d / "ed-public.bin", d / "ed-secret.bin"
        ml_private, ml_public = d / "ml-private.pem", d / "ml-public.pem"
        principal.write_bytes(bytes([85]) * 32)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        for words in (["genpkey", "-algorithm", "ML-DSA-65", "-out", str(ml_private)],
                      ["pkey", "-in", str(ml_private), "-pubout", "-out", str(ml_public)]):
            made = subprocess.run([openssl, *words], env=cls.env, capture_output=True,
                                  timeout=60, check=False)
            if made.returncode != 0:
                cls.step("hybrid", "skipped: openssl " + words[0] + " failed")
                return
        source = article("<det-signed@example.invalid>", "fn.test", "signed", b"signed body\r\n",
                         extra=b"Date: Fri, 25 Sep 2026 12:00:00 +0000\r\n")
        authored = d / "authored.eml"
        authored.write_bytes(source)
        cls.step("hybrid enroll", cls.run_native("hybrid-enroll", control, "1", principal,
                                                 ed_public, ml_public, expected=None))
        signed = cls.run_native("hybrid-sign", principal, ed_public, ed_secret, ml_public,
                                ml_private, authored, expected=None)
        if signed.returncode != 0:
            cls.step("hybrid sign", signed)
            return
        parts = dict(line.split() for line in signed.stdout.decode("ascii").splitlines())
        (d / "ed.sig").write_bytes(bytes.fromhex(parts["ed25519"]))
        (d / "ml.sig").write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        cls.step("hybrid author", cls.run_native("hybrid-author", control, "1", authored,
                                                 d / "ed.sig", d / "ml.sig", ml_public,
                                                 expected=None))

    # -- the comparisons ----------------------------------------------------

    def copy(self, source, name):
        dest = self.base / "copies" / name
        if dest.exists():
            shutil.rmtree(dest)
        shutil.copytree(source, dest, symlinks=True,
                        ignore=shutil.ignore_patterns("*.sock"))
        # A copy is on (possibly) another filesystem: record it (PKT-579).
        self.run_native("store", dest, "rebind-filesystem")
        return dest

    def digest(self, store):
        out = self.run_native("store", store, "digest").stdout.decode("ascii")
        digests, opens = digest_lines(out)
        self.assertTrue(any(ln.startswith("digest state ") for ln in digests), out)
        return digests, opens

    def assert_same(self, a, b, what):
        self.assertEqual(a, b, "{} differ: {}".format(what, differing(a, b)))

    def replays_identically(self, source, label):
        one, two = self.copy(source, label + "-a"), self.copy(source, label + "-b")
        first, opens1 = self.digest(one)
        again, _ = self.digest(one)
        other, opens2 = self.digest(two)
        self.assertTrue(opens1 and opens1[0].startswith("open=full-replay"), opens1)
        self.assert_same(first, again, label + ": two processes over one copy")
        self.assert_same(first, other, label + ": two copies")
        return first, one, two

    def test_a_mixed_store_full_replay_is_deterministic(self):
        print("workload:", json.dumps(self.workload), flush=True)
        digests, _, _ = self.replays_identically(self.store, "mixed")
        print("\n".join(digests), flush=True)
        if EXPORT:
            out = Path(EXPORT)
            out.mkdir(parents=True, exist_ok=True)
            with tarfile.open(out / "mixed-store.tar", "w") as tar:
                tar.add(self.store, arcname="store",
                        filter=lambda t: None if t.name.endswith(".sock") else t)
            (out / "digest.txt").write_text("\n".join(digests) + "\n", encoding="ascii")
        if EXPECT:
            expected = (Path(EXPECT) / "digest.txt").read_text(encoding="ascii").splitlines()
            self.assert_same(digests, expected, "this box against the exported box")

    def test_b_checkpoint_bytes_and_checkpoint_open(self):
        full, one, two = self.replays_identically(self.store, "cp")
        files = {}
        for store in (one, two):
            out = self.run_native("store", store, "checkpoint").stdout.decode("ascii")
            self.assertIn("checkpoint sequence=", out)
            files[store] = {p.name: p.read_bytes() for p in sorted(store.iterdir())
                            if p.name.startswith("store-checkpoint") and p.is_file()}
            self.assertTrue(files[store], sorted(p.name for p in store.iterdir()))
        self.assertEqual(sorted(files[one]), sorted(files[two]))
        for name in files[one]:
            self.assertEqual(files[one][name], files[two][name],
                             "checkpoint file {} differs between the copies".format(name))
        joined = hashlib.sha256()
        for name in sorted(files[one]):
            joined.update(name.encode("ascii") + b"\0" + hashlib.sha256(files[one][name]).digest())
        other_box = cross_box("checkpoint.sha256", joined.hexdigest())
        if other_box is not None:
            self.assertEqual(joined.hexdigest(), other_box, "checkpoint bytes across boxes")
        from_checkpoint, opens = self.digest(one)
        self.assertTrue(opens and opens[0].startswith("open=checkpoint"), opens)
        # The checkpoint open is the full replay (fn-sco-store-open-of-extended-
        # capture): the same logical state, field by field.
        self.assert_same(from_checkpoint, full, "checkpoint open against full replay")

    def served_view(self, store, name):
        node = node_at(self, store, self.base / (name + "-node"))
        node.start(timeout=TIMEOUT)
        view = []
        try:
            client = Client(node.port, timeout=120, greeting=None)
            try:
                active = exchange(client, "LIST ACTIVE")
                view.append(active)
                view.append(exchange(client, "LIST NEWSGROUPS"))
                groups = [ln.split()[0].decode("ascii") for ln in active.split(b"\r\n")[1:]
                          if ln and ln != b"."]
                for group in groups:
                    reply = exchange(client, "GROUP " + group)
                    view.append(reply)
                    if not reply.startswith(b"211 "):
                        continue
                    count, low, high = (int(x) for x in reply.split()[1:4])
                    if count == 0:
                        continue
                    view.append(exchange(client, "OVER {}-{}".format(low, high)))
                    for n in range(low, high + 1):
                        view.append(exchange(client, "ARTICLE {}".format(n)))
                        view.append(exchange(client, "HEAD {}".format(n)))
            finally:
                client.close()
        finally:
            node.stop(grace=120)
        return view

    def test_c_served_view_is_identical(self):
        one, two = self.copy(self.store, "view-a"), self.copy(self.store, "view-b")
        a, b = self.served_view(one, "view-a"), self.served_view(two, "view-b")
        self.assertGreater(len(a), 4)
        self.assertEqual(len(a), len(b))
        for x, y in zip(a, b):
            self.assertEqual(x, y)
        whole = hashlib.sha256(b"".join(a)).hexdigest()
        other_box = cross_box("served-view.sha256", whole)
        if other_box is not None:
            self.assertEqual(whole, other_box, "served view across boxes")

    def test_e_a_changed_history_digests_differently(self):
        """Teeth: the digest is not constant.  One more record (an offline
        `store ROOT post`) changes history, canonical and state; the fields it
        cannot touch (groups, capacity) stay; a copy untouched keeps its digest."""
        base, _ = self.digest(self.copy(self.store, "teeth-base"))
        changed = self.copy(self.store, "teeth-changed")
        payload = self.base / "teeth.eml"
        payload.write_bytes(article("<det-teeth@example.invalid>", "fn.test", "teeth",
                                    b"one more record\r\n",
                                    extra=b"Date: Sat, 26 Sep 2026 12:00:00 +0000\r\n"))
        self.run_native("store", changed, "post", "<det-teeth@example.invalid>", payload,
                        "-", "-", "fn.test")
        after, _ = self.digest(changed)
        by = lambda lines: {ln.rsplit(" ", 1)[0]: ln.rsplit(" ", 1)[1] for ln in lines}
        b, a = by(base), by(after)
        for name in ("digest canonical", "digest state", "digest field files"):
            self.assertNotEqual(b[name], a[name], name)
        self.assertNotEqual([k for k in b if k.startswith("digest history")],
                            [k for k in a if k.startswith("digest history")])
        for name in ("digest field groups", "digest field capacity"):
            self.assertEqual(b[name], a[name], name)

    def test_g_the_genesis_is_read_only_where_it_must_be(self):
        """Format 10 (books/store-genesis.lisp, lane format-bump-10): two
        stores holding the same records under DIFFERENT genesis records (two
        imports of one export: each import draws its own node identity,
        history salt and clock reading) fold the same state: every digest
        line but `digest genesis' is equal, and that one differs.  So no
        folded field reads a genesis field; the salt keys only the owner's
        derived index.  Teeth, where the open must read it: a genesis with
        one octet changed is refused by name (genesis-damaged), and a genesis
        swapped from the other store opens but its trailer is not the chain
        segment 1 names (the open refuses, never replays)."""
        d = self.base / "gen"
        d.mkdir(exist_ok=True)
        archive = d / "archive"
        self.operator(self.store, "gen-src", "store", "export", str(archive))
        a, b = d / "a", d / "b"
        self.operator(a, "gen-a", "store", "import", str(archive))
        self.operator(b, "gen-b", "store", "import", str(archive))
        da, _ = self.digest(a)
        db, _ = self.digest(b)
        rest = lambda lines: [ln for ln in lines if not ln.startswith("digest genesis ")]
        gen = lambda lines: [ln for ln in lines if ln.startswith("digest genesis ")]
        self.assertEqual(len(gen(da)), 1, da)
        self.assert_same(rest(da), rest(db), "two genesis records, one history")
        self.assertNotEqual(gen(da), gen(db), "the two imports drew the same genesis")
        self.assertNotEqual((a / "journal" / "000000.log").read_bytes(),
                            (b / "journal" / "000000.log").read_bytes())
        # Teeth 1: a damaged genesis is refused by name at the open.
        damaged = self.copy(a, "gen-damaged")
        path = damaged / "journal" / "000000.log"
        octets = bytearray(path.read_bytes())
        octets[40] ^= 1
        path.write_bytes(bytes(octets))
        refused = self.run_native("store", damaged, "digest", expected=None)
        self.assertEqual(refused.returncode, 1, refused.stderr)
        self.assertIn(b"reason=genesis-damaged", refused.stderr + refused.stdout)
        # Teeth 2: b's genesis under a's log: it opens (same profile and
        # schema), but segment 1 chains from a's trailer, so the open refuses.
        swapped = self.copy(a, "gen-swapped")
        (swapped / "journal" / "000000.log").write_bytes(
            (b / "journal" / "000000.log").read_bytes())
        chained = self.run_native("store", swapped, "digest", expected=None)
        self.assertNotEqual(chained.returncode, 0, chained.stdout)
        self.assertNotIn(b"digest state ", chained.stdout)

    def operator(self, store, name, *words, expected=0):
        node = node_at(self, store, self.base / (name + "-node"))
        return self.run_native("operator", node.config, *words, expected=expected)

    def test_f_a_reclaim_replays_from_its_recorded_instant(self):
        """PKT-857 (books/reclaim-instant.lisp): `store reclaim' records its
        instant as the configuration row `retention-reclaim-at' before it
        rewrites anything, and the rewrite is a function of the pre-reclaim
        store and that record.  A copy of the pre-reclaim store given the
        record (the one new config/ file) reclaims with `store reclaim
        --recorded' exactly as the store did: the same report and the same
        folded state.  Teeth: without the record `--recorded' is refused by
        name and rewrites nothing."""
        # Its own small store: the mixed store's registered consumer lags the
        # frontier, and a lagging consumer holds every article
        # (books/store-reclaim-holders.lisp, the conservative reading).
        base = self.base / "rc" / "store"
        base.parent.mkdir(exist_ok=True)
        node = node_at(self, base, self.base / "rc-base-node")
        self.run_native("operator", node.config, "init", "fn.test")
        node.start(timeout=TIMEOUT)
        try:
            client = Client(node.port, timeout=120, greeting=None)
            try:
                for i in range(4):
                    reply = post(client, article("<det-rc-{}@example.invalid>".format(i), "fn.test",
                                                "rc {}".format(i), b"reclaimable\r\n" * (4 + i)))
                    self.assertTrue(reply.startswith(b"240"), reply)
            finally:
                client.close()
        finally:
            node.stop(grace=120)
        self.operator(base, "rc-base", "retention", "set", "released-by-all-holders")
        a, b, c = (self.copy(base, "rc-" + x) for x in "abc")
        before = set(os.listdir(b / "config"))
        done = self.operator(a, "rc-a", "store", "reclaim").stdout.decode("ascii")
        first = done.splitlines()[0]
        self.assertTrue(first.startswith("reclaimed="), done)
        self.assertNotEqual(first.split()[0], "reclaimed=0", done)
        record = [w.split("=", 1)[1] for w in first.split() if w.startswith("instant-record=")]
        new = sorted(set(os.listdir(a / "config")) - before)
        self.assertEqual(new, record, (done, new))
        shutil.copyfile(a / "config" / new[0], b / "config" / new[0])
        again = self.operator(b, "rc-b", "store", "reclaim", "--recorded").stdout.decode("ascii")
        strip = lambda text: [ln if not ln.startswith("reclaimed=") else
                              " ".join(w for w in ln.split()
                                       if w.split("=")[0] in ("reclaimed", "freed-octets"))
                              for ln in text.splitlines()]
        self.assertEqual(strip(done), strip(again), (done, again))
        self.assertIn("instant=recorded", again)
        da, opens_a = self.digest(a)
        db, opens_b = self.digest(b)
        self.assertTrue(opens_a and opens_a[0].startswith("open=checkpoint"), opens_a)
        self.assert_same(da, db, "the reclaim against its replay from the recorded instant")
        refused = self.operator(c, "rc-c", "store", "reclaim", "--recorded", expected=None)
        self.assertNotEqual(refused.returncode, 0)
        self.assertIn(b"no-recorded-instant", refused.stdout + refused.stderr)
        dc, _ = self.digest(c)
        dbase, _ = self.digest(base)
        self.assert_same(dc, dbase, "the refused copy against the pre-reclaim store")
        self.assertNotEqual(dc, da)

    @unittest.skipUnless((FIXTURES / FIXTURE / "store").is_dir(),
                         "the registered fixture is not on this box")
    def test_d_registered_fixture_replays_identically(self):
        self.replays_identically(FIXTURES / FIXTURE / "store", FIXTURE)


if __name__ == "__main__":
    unittest.main()

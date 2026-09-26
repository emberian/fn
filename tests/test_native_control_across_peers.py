"""Opt-in native matrix: control across two peers under D29 (PKT-210, NNT-037).

Each test drives three saved-image nodes on loopback.  H is the authoring
node: every target and every cancel is authored there (signed articles
through `hybrid-author`, unsigned ones through POST) and its octets are
fetched before anything is relayed, so the harness controls the order in
which A and B receive each pair.  A and B are the nodes under test; they
receive over IHAVE (Path prefixed with the configured peer's name) and each
decides under its own enrolment and grants (design section 3, "the receiver
decides again").  Q holds `cancel` over fn.ga.* on A only, fn.gb.* on B only
and fn.gab.* on both; P and Q are enrolled on all three nodes.

The matrix, per test: {grant on A only, on B only, on both} (the target's
group) x {target then cancel, cancel then target} x {no kill, both receivers
SIGKILLed and restarted between the two arrivals}.  One test takes the
author basis (P cancels P's signed target), the other the authority basis
(Q cancels an unsigned target).  The observations:

- D29's test, visible(T then C) = visible(C then T): on each node the fresh
  answer for the target is the same line in both orders, and it is 430
  exactly when the node's decision withdraws (the author basis everywhere;
  the authority basis where that node's grant covers the target's group).
  Theorem: books/control-authority.lisp fn-ctl-visible-is-arrival-order-
  independent over fn-ctl-cancel-executes-only-for-author-or-authority.
- A reader pinned on A and on B after the first arrivals keeps its archive
  across the second arrivals, and sees the fresh answer once it advances
  (its own POST's 240 re-pins it: fn-own-durable-outcome-repins-the-poster).
  Theorem: fn-ctl-pinned-view-keeps-its-archive.
- Every grant is then revoked on both nodes and both are SIGKILLed and
  restarted: every answer is unchanged, since each record carries the
  configuration generation it was decided under.  Theorems:
  fn-ctl-replay-is-the-fold, fn-ctl-revoke-changes-decisions-not-records.

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest -v tests.test_native_control_across_peers
(OpenSSL 3.5 with ML-DSA-65: FN_TEST_OPENSSL, else $FN_OPENSSL_PREFIX/bin/openssl,
else openssl on PATH; the module skips when none generates an ML-DSA-65 key.)
"""

import itertools
import json
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import unittest

from tests.native_process import wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
# tools/hbox_native.sh sets no FN_NATIVE_HOST: take the developer image it
# built, else the production one.
IMAGE = (Path(IMAGE_TEXT) if IMAGE_TEXT else
         next((p for p in (ROOT / "build" / "fn-host-developer", ROOT / "build" / "fn-host")
               if p.is_file()), None))
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))


def openssl_with_ml_dsa():
    candidates = [os.environ.get("FN_TEST_OPENSSL")]
    prefix = os.environ.get("FN_OPENSSL_PREFIX")
    if prefix:
        candidates.append(str(Path(prefix) / "bin" / "openssl"))
    candidates.append("openssl")
    for candidate in candidates:
        if not candidate:
            continue
        try:
            probe = subprocess.run([candidate, "list", "-signature-algorithms"],
                                   stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                   timeout=30, check=False)
        except (OSError, subprocess.TimeoutExpired):
            continue
        if probe.returncode == 0 and b"ML-DSA-65" in probe.stdout:
            return candidate
    return None


OPENSSL = openssl_with_ml_dsa() if READY else None

GRANTS = {"a": ("fn.ga.*", "fn.gab.*"), "b": ("fn.gb.*", "fn.gab.*")}
SCOPES = {"a-only": "fn.ga.t", "b-only": "fn.gb.t", "both": "fn.gab.t"}
GROUPS = ["fn.ga.t", "fn.gb.t", "fn.gab.t", "fn.post", "control.cancel"]
ORDERS = ("tc", "ct")
KILLS = ("run", "kill")


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def source(message_id, newsgroups, extra=None):
    lines = ["From: poster@example.invalid", "Newsgroups: " + newsgroups,
             "Subject: across-peers " + message_id,
             "Date: Sat, 26 Sep 2026 10:00:00 +0000",
             "Message-ID: " + message_id] + ([extra] if extra else [])
    return ("\r\n".join(lines) + "\r\n\r\nbody\r\n").encode("ascii")


def stuffed(octets):
    return b"".join((b"." + line if line.startswith(b".") else line)
                    for line in octets.splitlines(keepends=True))


@unittest.skipUnless(READY and OPENSSL, "set FN_NATIVE_HOST and an OpenSSL with ML-DSA-65")
class NativeControlAcrossPeersTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-across-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.processes = []
        self.addCleanup(self.stop_all)

    # -- nodes -------------------------------------------------------------
    def command(self, arguments, expected=0):
        result = subprocess.run(list(map(str, arguments)), cwd=ROOT, env=self.env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=180, check=False)
        self.assertEqual(result.returncode, expected, result)
        return result

    def initialize(self, name):
        root = self.base / name
        root.mkdir()
        store = root / "store"
        port = free_port()
        self.command([IMAGE, "--fn", "store", store, "init", *GROUPS])
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(store, port, root / "control.sock"),
            encoding="ascii")
        node = {"name": name, "root": root, "config": config, "port": port,
                "control": root / "control.sock", "starts": 0}
        if name != "h":
            self.command([IMAGE, "--fn", "operator", config, "peer", "add", "source",
                          "source.example.invalid", "127.0.0.1", str(free_port()),
                          "fn.*", "-", "127.0.0.1", "true"])
        return node

    def start(self, node):
        node["starts"] += 1
        log = open(node["root"] / "node-{}.log".format(node["starts"]), "wb")
        self.addCleanup(log.close)
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=log)
        self.processes.append(process)
        node["process"] = process
        wait_for_announcement(process, b"LISTENING ")

    def kill(self, node):
        """SIGKILL: no shutdown path runs; the restart is a recovery."""
        process = node.pop("process")
        process.kill()
        process.communicate(timeout=60)
        self.processes.remove(process)

    def stop_all(self):
        for process in self.processes:
            if process.poll() is None:
                process.terminate()
                process.communicate(timeout=60)

    # -- signers -----------------------------------------------------------
    def signer(self, label, principal_byte, ed_public_hex, ed_seed_hex, generation):
        root = self.base / ("signer-" + label)
        root.mkdir()
        keys = {"principal": root / "principal.bin", "ed_public": root / "ed-public.bin",
                "ed_secret": root / "ed-secret.bin", "ml_private": root / "ml.pem",
                "ml_public": root / "ml-public.pem", "root": root,
                "generation": generation}
        keys["principal"].write_bytes(bytes([principal_byte]) * 32)
        keys["ed_public"].write_bytes(bytes.fromhex(ed_public_hex))
        keys["ed_secret"].write_bytes(bytes.fromhex(ed_seed_hex + ed_public_hex))
        self.command([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out",
                      keys["ml_private"]])
        self.command([OPENSSL, "pkey", "-in", keys["ml_private"], "-pubout", "-out",
                      keys["ml_public"]])
        return keys

    def author(self, node, keys, message_id, newsgroups, extra=None):
        path = keys["root"] / (message_id.strip("<>").replace("@", "_") + ".eml")
        path.write_bytes(source(message_id, newsgroups, extra))
        signed = self.command([IMAGE, "--fn", "hybrid-sign", keys["principal"],
                               keys["ed_public"], keys["ed_secret"], keys["ml_public"],
                               keys["ml_private"], path])
        parts = dict(line.split() for line in signed.stdout.decode().splitlines())
        ed_sig, ml_sig = path.with_suffix(".ed"), path.with_suffix(".ml")
        ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
        ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        self.command([IMAGE, "--fn", "hybrid-author", node["control"], keys["generation"],
                      path, ed_sig, ml_sig, keys["ml_public"]])

    # -- NNTP --------------------------------------------------------------
    def connect(self, node):
        client = socket.create_connection(("127.0.0.1", node["port"]), timeout=30)
        self.addCleanup(client.close)
        stream = client.makefile("rwb", buffering=0)
        self.assertTrue(stream.readline().startswith(b"200 "))
        return stream

    @staticmethod
    def first_line(stream, command):
        stream.write(command)
        line = stream.readline()
        if line[:3] == b"220" or (line[:3] == b"211" and command.startswith(b"LISTGROUP")):
            while stream.readline() not in (b".\r\n", b""):
                pass
        return line.decode().strip()

    def answer(self, node, message_id):
        stream = self.connect(node)
        return self.first_line(stream, b"ARTICLE " + message_id.encode() + b"\r\n")

    def fetch(self, node, message_id):
        stream = self.connect(node)
        stream.write(b"ARTICLE " + message_id.encode() + b"\r\n")
        status = stream.readline()
        self.assertTrue(status.startswith(b"220"), (node["name"], message_id, status))
        lines = []
        while True:
            line = stream.readline()
            if line in (b".\r\n", b""):
                break
            lines.append(line[1:] if line.startswith(b".") else line)
        return b"".join(lines)

    def post(self, stream, payload):
        stream.write(b"POST\r\n")
        first = stream.readline()
        self.assertTrue(first.startswith(b"340"), first)
        stream.write(stuffed(payload) + b".\r\n")
        return stream.readline().decode().strip()

    def relay(self, octets, destination, message_id, codes):
        head, _, body = octets.partition(b"\r\n\r\n")
        fields = head.split(b"\r\n")
        rest = [f for f in fields if not f.lower().startswith(b"path:")]
        old = [f for f in fields if f.lower().startswith(b"path:")]
        tail = old[0].split(b":", 1)[1].strip() if old else b"not-for-mail"
        relayed = (b"\r\n".join([b"Path: source.example.invalid!" + tail] + rest)
                   + b"\r\n\r\n" + body)
        stream = self.connect(destination)
        stream.write(b"IHAVE " + message_id.encode() + b"\r\n")
        first = stream.readline().decode().strip()
        if first.startswith("335"):
            stream.write(stuffed(relayed) + b".\r\n")
            first += " / " + stream.readline().decode().strip()
        codes["relay {} {}".format(destination["name"], message_id)] = first

    # -- the matrix --------------------------------------------------------
    def run_matrix(self, basis):
        p = self.signer("p", 0x55,
                        "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
                        "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
                        "1")
        q = self.signer("q", 0x66,
                        "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
                        "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
                        "2")
        h, a, b = (self.initialize(n) for n in ("h", "a", "b"))
        nodes = {"a": a, "b": b}
        for node in (h, a, b):
            self.start(node)
            for keys in (p, q):
                self.command([IMAGE, "--fn", "hybrid-enroll", node["control"],
                              keys["generation"], keys["principal"], keys["ed_public"],
                              keys["ml_public"]])
        for name, namespaces in GRANTS.items():
            for namespace in namespaces:
                self.command([IMAGE, "--fn", "operator", nodes[name]["config"], "control",
                              "grant", "66" * 32, "cancel", namespace])

        # Every case's two articles are authored on H and fetched before any
        # relay: H always takes the target first, and its answers are not
        # under test.
        cases = []
        for scope, order, kill in itertools.product(SCOPES, ORDERS, KILLS):
            stem = "{}-{}-{}-{}".format(basis, scope, order, kill)
            cases.append({"scope": scope, "order": order, "kill": kill,
                          "target": "<t-{}@example.invalid>".format(stem),
                          "cancel": "<c-{}@example.invalid>".format(stem)})
        poster = self.connect(h)
        for case in cases:
            group = SCOPES[case["scope"]]
            if basis == "author":
                self.author(h, p, case["target"], group)
            else:
                posted = self.post(poster, source(case["target"], group))
                self.assertTrue(posted.startswith("240"), (case["target"], posted))
            case["target-octets"] = self.fetch(h, case["target"])
        for case in cases:
            canceller = p if basis == "author" else q
            self.author(h, canceller, case["cancel"], SCOPES[case["scope"]],
                        "Control: cancel " + case["target"])
            case["cancel-octets"] = self.fetch(h, case["cancel"])

        codes = {}

        def arrive(case, which):
            for node in (a, b):
                self.relay(case[which + "-octets"], node, case[which], codes)

        def first_of(case):
            return "target" if case["order"] == "tc" else "cancel"

        def second_of(case):
            return "cancel" if case["order"] == "tc" else "target"

        # Kill cases: first arrivals, then both receivers SIGKILLed and
        # restarted, so the second arrival meets a recovered node.
        for case in cases:
            if case["kill"] == "kill":
                arrive(case, first_of(case))
        for node in (a, b):
            self.kill(node)
            self.start(node)
        for case in cases:
            if case["kill"] == "run":
                arrive(case, first_of(case))

        # Readers pinned on A and on B after every first arrival.
        pinned = {name: self.connect(node) for name, node in nodes.items()}
        pinned_before = {name: {c["target"]: self.first_line(
            stream, b"ARTICLE " + c["target"].encode() + b"\r\n")
            for c in cases if c["order"] == "tc"} for name, stream in pinned.items()}

        for case in cases:
            arrive(case, second_of(case))

        fresh = {name: {c["target"]: self.answer(node, c["target"]) for c in cases}
                 for name, node in nodes.items()}
        pinned_after = {name: {m: self.first_line(stream, b"ARTICLE " + m.encode() + b"\r\n")
                               for m in pinned_before[name]}
                        for name, stream in pinned.items()}
        advanced_post = {}
        pinned_advanced = {}
        for name, stream in pinned.items():
            advanced_post[name] = self.post(stream, source(
                "<advance-{}-{}@example.invalid>".format(basis, name), "fn.post"))
            pinned_advanced[name] = {m: self.first_line(
                stream, b"ARTICLE " + m.encode() + b"\r\n") for m in pinned_before[name]}

        # Every grant revoked, both receivers SIGKILLed and restarted.
        for name, namespaces in GRANTS.items():
            for namespace in namespaces:
                self.command([IMAGE, "--fn", "operator", nodes[name]["config"], "control",
                              "revoke", "66" * 32, "cancel", namespace])
        for node in (a, b):
            self.kill(node)
            self.start(node)
        replayed = {name: {c["target"]: self.answer(node, c["target"]) for c in cases}
                    for name, node in nodes.items()}

        table = []
        for case in cases:
            row = {k: case[k] for k in ("scope", "order", "kill", "target")}
            for name in nodes:
                row[name] = fresh[name][case["target"]]
                row[name + "-replayed"] = replayed[name][case["target"]]
            table.append(row)
        witness = {"basis": basis, "table": table, "pinned-before": pinned_before,
                   "pinned-after": pinned_after, "advanced-post": advanced_post,
                   "pinned-advanced": pinned_advanced, "codes": codes}
        print("NATIVE-ACROSS-PEERS-WITNESS " + json.dumps(witness, sort_keys=True))

        # Every relay was offered and taken.
        self.assertTrue(all(v.startswith("335") and v.endswith(
            "235 article transferred OK") for v in codes.values()), codes)
        for case in cases:
            for name in nodes:
                granted = (case["scope"] == "both"
                           or case["scope"] == name + "-only")
                withdraws = basis == "author" or granted
                answer = fresh[name][case["target"]]
                self.assertTrue(answer.startswith("430" if withdraws else "220"),
                                (name, case["target"], answer))
                self.assertEqual(replayed[name][case["target"]], answer,
                                 (name, case["target"]))
        # D29's test: the same answer, whichever arrived first.
        for scope, kill in itertools.product(SCOPES, KILLS):
            tc, ct = (next(c for c in cases if (c["scope"], c["order"], c["kill"])
                           == (scope, order, kill)) for order in ORDERS)
            for name in nodes:
                self.assertEqual(fresh[name][tc["target"]].split()[0],
                                 fresh[name][ct["target"]].split()[0],
                                 (name, scope, kill))
                self.assertEqual(
                    fresh[name][tc["target"]].replace(tc["target"], "<T>"),
                    fresh[name][ct["target"]].replace(ct["target"], "<T>"),
                    (name, scope, kill))
        for name in nodes:
            self.assertTrue(all(v.startswith("220") for v in pinned_before[name].values()),
                            pinned_before[name])
            self.assertEqual(pinned_after[name], pinned_before[name])
            self.assertTrue(advanced_post[name].startswith("240"), advanced_post)
            self.assertEqual(pinned_advanced[name],
                             {m: fresh[name][m] for m in pinned_before[name]})

    def solo(self):
        p = self.signer("p", 0x55,
                        "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
                        "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
                        "1")
        node = self.initialize("h")
        self.start(node)
        self.command([IMAGE, "--fn", "hybrid-enroll", node["control"], p["generation"],
                      p["principal"], p["ed_public"], p["ml_public"]])
        return node, p

    def test_a_self_cancel_is_declined(self):
        """A cancel naming its own Message-ID is declined (books/control-
        authority.lisp fn-ctl-withdrawal-plan, `(:decline :self-target)`):
        the article stays visible, before and after a SIGKILL."""
        node, p = self.solo()
        own = "<self-cancel@example.invalid>"
        self.author(node, p, own, "fn.post", "Control: cancel " + own)
        fresh = self.answer(node, own)
        self.kill(node)
        self.start(node)
        replayed = self.answer(node, own)
        print("NATIVE-SELF-CANCEL-WITNESS " + json.dumps(
            {"fresh": fresh, "replayed": replayed}, sort_keys=True))
        self.assertTrue(fresh.startswith("220 "), fresh)
        self.assertEqual(replayed, fresh)

    # PKT-443: reachable and still the plain answer.  With nothing visible
    # the view's group index is nil (fn-own-refresh: fn-gidx-build of an
    # empty list), so books/served.lisp fn-served-conn-pinned-index pins the
    # bare trie without the control pin and the reader answers "430 no
    # article with that message-id" (hbox, developer image f10414e9 at f9b91cde, manual-ev2.log).
    # The expected answer stays the served guarantee.
    @unittest.expectedFailure
    def test_a_view_with_every_article_withdrawn(self):
        """PKT-208's nil-group-index view (control-c3e, "Not done"): a view
        whose visible list is empty has no group index.  Two signed cancels
        by one author naming each other (C1 cancels C2, C2 cancels C1; neither
        is a self-target) withdraw each other on the author basis, so a store
        holding only them publishes a view with nothing visible and two
        withdrawn articles.  The answer by Message-ID must still say
        `withdrawn` (books/nntp-control.lisp
        fn-nntp-withdrawn-article-answers-430-withdrawn)."""
        node, p = self.solo()
        one, two = "<mutual-1@example.invalid>", "<mutual-2@example.invalid>"
        self.author(node, p, one, "fn.post", "Control: cancel " + two)
        self.author(node, p, two, "fn.post", "Control: cancel " + one)
        fresh = [self.answer(node, m) for m in (one, two)]
        stream = self.connect(node)
        group = self.first_line(stream, b"GROUP control.cancel\r\n")
        self.kill(node)
        self.start(node)
        replayed = [self.answer(node, m) for m in (one, two)]
        print("NATIVE-EMPTY-VIEW-WITNESS " + json.dumps(
            {"fresh": fresh, "replayed": replayed, "group": group}, sort_keys=True))
        self.assertEqual(fresh, ["430 withdrawn", "430 withdrawn"])
        self.assertEqual(replayed, fresh)

    def test_author_basis(self):
        self.run_matrix("author")

    def test_authority_basis(self):
        self.run_matrix("authority")


if __name__ == "__main__":
    unittest.main()

"""Opt-in native witness: one authored article keeps one identity through
every route the node offers (the Fable mandate sections 5.3 and 5.4; D25,
D29, D32).  NNT-020, SCN-062.

Two developer-image nodes on loopback, A and B, each with its own path
identity; A feeds B over the peer port.  The corpus is
tests/fixtures/source-corpus: a supplied and a generated Date, a
client-supplied Path, a supplied Xref, unknown headers, 8-bit MIME, a
dual-signature carrier and an unsigned legacy post.  Each element is driven
through the served POST, a retry of the same bytes at a later second, one
changed authored byte, the operator post, the signed route (hybrid-author and
a POSTed carrier), protected-transit carriage A to B, and a reopen of A.
Every decision is the image's; Python observes replies and bytes and prints
the identity table as one `SOURCE-CORPUS-TABLE <json>` line.

The equality each column means:
  * Message-ID: RFC 5536 s3.1.3 identity; transit (IHAVE/TAKETHIS) decides
    duplicates by it alone (RFC 3977 s6.3.2, RFC 4644).
  * authored source: the poster's octets; on the injecting routes the D25
    verdict compares it (fn-rcl-existing-action): same source is 441
    "already stored here", a changed byte 441 "a different article".
  * stored representation: SHA-256 of the record payload (`store inspect`),
    which differs between A and B by exactly B's Path prefix.
  * local number: per node and per group, never compared across nodes.
  * application operation: the harness's own label; an unsigned legacy post
    with no Message-ID has no identity a retry can name, so its retry is a
    new article under a new generated Message-ID.

Run: FN_NATIVE_HOST=<developer launcher> python3 -m unittest tests.test_native_source_corpus
"""

import hashlib
import json
import os
from pathlib import Path
import signal
import socket
import subprocess
import tempfile
import time
import unittest

from tests.native_process import wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "tests" / "fixtures" / "source-corpus"
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))
ALREADY = b"441 posting failed; this article is already stored here"
DIFFERENT = b"441 posting failed; a different article with this Message-ID is stored here"
ELEMENTS = ("supplied-date", "generated-date", "client-path", "xref", "unknown-headers",
            "mime", "legacy")
ED_PUBLIC = "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
ED_SECRET = "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60" + ED_PUBLIC


def sha(data):
    return hashlib.sha256(data).hexdigest()


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def header(article, name):
    for line in article.split(b"\r\n\r\n", 1)[0].split(b"\r\n"):
        if line.lower().startswith(name.lower() + b":"):
            return line.split(b":", 1)[1].strip().decode("ascii", "replace")
    return None


def changed(source):
    """One authored byte changed: the last body octet before the final CRLF."""
    return source[:-3] + bytes([source[-3] ^ 1]) + source[-2:]


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a developer native launcher")
class NativeSourceCorpusTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-source-corpus-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.processes = []
        self.addCleanup(self.stop_all)

    # -- process and protocol helpers ---------------------------------------
    def command(self, arguments, expected=0):
        result = subprocess.run(list(map(str, arguments)), cwd=ROOT, env=self.env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=300, check=False)
        if expected is not None:
            self.assertEqual(result.returncode, expected, result)
        return result

    def initialize(self, name, groups, identity):
        root = self.base / name
        root.mkdir()
        store, control = root / "store", root / "control.sock"
        port = free_port()
        self.command([IMAGE, "--fn", "store", store, "init", *groups])
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(store, port, control), encoding="ascii")
        node = {"name": name, "root": root, "store": store, "config": config,
                "port": port, "control": control, "identity": identity}
        self.command([IMAGE, "--fn", "operator", config, "policy", "set",
                      "path-identity", identity])
        return node

    def peer(self, source, target, outbound):
        self.command([IMAGE, "--fn", "operator", source["config"], "peer", "add",
                      target["name"], target["identity"], "127.0.0.1", str(target["port"]),
                      "fn.*", outbound, "127.0.0.1", "true"])

    def start(self, node):
        # The owner's diagnostics go to a regular file (an unread PIPE can
        # fill and block the service), kept in FN_NATIVE_TEST_DIAGNOSTIC_DIR
        # when set.
        keep = os.environ.get("FN_NATIVE_TEST_DIAGNOSTIC_DIR")
        directory = Path(keep) if keep else node["root"]
        directory.mkdir(parents=True, exist_ok=True)
        with (directory / (self.id().rsplit(".", 1)[-1] + "-" + node["name"]
                           + ".stderr")).open("ab") as stderr:
            process = subprocess.Popen(
                [str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
                cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=stderr)
        self.processes.append(process)
        node["process"] = process
        wait_for_announcement(process, b"LISTENING ")

    def stop(self, node, kill=False):
        process = node.pop("process")
        if kill:
            process.send_signal(signal.SIGKILL)
        else:
            process.terminate()
        process.communicate(timeout=60)
        self.processes.remove(process)
        return process.returncode

    def stop_all(self):
        for process in self.processes:
            if process.poll() is None:
                process.terminate()
                process.communicate(timeout=60)

    def connect(self, node):
        client = socket.create_connection(("127.0.0.1", node["port"]), timeout=30)
        stream = client.makefile("rwb", buffering=0)
        self.assertTrue(stream.readline().startswith(b"200 "))
        return client, stream

    @staticmethod
    def body(stream):
        lines = []
        while True:
            line = stream.readline()
            if line in (b".\r\n", b""):
                return b"".join(lines)
            lines.append(line[1:] if line.startswith(b"..") else line)

    def ask(self, stream, command):
        stream.write(command)
        line = stream.readline()
        data = self.body(stream) if line[:3] in (b"211", b"220", b"101", b"225") else None
        if line[:3] == b"211" and not command.startswith(b"LISTGROUP"):
            data = None
        return line.rstrip(b"\r\n"), data

    def post(self, node, payload):
        client, stream = self.connect(node)
        with client:
            stream.write(b"POST\r\n")
            first = stream.readline()
            self.assertTrue(first.startswith(b"340"), first)
            for line in payload.split(b"\r\n")[:-1]:
                stream.write((b"." + line if line.startswith(b".") else line) + b"\r\n")
            stream.write(b".\r\n")
            return stream.readline().rstrip(b"\r\n")

    def served(self, node, group=b"fn.test"):
        """{Message-ID: (number, octets)} for every article a fresh view serves."""
        client, stream = self.connect(node)
        view = {}
        with client:
            stream.write(b"LISTGROUP " + group + b"\r\n")
            status = stream.readline()
            if not status.startswith(b"211"):
                return view
            numbers = [int(x) for x in self.body(stream).split()]
            for number in numbers:
                stream.write(b"ARTICLE %d\r\n" % number)
                line = stream.readline()
                if line.startswith(b"220"):
                    octets = self.body(stream)
                    view[header(octets, b"Message-ID")] = (number, octets)
        return view

    def article(self, node, message_id):
        client, stream = self.connect(node)
        with client:
            line, data = self.ask(stream, b"ARTICLE " + message_id.encode() + b"\r\n")
            return line, data

    def await_article(self, node, message_id, timeout=90):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            line, data = self.article(node, message_id)
            if line.startswith(b"220"):
                return data
            time.sleep(0.2)
        self.fail("{} did not receive {}".format(node["name"], message_id))

    def inspect(self, node, message_id):
        result = self.command([IMAGE, "--fn", "store", node["store"], "inspect", message_id],
                              expected=None)
        return result.stdout if result.returncode == 0 else None

    def keys(self, node):
        root = node["root"]
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        keys = {"principal": root / "principal.bin", "ed_public": root / "ed-public.bin",
                "ed_secret": root / "ed-secret.bin", "ml_private": root / "ml-private.pem",
                "ml_public": root / "ml-public.pem"}
        keys["principal"].write_bytes(bytes([85]) * 32)
        keys["ed_public"].write_bytes(bytes.fromhex(ED_PUBLIC))
        keys["ed_secret"].write_bytes(bytes.fromhex(ED_SECRET))
        self.command([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out",
                      keys["ml_private"]])
        self.command([openssl, "pkey", "-in", keys["ml_private"], "-pubout", "-out",
                      keys["ml_public"]])
        return keys

    def author(self, node, keys, stem, source_octets, signatures=None):
        """Sign SOURCE_OCTETS and author it; with SIGNATURES (an earlier stem),
        resend that earlier signed source exactly.  ML-DSA-65 signing is
        hedged (FIPS 204), so signing the same source again yields another
        signature and so another authored carrier: a client's retry reuses
        the signature it persisted, as it reuses its Message-ID."""
        root = node["root"]
        source = root / (stem + ".eml")
        source.write_bytes(source_octets)
        ed_sig, ml_sig = root / (stem + ".ed"), root / (stem + ".ml")
        if signatures is not None:
            ed_sig.write_bytes((root / (signatures + ".ed")).read_bytes())
            ml_sig.write_bytes((root / (signatures + ".ml")).read_bytes())
        else:
            signed = self.command([IMAGE, "--fn", "hybrid-sign", keys["principal"],
                                   keys["ed_public"], keys["ed_secret"], keys["ml_public"],
                                   keys["ml_private"], source])
            parts = dict(line.split() for line in signed.stdout.decode().splitlines())
            ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        done = self.command([IMAGE, "--fn", "hybrid-author", node["control"], "1", source,
                             ed_sig, ml_sig, keys["ml_public"]], expected=None)
        self.last_author = (done.returncode, done.stdout.decode("utf-8", "replace").strip(),
                            done.stderr.decode("utf-8", "replace").strip()[-400:])
        return done.returncode

    def carrier(self, node, keys, stem, source_octets):
        source, carried = node["root"] / (stem + ".eml"), node["root"] / (stem + ".carrier")
        source.write_bytes(source_octets)
        self.command([IMAGE, "--fn", "hybrid-sign-carrier", keys["principal"],
                      keys["ed_public"], keys["ed_secret"], keys["ml_public"],
                      keys["ml_private"], source, carried])
        return carried.read_bytes()

    # -- the identity table ---------------------------------------------------
    def test_identity_table_across_routes(self):
        a = self.initialize("a", ["fn.test"], "a.corpus.invalid")
        b = self.initialize("b", ["fn.test"], "b.corpus.invalid")
        self.peer(a, b, "fn.*")
        self.peer(b, a, "-")
        self.start(b)
        self.start(a)
        keys = self.keys(a)
        # D23: a carried signed article is admitted at B on the author's
        # enrollment there, so the author is enrolled at both nodes.
        for node in (a, b):
            self.command([IMAGE, "--fn", "hybrid-enroll", node["control"], "1",
                          keys["principal"], keys["ed_public"], keys["ml_public"]])
        corpus = {name: (CORPUS / (name + ".article")).read_bytes() for name in ELEMENTS}
        corpus["signed"] = (CORPUS / "signed.article").read_bytes()
        rows, facts = [], {}

        def row(element, route, operation, reply, message_id=None, node=None, octets=None,
                number=None, source=None, equality=None):
            rows.append({"element": element, "route": route, "operation": operation,
                         "reply": reply, "message_id": message_id, "node": node,
                         "source_sha256": sha(source) if source is not None else None,
                         "stored_sha256": sha(octets) if octets is not None else None,
                         "path": header(octets, b"Path") if octets is not None else None,
                         "number": number, "equality": equality})

        # 1. The served POST, its retry at a later second, one changed byte.
        before = self.served(a)
        for name in ELEMENTS:
            facts[name] = {"first": self.post(a, corpus[name]).decode()}
        time.sleep(1.2)
        view = self.served(a)
        new = {m: v for m, v in view.items() if m not in before}
        by_subject = {header(v[1], b"Subject"): m for m, v in new.items()}
        for name in ELEMENTS:
            subject = header(corpus[name], b"Subject")
            message_id = by_subject.get(subject)
            facts[name]["message_id"] = message_id
            number, octets = view[message_id] if message_id else (None, None)
            row(name, "post", "post " + name, facts[name]["first"], message_id, "a", octets,
                number, corpus[name], "first acceptance")
            if octets is not None:
                facts[name]["stored"] = octets
                facts[name]["number"] = number
        for name in ELEMENTS:
            retry = self.post(a, corpus[name])
            facts[name]["retry"] = retry.decode()
            row(name, "post", "retry " + name, retry.decode(), facts[name]["message_id"], "a",
                source=corpus[name], equality="same source, later injection time")
            other = self.post(a, changed(corpus[name]))
            facts[name]["changed"] = other.decode()
            row(name, "post", "changed byte " + name, other.decode(),
                facts[name]["message_id"], "a", source=changed(corpus[name]),
                equality="one authored byte changed")
        after_retries = self.served(a)

        # 2. The operator post of the same source under its Message-ID.
        for name in ("supplied-date", "client-path", "mime"):
            payload = a["root"] / (name + ".operator")
            payload.write_bytes(corpus[name])
            done = self.command([IMAGE, "--fn", "operator", a["config"], "post",
                                 "--message-id", facts[name]["message_id"], "--payload",
                                 payload, "--group", "fn.test"], expected=None)
            facts[name]["operator"] = [done.returncode,
                                       done.stderr.decode("utf-8", "replace").strip()[-200:]]
            row(name, "operator-post", "operator post " + name,
                "rc={} {}".format(*facts[name]["operator"]), facts[name]["message_id"], "a",
                source=corpus[name], equality="same source through the operator route")
        after_operator = self.served(a)

        # 3. The signed routes: hybrid-author (the operator's signed carrier,
        #    injected) and a dual-signature carrier POSTed by a client.
        facts["signed"] = {"author": self.author(a, keys, "signed", corpus["signed"])}
        signed_id = header(corpus["signed"], b"Message-ID")
        facts["signed"]["message_id"] = signed_id
        facts["signed"]["author-retry"] = self.author(a, keys, "signed-retry", corpus["signed"],
                                                      signatures="signed")
        facts["signed"]["author-retry-detail"] = self.last_author
        carrier_source = corpus["signed"].replace(b"<sc-signed@", b"<sc-carrier@")
        carrier = self.carrier(a, keys, "carrier", carrier_source)
        carrier_id = "<sc-carrier@example.invalid>"
        facts["carrier"] = {"first": self.post(a, carrier).decode(), "message_id": carrier_id}
        time.sleep(1.2)
        facts["carrier"]["retry"] = self.post(a, carrier).decode()
        signed_view = self.served(a)
        for name, message_id, source in (("signed", signed_id, corpus["signed"]),
                                         ("carrier", carrier_id, carrier)):
            number, octets = signed_view.get(message_id, (None, None))
            facts[name]["stored"], facts[name]["number"] = octets, number
            row(name, "signed", name + " first", str(facts[name].get("author",
                facts[name].get("first"))), message_id, "a", octets, number, source,
                "signed source")
            row(name, "signed", name + " retry", str(facts[name].get("author-retry",
                facts[name].get("retry"))), message_id, "a", source=source,
                equality="same signed source again")

        # 4. Protected-transit carriage A to B (A's feed, IHAVE on B's peer port).
        carried = [n for n in ELEMENTS + ("signed", "carrier") if facts[n].get("stored")]
        for name in carried:
            message_id = facts[name]["message_id"]
            octets = self.await_article(b, message_id)
            facts[name]["b"] = octets
        b_view = self.served(b)
        for name in carried:
            message_id = facts[name]["message_id"]
            number, octets = b_view.get(message_id, (None, facts[name]["b"]))
            row(name, "transit", "feed a->b " + name, "220", message_id, "b", octets, number,
                equality="Message-ID; stored = A's with B's Path prefix")
            client, stream = self.connect(b)
            with client:
                stream.write(b"IHAVE " + message_id.encode() + b"\r\n")
                facts[name]["b-ihave"] = stream.readline().rstrip(b"\r\n").decode()
            row(name, "transit", "re-offer to b " + name, facts[name]["b-ihave"], message_id,
                "b", equality="Message-ID only")

        # 5. Reopen A: same octets and numbers; a retry is still the duplicate.
        self.stop(a, kill=True)
        self.start(a)
        reopened = self.served(a)
        for name in carried:
            message_id = facts[name]["message_id"]
            number, octets = reopened.get(message_id, (None, None))
            facts[name]["reopened"] = (number, octets)
            row(name, "reopen", "reopen a " + name, "220" if octets else "missing",
                message_id, "a", octets, number, equality="same record after SIGKILL")
        for name in ("supplied-date", "generated-date", "client-path", "mime"):
            facts[name]["retry-after-reopen"] = self.post(a, corpus[name]).decode()
            row(name, "reopen", "retry after reopen " + name,
                facts[name]["retry-after-reopen"], facts[name]["message_id"], "a",
                source=corpus[name], equality="same source after reopen")
        self.stop(a)
        self.stop(b)
        for name in carried:
            message_id = facts[name]["message_id"]
            facts[name]["inspect-a"] = self.inspect(a, message_id)
            facts[name]["inspect-b"] = self.inspect(b, message_id)
            row(name, "record", "store inspect a " + name,
                "found" if facts[name]["inspect-a"] else "absent", message_id, "a",
                facts[name]["inspect-a"], equality="record payload = served octets")
            row(name, "record", "store inspect b " + name,
                "found" if facts[name]["inspect-b"] else "absent", message_id, "b",
                facts[name]["inspect-b"], equality="record payload = served octets")
        rows.append({"route": "bp", "classification": "not exercised by this module"})
        rows.append({"route": "reclaim-tombstone",
                     "classification": "unexercised capability: no `store reclaim` verb"})
        print("SOURCE-CORPUS-TABLE " + json.dumps(rows, sort_keys=True))

        # Assertions: the contract, element by element.
        accepted = [n for n in ELEMENTS if n != "xref"]
        self.assertTrue(facts["xref"]["first"].startswith("441"), facts["xref"])
        self.assertIsNone(facts["xref"]["message_id"])
        for name in accepted:
            self.assertEqual(facts[name]["first"], "240 article received OK", name)
            self.assertIsNotNone(facts[name]["message_id"], name)
        for name in ("supplied-date", "generated-date", "client-path", "unknown-headers",
                     "mime"):
            self.assertEqual(facts[name]["retry"].encode(), ALREADY, (name, facts[name]))
            self.assertEqual(facts[name]["changed"].encode(), DIFFERENT, (name, facts[name]))
        # A legacy post with no Message-ID: its retry is a new article under a
        # new generated Message-ID (no identity to name); two new articles.
        self.assertEqual(facts["legacy"]["retry"], "240 article received OK")
        legacy_new = [m for m in after_retries if m not in view]
        self.assertEqual(len(legacy_new), 2, legacy_new)
        # One acceptance and number: the operator route adds no article.
        self.assertEqual(set(after_operator), set(after_retries))
        for name in ("supplied-date", "client-path", "mime"):
            # The operator route answers the D25 verdict by name: exit 0 (the
            # article is stored) and the word DUPLICATE (nothing new stored).
            self.assertEqual(facts[name]["operator"], [0, "accepted operator post DUPLICATE"])
        # D32: the supplied Path tail kept verbatim behind A's identity.
        self.assertEqual(header(facts["client-path"]["stored"], b"Path"),
                         "a.corpus.invalid!poster.example.invalid!not-for-mail")
        # The source is a suffix of what A stored (no normalization), for every
        # element without a supplied Path, the signed carrier included.
        for name in ("supplied-date", "generated-date", "unknown-headers", "mime"):
            self.assertTrue(facts[name]["stored"].endswith(corpus[name]), name)
        self.assertEqual(facts["signed"]["author"], 0, facts["signed"])
        self.assertEqual(facts["signed"]["author-retry"], 0, facts["signed"])
        self.assertTrue(facts["carrier"]["first"].startswith("240"), facts["carrier"])
        self.assertEqual(facts["carrier"]["retry"].encode(), ALREADY, facts["carrier"])
        self.assertTrue(facts["carrier"]["stored"].endswith(carrier), "carrier normalized")
        # Transit: B stores A's octets with B's identity spliced into Path; the
        # re-offer is refused by Message-ID.
        for name in carried:
            a_octets, b_octets = facts[name]["stored"], facts[name]["b"]
            # RFC 5537 s3.2.1: B prepends its identity and "!", then an empty
            # path-diagnostic and "!" because A's identity matched the peer
            # record ("!!", the verified hop; fn-pu-edit-path).
            self.assertEqual(b_octets,
                             a_octets.replace(b"Path: ", b"Path: b.corpus.invalid!!", 1), name)
            self.assertTrue(facts[name]["b-ihave"].startswith("435"), facts[name])
            self.assertEqual(facts[name]["reopened"], (facts[name]["number"],
                                                       facts[name]["stored"]), name)
            self.assertEqual(facts[name]["inspect-a"], facts[name]["stored"], name)
            self.assertEqual(facts[name]["inspect-b"], facts[name]["b"], name)
        for name in ("supplied-date", "generated-date", "client-path", "mime"):
            self.assertEqual(facts[name]["retry-after-reopen"].encode(), ALREADY, name)

    # -- the signed control route's retry --------------------------------------
    def test_signed_route_retry_is_already_stored(self):
        """The contract of every injecting route (D25, NNT-020): the same
        signed source authored again through `hybrid-author` is the article
        already stored, not an error, and adds no article.  RED on the image
        of e79286bf: the route commits through fn-owner-prepare-identity with
        no existing-action verdict (PKT-166, decided: the route now asks
        fn-owner-existing-action first)."""
        a = self.initialize("s", ["fn.test"], "s.corpus.invalid")
        self.start(a)
        keys = self.keys(a)
        self.command([IMAGE, "--fn", "hybrid-enroll", a["control"], "1", keys["principal"],
                      keys["ed_public"], keys["ml_public"]])
        signed = (CORPUS / "signed.article").read_bytes()
        first = self.author(a, keys, "first", signed)
        first_detail = self.last_author
        before = self.served(a)
        time.sleep(1.2)
        again = self.author(a, keys, "again", signed, signatures="first")
        again_detail = self.last_author
        resigned = self.author(a, keys, "resigned", signed)
        resigned_detail = self.last_author
        after = self.served(a)
        self.stop(a)
        print("SOURCE-CORPUS-SIGNED-RETRY " + json.dumps(
            {"first": first_detail, "again": again_detail, "resigned": resigned_detail,
             "before": sorted(before), "after": sorted(after)}, sort_keys=True))
        self.assertEqual(first, 0, first_detail)
        self.assertEqual(sorted(after), sorted(before))
        self.assertEqual(again, 0, again_detail)
        self.assertIn("DUPLICATE", again_detail[2], again_detail)
        # The same source signed afresh is another carrier (hedged ML-DSA-65):
        # a changed authored source under the held Message-ID, the conflict.
        self.assertEqual(resigned, 1, resigned_detail)
        self.assertIn("REFUSED", resigned_detail[2], resigned_detail)
        # A changed signed source under the held Message-ID is the conflict:
        # a refusal (exit 1), not an acceptance, with its word printed.
        self.start(a)
        other = self.author(a, keys, "other", changed(signed))
        other_detail = self.last_author
        after_other = self.served(a)
        self.stop(a)
        print("SOURCE-CORPUS-SIGNED-CONFLICT " + json.dumps(
            {"other": other_detail, "after": sorted(after_other)}, sort_keys=True))
        self.assertEqual(other, 1, other_detail)
        self.assertIn("REFUSED", other_detail[2], other_detail)
        self.assertEqual(sorted(after_other), sorted(before))

    # -- cancel order, pinned reader, Supersedes, replay ------------------------
    def test_cancel_orders_pinned_reader_and_replay(self):
        a = self.initialize("c", ["fn.test", "control.cancel"], "c.corpus.invalid")
        self.start(a)
        keys = self.keys(a)
        self.command([IMAGE, "--fn", "hybrid-enroll", a["control"], "1", keys["principal"],
                      keys["ed_public"], keys["ml_public"]])

        def source(message_id, subject, extra=b""):
            return (b"From: poster@example.invalid\r\nNewsgroups: fn.test\r\nSubject: "
                    + subject + b"\r\nDate: Fri, 25 Sep 2026 12:00:00 +0000\r\n"
                    + b"Message-ID: " + message_id.encode() + b"\r\n" + extra
                    + b"\r\nbody\r\n")

        t1, c1 = "<sc-t1@example.invalid>", "<sc-c1@example.invalid>"
        t2, c2 = "<sc-t2@example.invalid>", "<sc-c2@example.invalid>"
        t3, s3 = "<sc-t3@example.invalid>", "<sc-s3@example.invalid>"
        codes = {}
        empty = self.served(a)
        # Target then cancel, with a reader pinned before the cancel.
        codes["t1"] = self.author(a, keys, "t1", source(t1, b"t1"))
        client, pinned = self.connect(a)
        with client:
            pinned_before = self.ask(pinned, b"ARTICLE " + t1.encode() + b"\r\n")[0]
            codes["c1"] = self.author(a, keys, "c1", source(
                c1, b"cancel t1", b"Control: cancel " + t1.encode() + b"\r\n"))
            fresh_after = self.article(a, t1)[0]
            pinned_after = self.ask(pinned, b"ARTICLE " + t1.encode() + b"\r\n")[0]
        # Cancel then target.
        codes["c2"] = self.author(a, keys, "c2", source(
            c2, b"cancel t2", b"Control: cancel " + t2.encode() + b"\r\n"))
        codes["t2"] = self.author(a, keys, "t2", source(t2, b"t2"))
        # Supersedes: S3 withdraws T3 under the cancel's rules and stays visible.
        codes["t3"] = self.author(a, keys, "t3", source(t3, b"t3"))
        codes["s3"] = self.author(a, keys, "s3", source(
            s3, b"s3", b"Supersedes: " + t3.encode() + b"\r\n"))
        live = {m: self.article(a, m)[0].decode() for m in (t1, t2, t3, s3)}
        live_view = sorted(self.served(a))
        # Replay: SIGKILL and reopen.
        self.stop(a, kill=True)
        self.start(a)
        replayed = {m: self.article(a, m)[0].decode() for m in (t1, t2, t3, s3)}
        replayed_view = sorted(self.served(a))
        self.stop(a)
        witness = {"codes": codes, "pinned_before": pinned_before.decode(),
                   "pinned_after": pinned_after.decode(), "fresh_after": fresh_after.decode(),
                   "live": live, "replayed": replayed, "live_view": live_view,
                   "replayed_view": replayed_view, "empty": sorted(empty)}
        print("SOURCE-CORPUS-CANCEL " + json.dumps(witness, sort_keys=True))
        self.assertTrue(all(code == 0 for code in codes.values()), codes)
        self.assertTrue(pinned_before.startswith(b"220"), witness)
        self.assertTrue(pinned_after.startswith(b"220"), witness)
        self.assertTrue(fresh_after.startswith(b"430"), witness)
        # visible(T then C) = visible(C then T): both targets withdrawn from
        # every fresh view, live and after replay.
        for view in (live, replayed):
            self.assertTrue(view[t1].startswith("430"), witness)
            self.assertTrue(view[t2].startswith("430"), witness)
            self.assertTrue(view[t3].startswith("430"), witness)
            self.assertTrue(view[s3].startswith("220"), witness)
        self.assertEqual(live_view, [s3], witness)
        self.assertEqual(replayed_view, live_view, witness)


if __name__ == "__main__":
    unittest.main()

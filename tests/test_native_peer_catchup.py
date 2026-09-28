"""Opt-in native witness for catching up from a peer (NNT-053, SCN-184, PRF-325).

Node A holds 1,000 articles in fn.test.  Node B, new, is configured with A
as a peer (inbound fn.*, dialled by B only) and `peer catch-up A 2`: B's
owner asks A for XFNCATCHUP batches (books/peer-catchup-serve.lisp on A),
verifies each batch's digest chain and offers its records by IHAVE to
itself (books/peer-catchup.lisp, host/native/pull-service.lisp).

- test_catch_up_imports_every_article: B ends with the same Message-IDs in
  fn.test as A, every article's octets equal A's apart from the Path line
  (B's acceptance adds its own identity) and neither node's Xref is
  compared (numbers are each node's own; B numbers in A's log order).  B's
  log names a done round at position 1000 whose digest is the chain over
  A's 1,000 stored articles, recomputed here from A's ARTICLE replies.
- test_kill_mid_catch_up_resumes: B is started with
  FN_CATCHUP_TEST_KILL=before-write:3 (developer image): it dies by SIGKILL
  after committing the third batch's records and before journaling that
  batch's cursor.  Restarted, it resumes from the second batch's cursor: the
  third batch is offered again and drawn 435 (duplicate), and B ends with
  exactly A's articles, none twice.

Run: FN_NATIVE_HOST=<launcher> FN_NATIVE_DEVELOPER_HOST=<developer launcher> \
     python3 -m unittest -v tests.test_native_peer_catchup
"""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import time
import unittest

from tests.native_harness import EXIT_OK, ROOT, Client, Node, native_image, scratch
import sys
sys.path.insert(0, str(ROOT / "tools"))
import blake3_ref  # noqa: E402  fn's digest (books/blake3.lisp), store format 10

# The images must be named explicitly.
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = native_image("FN_NATIVE_HOST") if IMAGE_TEXT else None
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))
# FN_CATCHUP_TEST_KILL is a developer-image selector; a production image
# refuses to start with it by name.
DEVELOPER_TEXT = os.environ.get("FN_NATIVE_DEVELOPER_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST") if DEVELOPER_TEXT else None
COUNT = int(os.environ.get("FN_CATCHUP_ARTICLES", "1000"))
INTERVAL = "2"
# The store both nodes use, named: 1,000 articles of about 2.3 KiB are
# about 2.3 MiB of history on each node, which the default init's sizing
# for this process refuses early ("no capacity"); 64 MiB of history and
# 32 KiB articles hold them with room.
PROFILE = ("--max-transactions", "16384", "--max-history-octets", str(64 << 20),
           "--max-record-octets", "196608", "--max-article-octets", "32768",
           "--max-groups-per-article", "16", "--max-open-suffix", "128")
# About 2 KiB of body per article, so the 256 KiB batch quantum makes
# several batches of the 1,000.
FILLER = ("catch-up filler line " * 4 + "\r\n") * 24


def sha256_of(path):
    try:
        return hashlib.sha256(Path(path).read_bytes()).hexdigest()
    except OSError:
        return None


def message_id(n):
    return "<catchup-{:05d}@example.invalid>".format(n)


def article(n):
    lines = ["From: poster@example.invalid", "Newsgroups: fn.test",
             "Subject: catch-up {}".format(n),
             "Date: Sun, 27 Sep 2026 20:00:00 +0000",
             "Message-ID: " + message_id(n)]
    body = "article {}\r\n.a line that begins with a dot\r\n".format(n) + FILLER
    return ("\r\n".join(lines) + "\r\n\r\n" + body).encode("ascii")


def listgroup(client, group):
    status, body = client.multiline("LISTGROUP " + group)
    if not status.startswith(b"211"):
        return status, []
    return status, [int(line) for line in body.split(b"\r\n") if line]


def without_path_and_xref(octets):
    head, _, body = octets.partition(b"\r\n\r\n")
    kept = [l for l in head.split(b"\r\n")
            if not (l.lower().startswith(b"path:") or l.lower().startswith(b"xref:"))]
    return b"\r\n".join(kept) + b"\r\n\r\n" + body


def chain_step(chain, msgid, octets):
    return blake3_ref.blake3(chain + blake3_ref.blake3(octets)
                             + msgid.encode("ascii"))


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a native launcher")
class NativePeerCatchupTests(unittest.TestCase):
    def setUp(self):
        self.base = scratch(self, "fn-native-catchup-")
        self.evidence = Path(os.environ.get("FN_CATCHUP_EVIDENCE", self.base / "evidence"))
        self.evidence.mkdir(parents=True, exist_ok=True)
        self.nodes = []
        self.addCleanup(self.keep_logs)

    def keep_logs(self):
        for node in self.nodes:
            prefix = "{}-{}-".format(self._testMethodName, node.name)
            if node.log.exists():
                shutil.copyfile(node.log, self.evidence / (prefix + "fn.log"))
            if node.processes:
                (self.evidence / (prefix + "stderr.log")).write_bytes(
                    b"".join(process.stderr.since(0) for process in node.processes))

    # ------------------------------------------------------------ nodes

    def initialize(self, name, identity):
        node = Node(self, IMAGE, root=self.base / name, name=name)
        node.log = node.root / "fn.log"
        node.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                node.store_path, node.port, node.control, node.log), encoding="ascii")
        node.operator("init", *PROFILE, "fn.test", expect=EXIT_OK)
        self.nodes.append(node)
        node.operator("policy", "set", "path-identity", identity, expect=EXIT_OK)
        return node

    def catch_up_from(self, node, name, identity, port):
        """NAME is a peer B dials only: inbound fn.*, outbound none; its
        source address is one no socket here uses."""
        node.operator("peer", "add", name, identity, "127.0.0.1", str(port), "fn.*", "-",
                      "source-address", "127.0.0.9", "true", expect=EXIT_OK)
        node.operator("peer", "catch-up", name, INTERVAL, expect=EXIT_OK)

    def start(self, node, extra_env=None):
        image = None
        if extra_env:
            if DEVELOPER is None or not os.access(DEVELOPER, os.X_OK):
                self.skipTest("set FN_NATIVE_DEVELOPER_HOST: the FN_CATCHUP_TEST_KILL cuts")
            image = DEVELOPER
        node.start(image=image, env=extra_env)

    def stop(self, node):
        node.stop(expect=None)

    def log_lines(self, node):
        try:
            return [l for l in node.log.read_text(errors="replace").splitlines()
                    if "catch-up peer=" in l]
        except OSError:
            return []

    def await_log(self, node, pattern, timeout=600):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            for line in self.log_lines(node):
                if re.search(pattern, line):
                    return line
            process = node.process
            if process is not None and process.poll() is not None:
                break
            time.sleep(0.5)
        self.fail("{}: no catch-up line matching {!r}; lines: {}; log tail: {}".format(
            node.name, pattern, self.log_lines(node)[-5:],
            node.log.read_text(errors="replace")[-2000:] if node.log.exists() else ""))

    # ------------------------------------------------------------ fixtures

    def populated_a(self):
        a = self.initialize("A", "a.catchup.example.invalid")
        self.start(a)
        with Client(a.port, timeout=60) as client:
            for n in range(COUNT):
                first, second = client.post(article(n))
                assert first.startswith(b"340"), first
                assert second.startswith(b"240"), second
        return a

    def articles_of(self, node):
        """{msgid: stored octets} of fn.test, and the numbers in order."""
        with Client(node.port, timeout=60) as client:
            status, numbers = listgroup(client, "fn.test")
            self.assertTrue(status.startswith(b"211"), status)
            out = {}
            order = []
            for number in numbers:
                status, octets = client.multiline("ARTICLE {}".format(number))
                self.assertTrue(status.startswith(b"220"), status)
                msgid = status.split()[2].decode("ascii")
                self.assertNotIn(msgid, out)
                out[msgid] = octets
                order.append(msgid)
            return out, order

    def expected_digest(self, a_articles, a_order):
        chain = bytes(32)
        for msgid in a_order:
            chain = chain_step(chain, msgid, without_xref(a_articles[msgid]))
        return chain.hex()

    def compare(self, a, b):
        a_articles, a_order = self.articles_of(a)
        b_articles, b_order = self.articles_of(b)
        self.assertEqual(len(a_articles), COUNT)
        self.assertEqual(sorted(b_articles), sorted(a_articles))
        # B numbered them in A's log order: catch-up is oldest first.
        self.assertEqual(b_order, a_order)
        for msgid, octets in a_articles.items():
            self.assertEqual(without_path_and_xref(b_articles[msgid]),
                             without_path_and_xref(octets), msgid)
        return a_articles, a_order

    def fncu_frames(self, node):
        data = (node.store_path / "catch-up" / "A.fnfd").read_bytes()
        frames, at = [], 0
        while at + 4 <= len(data):
            size = int.from_bytes(data[at:at + 4], "big")
            frames.append(size)
            at += 4 + size
        self.assertEqual(at, len(data), "a torn FNCU tail")
        return frames

    def witness(self, kind, data, nodes):
        data = dict(data, kind=kind)
        for node in nodes:
            keep = self.evidence / "{}-{}.log".format(kind, node.name)
            if node.log.exists():
                shutil.copyfile(node.log, keep)
            data["log_sha256_" + node.name] = sha256_of(node.log)
        data["image_sha256"] = sha256_of(IMAGE)
        (self.evidence / (kind + ".witness.json")).write_text(
            json.dumps(data, sort_keys=True, indent=1), encoding="utf-8")
        print("NATIVE-CATCHUP-WITNESS " + json.dumps(data, sort_keys=True), flush=True)

    # ------------------------------------------------------------ cases

    def test_catch_up_imports_every_article(self):
        a = self.populated_a()
        b = self.initialize("B", "b.catchup.example.invalid")
        self.catch_up_from(b, "A", "a.catchup.example.invalid", a.port)
        started = time.monotonic()
        self.start(b)
        done = self.await_log(b, r"catch-up peer=A round=done position={} ".format(COUNT))
        elapsed = time.monotonic() - started
        a_articles, a_order = self.compare(a, b)
        digest = re.search(r"digest=([0-9a-f]{64})", done).group(1)
        self.assertEqual(digest, self.expected_digest(a_articles, a_order))
        first = [l for l in self.log_lines(b) if "round=done" in l][0]
        imported = int(re.search(r"imported=(\d+)", first).group(1))
        self.assertEqual(imported, COUNT, first)
        journals = sorted(str(p.relative_to(b.store_path)) for p in
                          (b.store_path / "catch-up").rglob("*") if p.is_file())
        self.stop(b)
        self.stop(a)
        self.witness("catch-up", {"articles": COUNT, "done_line": done,
                                  "seconds_to_done": round(elapsed, 2),
                                  "digest": digest, "journals": journals,
                                  "lines": self.log_lines(b)}, [a, b])
        self.assertTrue(journals, "no FNCU journal under the store's catch-up directory")

    def test_kill_mid_catch_up_resumes(self):
        a = self.populated_a()
        b = self.initialize("B", "b.catchup.example.invalid")
        self.catch_up_from(b, "A", "a.catchup.example.invalid", a.port)
        self.start(b, extra_env={"FN_CATCHUP_TEST_KILL": "before-write:3"})
        code = b.process.wait(timeout=600)
        b.process.finish()
        self.assertEqual(code, -signal.SIGKILL,
                         "B was to die at the third FNCU append; log: {}".format(
                             b.log.read_text(errors="replace")[-2000:]))
        # The cut's own line goes to the owner's log queue, which a SIGKILL
        # may not let drain; the journal is the evidence: two FNCU cursor
        # frames (four-octet length, then the frame), the third never written.
        frames = self.fncu_frames(b)
        self.assertEqual(len(frames), 2, frames)
        killed_lines = self.log_lines(b)
        self.start(b)
        done = self.await_log(b, r"catch-up peer=A round=done position={} ".format(COUNT))
        a_articles, a_order = self.compare(a, b)
        digest = re.search(r"digest=([0-9a-f]{64})", done).group(1)
        self.assertEqual(digest, self.expected_digest(a_articles, a_order))
        duplicate = int(re.search(r"duplicate=(\d+)", done).group(1))
        imported = int(re.search(r"imported=(\d+)", done).group(1))
        # The third batch was committed before the cut and offered again.
        self.assertGreater(duplicate, 0, done)
        self.assertLess(imported + duplicate, COUNT, done)
        self.stop(b)
        self.stop(a)
        self.witness("catch-up-kill", {"articles": COUNT, "done_line": done,
                                       "before_kill": killed_lines,
                                       "frames_at_the_cut": frames,
                                       "lines": self.log_lines(b)}, [a, b])


def without_xref(octets):
    head, _, body = octets.partition(b"\r\n\r\n")
    kept = [l for l in head.split(b"\r\n") if not l.lower().startswith(b"xref:")]
    return b"\r\n".join(kept) + b"\r\n\r\n" + body


if __name__ == "__main__":
    unittest.main()

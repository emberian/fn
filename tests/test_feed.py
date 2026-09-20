#!/usr/bin/env python3
"""`tools/run_feed.py` against a fake peer, and across a crash mid-transfer.

The peer is `tests/twonode_gate_fake/tools/run_peer.py`, a line filter over
the deploy gate's fake reader that answers IHAVE / CHECK / TAKETHIS.  Its
replies are that file's, not ACL2's, so a green run here says the feed driver
speaks RFC 3977 section 6.3.2 and RFC 4644 correctly and journals what it
decided; it says nothing about a real peer.  The INN scenarios of
specs/peering.md section 5 are what would.

The two cases that matter:

  * `test_two_articles_are_offered_once_each`: a two-article feed finishes
    both, and the FNFD journal holds exactly one accepted outcome per
    Message-ID.
  * `test_a_crash_between_sent_and_outcome_resolves_by_check`: the driver is
    killed at the `(:feed-sent ...)` record boundary, before the peer's
    response is journaled.  On restart the first command for that article is
    a CHECK -- never a blind TAKETHIS -- and the peer, which already has the
    article, answers 438; the peer's store holds exactly one copy.

Every case is skipped, never faked, when ACL2 or the certified feed books are
not on this tree: `tools/run_feed.py` runs the proved machine or nothing.
"""
from __future__ import annotations

import os
import shutil
import socket
import struct
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

ACL2 = os.environ.get("FN_ACL2", "acl2")
HAVE_ACL2 = shutil.which(ACL2) is not None
HAVE_BOOKS = (ROOT / "books/peer-feed.cert").exists()
REASON = "needs ACL2 and a certified books/peer-feed"

ARTICLE = ("Path: peer.example.invalid!not-for-mail\r\n"
           "From: t <t@fn.invalid>\r\n"
           "Newsgroups: fn.letters\r\n"
           "Subject: {}\r\n"
           "Message-ID: {}\r\n"
           "Date: Sat, 20 Sep 2026 00:00:00 +0000\r\n"
           "\r\n"
           "body {}\r\n")


def free_port() -> int:
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


class FakePeer:
    """The two-node gate's fake transit peer, in its own directory."""

    def __init__(self, workdir: Path):
        self.dir = workdir / "peer"
        (self.dir / "tools").mkdir(parents=True)
        for overlay in ("deploy_gate_fake", "twonode_gate_fake"):
            source = ROOT / "tests" / overlay / "tools"
            for entry in source.iterdir():
                shutil.copy(entry, self.dir / "tools" / entry.name)
        self.store = self.dir / "store"
        self.store.mkdir()
        self.proc = subprocess.Popen(
            [sys.executable, str(self.dir / "tools/run_peer.py"),
             "--store", str(self.store), "--port", "0",
             "--path-identity", "peer.example.invalid"],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        line = self.proc.stdout.readline().decode()
        if not line.startswith("LISTENING "):
            raise RuntimeError("fake peer did not start: " + line)
        self.port = int(line.split()[1])

    def holds(self):
        import json
        path = self.store / "store.json"
        if not path.exists():
            return []
        return [a["msgid"] for a in json.loads(path.read_text())["articles"]]

    def stop(self):
        self.proc.kill()
        self.proc.wait(timeout=10)


def journal_records(path: Path):
    """The FNFD file's frames, by the host's own 4-octet length prefix."""
    blob = path.read_bytes() if path.exists() else b""
    offset, out = 0, []
    while offset + 4 <= len(blob):
        (length,) = struct.unpack(">I", blob[offset:offset + 4])
        offset += 4
        if offset + length > len(blob):
            break
        out.append(blob[offset:offset + length])
        offset += length
    return out


@unittest.skipUnless(HAVE_ACL2 and HAVE_BOOKS, REASON)
class FeedTests(unittest.TestCase):

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-feed-")
        self.work = Path(self.temp.name)
        self.peer = FakePeer(self.work)
        self.articles = {}
        for name in ("a", "b"):
            msgid = "<{}@fn.invalid>".format(name)
            path = self.work / (name + ".art")
            path.write_text(ARTICLE.format(name, msgid, name))
            self.articles[msgid] = path
        self.journal = self.work / "journal"
        self.journal.mkdir()

    def tearDown(self):
        self.peer.stop()
        self.temp.cleanup()

    def drive(self, fault=None, msgids=None, extra=()):
        argv = [sys.executable, str(ROOT / "tools/run_feed.py"),
                "--journal", str(self.journal), "--peer", "inn",
                "--port", str(self.peer.port), "--deadline", "90"]
        for msgid, path in self.articles.items():
            if msgids is None or msgid in msgids:
                argv += ["--article", "{}={}".format(msgid, path)]
        if fault:
            argv += ["--fault", fault]
        argv += list(extra)
        return subprocess.run(argv, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=900)

    def outcomes(self):
        """One decoded FNFD outcome per record, as (msgid, code) pairs."""
        pairs = []
        for frame in journal_records(self.journal / "feed/inn.fnfd"):
            text = frame[len(b"FNFD") + 4:]
            for msgid in self.articles:
                if msgid.encode() in text:
                    pairs.append((msgid, frame))
        return pairs

    def test_two_articles_are_offered_once_each(self):
        done = self.drive()
        self.assertEqual(done.returncode, 0, done.stdout.decode()[-3000:])
        text = done.stdout.decode()
        for msgid in self.articles:
            self.assertIn("FINAL {} :DONE".format(msgid), text)
        self.assertEqual(sorted(self.peer.holds()), sorted(self.articles))
        # One accepted outcome per article: 239 appears once per Message-ID.
        for msgid in self.articles:
            self.assertEqual(text.count("OUTCOME {} 239".format(msgid)), 1)

    def test_a_crash_between_sent_and_outcome_resolves_by_check(self):
        one = list(self.articles)[:1]
        crashed = self.drive(fault="after-sent", msgids=one)
        self.assertEqual(crashed.returncode, 4, crashed.stdout.decode()[-2000:])
        before = len(journal_records(self.journal / "feed/inn.fnfd"))
        self.assertGreaterEqual(before, 3)   # enqueue, offer, sent

        # The peer never saw the article: the kill was before the block.
        self.assertEqual(self.peer.holds(), [])

        again = self.drive(msgids=one)
        self.assertEqual(again.returncode, 0, again.stdout.decode()[-3000:])
        text = again.stdout.decode()
        self.assertIn("REPLAYED {}".format(before), text)
        self.assertIn("FINAL {} :DONE".format(one[0]), text)
        # Exactly one copy at the peer, whichever way the re-offer went.
        self.assertEqual(self.peer.holds(), one)

    def test_a_crash_after_the_article_is_answered_438_not_a_second_copy(self):
        one = list(self.articles)[:1]
        first = self.drive(msgids=one)
        self.assertEqual(first.returncode, 0, first.stdout.decode()[-2000:])
        self.assertEqual(self.peer.holds(), one)

        # A second driver over a FRESH journal re-offers the same article; the
        # peer's own history is what makes that safe (RFC 5537 section 3.3).
        second = tempfile.TemporaryDirectory(prefix="fn-feed-2-")
        self.addCleanup(second.cleanup)
        argv = [sys.executable, str(ROOT / "tools/run_feed.py"),
                "--journal", second.name, "--peer", "inn",
                "--port", str(self.peer.port), "--deadline", "90",
                "--article", "{}={}".format(one[0], self.articles[one[0]])]
        run = subprocess.run(argv, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, timeout=900)
        self.assertEqual(run.returncode, 0, run.stdout.decode()[-2000:])
        self.assertIn("OUTCOME {} 438".format(one[0]), run.stdout.decode())
        self.assertEqual(self.peer.holds(), one)


class FramingTests(unittest.TestCase):
    """What can be checked with no ACL2: the journal file's own layout."""

    def test_a_torn_tail_ends_the_record_stream(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "inn.fnfd"
            path.write_bytes(struct.pack(">I", 4) + b"abcd" +
                             struct.pack(">I", 99) + b"xy")
            self.assertEqual(journal_records(path), [b"abcd"])


if __name__ == "__main__":
    unittest.main()

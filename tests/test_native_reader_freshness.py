"""R1 probe: does a long-lived reader connection see a new article?

The NNTP gap inventory (planning/nntp-gap-inventory-2026-09-26.md, R1) says a
reader connection keeps the view it pinned at open, and that only the poster
is re-pinned after its own 240 (specs/nntp.md "Read-back").  RFC 3977
section 6.1.1's 211 reports the group as it is now; pan and Thunderbird keep
connections open.  This module MEASURES that on the native owner and fixes
nothing (the fix is held for the consolidation's delta interface).

Two arrivals, each seen by a reader that opened and selected the group
before the article existed:

  * another connection's POST (store A, no peers), and
  * a peer's IHAVE (store B, a source-address peer on 127.0.0.1; the
    long-lived reader connects from 127.0.0.2 so it stays a reader).

After each arrival the long-lived reader sends GROUP, LISTGROUP, STAT
<message-id> and ARTICLE <message-id>; a fresh connection sends the same
as the control.  Every reply line is printed as `R1-OBSERVED` JSON on
stderr (the module log is the evidence; tools/hbox_native.sh records its
SHA-256).

Until 2026-09-26 this module measured and asserted nothing about the
freshness answer (R1 was observed STALE in batch AG, log afd76501).  Since
NNT-042 (specs/nntp.md: a successful GROUP or LISTGROUP acquires a fresh
coherent view; catalog-slice-5) the answer is specified, and the module
asserts it: after the arrival the long-lived reader's GROUP reports the
new count and its STAT/ARTICLE by Message-ID answer 223/220, exactly as a
fresh connection's do.  The controls (the arrival was accepted, a fresh
connection sees it) stay.
"""
import json
import os
import sys
import unittest

from tests.native_harness import (
    EXIT_OK, ROOT, Client, Node, environment, native_image, native_peer_add)

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
GROUP = b"fn.test"


def article(message_id, subject=b"freshness probe"):
    return (b"From: probe@example.invalid\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: " + subject + b"\r\n"
            b"Date: Sat, 26 Sep 2026 12:00:00 +0000\r\n"
            b"Path: source.invalid!not-for-mail\r\n"
            b"Message-ID: " + message_id + b"\r\n\r\n"
            b"a freshness probe body\r\n")


def text(line):
    return line.decode("latin-1").rstrip("\r\n")


def view(conn, message_id):
    group = text(conn.command("GROUP fn.test"))
    listgroup_line, numbers = conn.multiline("LISTGROUP fn.test")
    stat = text(conn.command("STAT " + message_id))
    art, _ = conn.multiline("ARTICLE " + message_id)
    return {"GROUP": group, "LISTGROUP": text(listgroup_line),
            "numbers": numbers.decode("latin-1").split("\r\n")[:-1],
            "STAT": stat, "ARTICLE": text(art)}


def sees(observed):
    return observed["STAT"].startswith("223 ") and observed["ARTICLE"].startswith("220 ")


class ReaderFreshnessProbe(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.access(IMAGE, os.X_OK):
            raise unittest.SkipTest(
                "developer native image missing: {} "
                "(FN_NATIVE_PROFILE=developer tools/build_native_host.sh)".format(IMAGE))

    def setUp(self):
        self.node = Node(self, IMAGE, listener=False, control=False)
        self.store = self.node.store_path
        self.node.store("init", "fn.test", expect=EXIT_OK)

    def record(self, arrival, long_lived_before, long_lived_after, fresh):
        row = {"arrival": arrival, "long_lived_before": long_lived_before,
               "long_lived_after": long_lived_after, "fresh_connection": fresh,
               "long_lived_sees_it": sees(long_lived_after),
               "long_lived_group_moved":
                   long_lived_after["GROUP"] != long_lived_before["GROUP"]}
        print("R1-OBSERVED " + json.dumps(row, sort_keys=True), file=sys.stderr)
        sys.stderr.flush()
        return row

    def probe(self, arrival, port, arrive, message_id, source=None):
        long_lived = Client(port, timeout=30, source=source)
        self.addCleanup(long_lived.close)
        before = view(long_lived, message_id)
        self.assertTrue(before["GROUP"].startswith("211 "), before)
        self.assertFalse(sees(before), before)
        arrive()
        after = view(long_lived, message_id)
        fresh_conn = Client(port, timeout=30, source=source)
        self.addCleanup(fresh_conn.close)
        fresh = view(fresh_conn, message_id)
        row = self.record(arrival, before, after, fresh)
        # The control: the arrival is visible to a connection opened after it.
        self.assertTrue(sees(fresh), fresh)
        # NNT-042: the long-lived reader's GROUP acquired the fresh view, so
        # it sees what the fresh connection sees, and its 211 moved.
        self.assertTrue(row["long_lived_sees_it"], after)
        self.assertTrue(row["long_lived_group_moved"], (before["GROUP"], after["GROUP"]))
        self.assertEqual(after["GROUP"], fresh["GROUP"], (after["GROUP"], fresh["GROUP"]))
        self.assertEqual(after["numbers"], fresh["numbers"], (after["numbers"], fresh["numbers"]))
        return row

    def test_another_connections_post(self):
        _, port = self.node.start_store_owner(once=False)
        message_id = "<r1-post@example.invalid>"

        def post():
            with Client(port, timeout=30) as poster:
                first, reply = poster.post(article(message_id.encode()))
                self.assertTrue(first.startswith(b"340 "), first)
                self.assertTrue(reply.startswith(b"240 "), reply)

        self.probe("another connection's POST", port, post, message_id)

    def test_a_peers_ihave(self):
        configured = native_peer_add(
            IMAGE, self.store, ["source", "source.invalid", "127.0.0.1", "9", "fn.*", "-",
                                "127.0.0.1", "true"], environment(), ROOT)
        self.assertEqual(configured.returncode, 0, configured.stderr.decode())
        _, port = self.node.start_store_owner(once=False)
        message_id = "<r1-ihave@example.invalid>"

        def ihave():
            with Client(port, timeout=30) as peer:
                first, reply = peer.post(article(message_id.encode(), b"via a peer"),
                                         verb="IHAVE " + message_id)
                self.assertTrue(first.startswith(b"335 "), first)
                self.assertTrue(reply.startswith(b"235 "), reply)

        # The reader connects from 127.0.0.2, which no peer record names.
        self.probe("a peer's IHAVE", port, ihave, message_id, source="127.0.0.2")


if __name__ == "__main__":
    unittest.main()

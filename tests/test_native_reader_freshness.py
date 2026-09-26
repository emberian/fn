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
SHA-256).  The assertions are the controls -- the arrival was accepted and
a fresh connection sees it -- plus one statement of what the long-lived
connection saw, whichever it was: the test fails only when the harness or
the control fails, never on the freshness answer, which is the measurement.
"""
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
GROUP = b"fn.test"


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    return env


def article(message_id, subject=b"freshness probe"):
    return (b"From: probe@example.invalid\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: " + subject + b"\r\n"
            b"Date: Sat, 26 Sep 2026 12:00:00 +0000\r\n"
            b"Path: source.invalid!not-for-mail\r\n"
            b"Message-ID: " + message_id + b"\r\n\r\n"
            b"a freshness probe body\r\n")


class Conn:
    def __init__(self, port, source=None):
        self.sock = socket.create_connection(
            ("127.0.0.1", port), timeout=30,
            source_address=(source, 0) if source else None)
        self.stream = self.sock.makefile("rwb", buffering=0)
        self.greeting = self.line()

    def line(self):
        return self.stream.readline().decode("latin-1").rstrip("\r\n")

    def cmd(self, text, multiline=False):
        self.stream.write(text.encode("latin-1") + b"\r\n")
        first = self.line()
        block = []
        if multiline and first[:1] in ("1", "2") and first[:3] not in ("205",):
            while True:
                line = self.line()
                if line in (".", ""):
                    break
                block.append(line)
        return first, block

    def close(self):
        try:
            self.stream.write(b"QUIT\r\n")
            self.stream.readline()
        except OSError:
            pass
        self.stream.close()
        self.sock.close()


def view(conn, message_id):
    group, _ = conn.cmd("GROUP fn.test")
    listgroup_line, numbers = conn.cmd("LISTGROUP fn.test", multiline=True)
    stat, _ = conn.cmd("STAT " + message_id)
    art, _ = conn.cmd("ARTICLE " + message_id, multiline=True)
    return {"GROUP": group, "LISTGROUP": listgroup_line, "numbers": numbers,
            "STAT": stat, "ARTICLE": art}


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
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-r1-probe-")
        self.addCleanup(self.temporary.cleanup)
        self.store = Path(self.temporary.name) / "store"
        initialized = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "init", "fn.test"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())

    def start_owner(self):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "owner", "run", str(self.store), "0", "0", "8"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment())
        self.addCleanup(self.stop, process)
        line = wait_for_announcement(process, b"LISTENING ")
        if not line.startswith(b"LISTENING "):
            self.fail("native owner failed: {!r} {}".format(
                line, stop_and_diagnostics(process)))
        return int(line.split()[1])

    @staticmethod
    def stop(process):
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=10)
        for pipe in (process.stdout, process.stderr):
            if pipe:
                pipe.close()

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
        long_lived = Conn(port, source)
        self.addCleanup(long_lived.close)
        self.assertTrue(long_lived.greeting.startswith(("200 ", "201 ")),
                        long_lived.greeting)
        before = view(long_lived, message_id)
        self.assertTrue(before["GROUP"].startswith("211 "), before)
        self.assertFalse(sees(before), before)
        arrive()
        after = view(long_lived, message_id)
        fresh_conn = Conn(port, source)
        self.addCleanup(fresh_conn.close)
        fresh = view(fresh_conn, message_id)
        row = self.record(arrival, before, after, fresh)
        # The control: the arrival is visible to a connection opened after it.
        self.assertTrue(sees(fresh), fresh)
        # The measurement is stated, never asserted either way.
        self.assertIn(row["long_lived_sees_it"], (True, False))
        return row

    def test_another_connections_post(self):
        port = self.start_owner()
        message_id = "<r1-post@example.invalid>"

        def post():
            poster = Conn(port)
            try:
                first, _ = poster.cmd("POST")
                self.assertTrue(first.startswith("340 "), first)
                poster.stream.write(article(message_id.encode()) + b".\r\n")
                reply = poster.line()
                self.assertTrue(reply.startswith("240 "), reply)
            finally:
                poster.close()

        self.probe("another connection's POST", port, post, message_id)

    def test_a_peers_ihave(self):
        configured = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(self.store),
             "peer", "add", "source", "--path-identity", "source.invalid",
             "--nntp", "127.0.0.1:9", "--inbound-groups", "fn.*",
             "--source-address", "127.0.0.1"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(configured.returncode, 0, configured.stderr.decode())
        port = self.start_owner()
        message_id = "<r1-ihave@example.invalid>"

        def ihave():
            peer = Conn(port)
            try:
                first, _ = peer.cmd("IHAVE " + message_id)
                self.assertTrue(first.startswith("335 "), first)
                peer.stream.write(article(message_id.encode(), b"via a peer") + b".\r\n")
                reply = peer.line()
                self.assertTrue(reply.startswith("235 "), reply)
            finally:
                peer.close()

        # The reader connects from 127.0.0.2, which no peer record names.
        self.probe("a peer's IHAVE", port, ihave, message_id, source="127.0.0.2")


if __name__ == "__main__":
    unittest.main()

"""No blocking I/O under the owner mutex: the commit's batch job (lane
owner-offlock, 2026-10-03; r71 F6, r72 item 3, sweep S014;
books/owner-queued-work.lisp).

Before this lane a served POST's FNFD feed-journal intent frame was written
and fsynced inside the START quantum, its resolution frame inside the
COMPLETE quantum, and the log's extension and append inside START, all
holding the owner mutex: a slow or stalled feed-journal device stopped every
other connection's quanta (r71 F6).  Since, those effects are the batch
job's phases (intents, extend, append, fence, resolutions), run by the
syncer thread with no owner lock, in that order (fn-oqw-batch-effect-order),
and the owner consumes the job's receipt (fn-oqw-receipt).

The node is configured with one outbound feed peer (a refused port: no feed
is ever delivered, every POST still writes its intent and resolution
frames).  Developer selectors: FN_NATIVE_TEST_FEED_STALL_FILE (each FNFD
fsync waits while the file exists) and FN_NATIVE_TEST_FEED_FSYNC_MS (each
FNFD fsync takes MS longer).

  * a stalled feed journal holds a POST's batch, and meanwhile another
    connection's GROUP (a :reader quantum) and the operator's `health' (an
    :inspect quantum) answer at once; the device coming back answers 240;
  * the owner's hold per commit quantum (FN_OWNER_MEASURE=1, label
    `commit') stays below one FNFD fsync's injected latency, whatever that
    latency: the fsyncs are not inside any hold;
  * a duplicate POST, refused at its drain with frames to write, is still
    told its refusal (the job's :deliver item, after its resolution frame).
"""
import json
import os
import re
import socket
import threading
import time
import unittest

from tests.native_harness import EXIT_OK, Node, native_image, node_log_on_failure, refused_port, requires

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
MEASURE = re.compile(rb"^fn-owner-measure (\S+) holds=(\d+) held-us=(\d+) max-us=(\d+) bytes=(\d+)$", re.M)


def measured(log):
    """{label: (holds, held-us, max-us)} from the owner's FN_OWNER_MEASURE report."""
    return {m.group(1).decode(): tuple(int(m.group(i)) for i in (2, 3, 4))
            for m in MEASURE.finditer(log)}


@requires(DEVELOPER)
class OwnerOfflockNativeTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, DEVELOPER)
        self.root, self.port = self.node.root, self.node.port
        init = self.node.operator("init", "fn.test", timeout=120)
        self.assertEqual(init.returncode, 0, init.stderr.decode())
        self.reservation, down = refused_port()
        self.addCleanup(self.reservation.close)
        self.node.operator("peer", "add", "down", "down.example.invalid", "127.0.0.1",
                           str(down), "-", "fn.*", "127.0.0.2", "true", expect=EXIT_OK)
        self.stall = self.root / "feedstall"
        self.addCleanup(lambda: self.stall.unlink() if self.stall.exists() else None)

    def connect(self):
        conn = socket.create_connection(("127.0.0.1", self.port), timeout=120)
        self.addCleanup(conn.close)
        stream = conn.makefile("rwb")
        self.assertTrue(stream.readline().startswith(b"200"))
        return conn, stream

    def send_article(self, stream, msgid, body):
        stream.write(b"POST\r\n")
        stream.flush()
        line = stream.readline()
        self.assertTrue(line.startswith(b"340"), line)
        stream.write(b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                     b"Subject: offlock\r\nMessage-ID: <" + msgid + b">\r\n\r\n"
                     + body + b"\r\n.\r\n")
        stream.flush()

    def timed(self, stream, command, expect):
        started = time.monotonic()
        stream.write(command)
        stream.flush()
        line = stream.readline()
        self.assertTrue(line.startswith(expect), (command, line))
        return time.monotonic() - started

    def test_a_stalled_feed_journal_holds_no_owner_quantum(self):
        owner = self.node.start(env={"FN_NATIVE_TEST_FEED_STALL_FILE": str(self.stall)})
        with node_log_on_failure(owner):
            c1, s1 = self.connect()
            c2, s2 = self.connect()
            self.timed(s2, b"GROUP fn.test\r\n", b"211")
            self.stall.write_bytes(b"")
            self.send_article(s1, b"stalled@example.invalid", b"feed journal stalled")
            time.sleep(1.0)
            reads, healths = [], []
            for _ in range(4):
                reads.append(self.timed(s2, b"GROUP fn.test\r\n", b"211"))
                started = time.monotonic()
                health = self.node.operator("health", timeout=60)
                healths.append(time.monotonic() - started)
                self.assertEqual(health.returncode, 0, health.stderr.decode())
                time.sleep(0.5)
            c1.settimeout(0.5)
            try:
                early = s1.readline()
            except (socket.timeout, TimeoutError):
                early = b""
            c1.settimeout(120)
            stalled_for = 1.0 + sum(reads) + sum(healths) + 2.0
            self.stall.unlink()
            started = time.monotonic()
            line = early or s1.readline()
            answered = time.monotonic() - started
            print("OWNER-OFFLOCK-STALL-WITNESS " + json.dumps({
                "reader_s": [round(x, 3) for x in reads],
                "health_s": [round(x, 3) for x in healths],
                "post_reply_before_release": early.decode("ascii", "replace").strip(),
                "post_reply": line.decode("ascii", "replace").strip(),
                "post_answered_after_release_s": round(answered, 3),
                "stalled_for_s": round(stalled_for, 1)}, sort_keys=True), flush=True)
            # The POST's batch was held by the stalled journal, not answered.
            self.assertEqual(early, b"", early)
            self.assertTrue(line.startswith(b"240"), line)
            # Neither quantum waited for the stalled device.
            self.assertLess(max(reads), 1.0, reads)
            self.assertLess(max(healths), 3.0, healths)
            self.timed(s2, b"STAT <stalled@example.invalid>\r\n", b"223")

    def test_the_owner_hold_per_commit_excludes_the_feed_fsync(self):
        fsync_ms = int(os.environ.get("FN_OFFLOCK_FEED_FSYNC_MS", "100"))
        posts = int(os.environ.get("FN_OFFLOCK_POSTS", "12"))
        owner = self.node.start(env={"FN_OWNER_MEASURE": "1",
                                     "FN_NATIVE_TEST_FEED_FSYNC_MS": str(fsync_ms)})
        with node_log_on_failure(owner):
            conn, stream = self.connect()
            latency = []
            for i in range(posts):
                started = time.monotonic()
                self.send_article(stream, b"measure-%d@example.invalid" % i, b"measured %d" % i)
                line = stream.readline()
                latency.append(time.monotonic() - started)
                self.assertTrue(line.startswith(b"240"), line)
            stream.write(b"QUIT\r\n")
            stream.flush()
            conn.close()
            self.node.stop()
            log = owner.stderr.since(0)
            table = measured(log)
            print("OWNER-OFFLOCK-HOLD-WITNESS " + json.dumps({
                "feed_fsync_ms": fsync_ms, "posts": posts,
                "post_latency_ms": [round(1000 * x) for x in latency],
                "measure": {k: {"holds": v[0], "held_us": v[1], "max_us": v[2],
                                "mean_us": (v[1] // v[0]) if v[0] else 0}
                            for k, v in table.items()}}, sort_keys=True), flush=True)
            self.assertIn("commit", table, log[-4000:])
            holds, held, most = table["commit"]
            self.assertGreaterEqual(holds, posts, table)
            # Each POST crosses two FNFD fsyncs (intent, resolution) of
            # FSYNC_MS each; none of it is inside a commit quantum's hold.
            self.assertLess(most, fsync_ms * 1000, table)
            # ... while the POST itself still waits for both (it is answered
            # only after its frames and its barrier).
            self.assertGreaterEqual(min(latency), 2 * fsync_ms / 1000.0 * 0.9, latency)

    def test_a_refusal_with_frames_is_still_told(self):
        owner = self.node.start()
        with node_log_on_failure(owner):
            conn, stream = self.connect()
            self.send_article(stream, b"twice@example.invalid", b"first")
            self.assertTrue(stream.readline().startswith(b"240"))
            started = time.monotonic()
            self.send_article(stream, b"twice@example.invalid", b"second")
            line = stream.readline()
            print("OWNER-OFFLOCK-REFUSAL-WITNESS " + json.dumps({
                "reply": line.decode("ascii", "replace").strip(),
                "s": round(time.monotonic() - started, 3)}), flush=True)
            self.assertTrue(line.startswith(b"441"), line)
            self.timed(stream, b"DATE\r\n", b"111")


if __name__ == "__main__":
    unittest.main()

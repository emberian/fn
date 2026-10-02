"""A stalled disk on a native image (lane time-model, 2026-09-27; PRF-311,
HST-026, SCN-182; planning/design-time-model-2026-09-27.md).

The developer selector FN_NATIVE_TEST_DISK_STALL_FILE holds every batch
barrier before its fdatasync while the named file exists: a device that
does not return.  The disk is an adversarial environment with unbounded
latency; the node's answers are stated relative to it
(books/owner-time-model.lisp):

  * while the barrier is stalled for 30 s, `status' and `health' (the
    :inspect class) and a reader's GROUP and ARTICLE (the :reader class) are
    answered with latency flat, not growing with the stall
    (fn-otm-barrier-reader-bound: only :inspect and :commit quanta run
    before a waiting reader while the barrier is pending, and the barrier is
    no quantum);
  * past the barrier deadline (the default 5,000 ms) `health' and `status'
    say `disk slow: barrier N ms pending', and a NEW POST is refused at once
    with ACL2's try-later 441 and its reason, nothing stored
    (fn-otm-shed-iff-slow, fn-otm-shed-only-past-the-deadline);
  * the POST whose batch is in flight gets no answer while the device is
    stalled (a timeout is not a failure: it is pending), and its 240 once
    the device comes back (fn-ocs-members-told-only-after-the-barrier);
  * the completion is the recovery: `health' says `disk ok' with the
    barrier's latency and one slow episode, and the next POST is accepted
    (fn-otm-return-recovers).
"""
import json
import os
from pathlib import Path
import re
import select
import shutil
import signal
import socket
import subprocess
import threading
import time
import unittest

from tests.native_harness import ROOT, Node, native_image, node_log_on_failure, requires

# The developer image: the only one that honours a developer selector.
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
STALL_SECONDS = float(os.environ.get("FN_SLOW_DISK_STALL_SECONDS", "30"))
DISK_SLOW = re.compile(rb"^disk slow: barrier (\d+) ms pending deadline-ms=(\d+) stall-ms=(\d+) "
                       rb"slow-episodes=(\d+) stalls=(\d+) posts=try-later$", re.M)
DISK_STALLED = re.compile(rb"^disk stalled: barrier (\d+) ms pending deadline-ms=(\d+) stall-ms=(\d+) "
                          rb"slow-episodes=(\d+) stalls=(\d+) posts=try-later members=uncertain$", re.M)
DISK_OK = re.compile(rb"^disk ok: pending-ms=(\d+) last-barrier-ms=(\d+) max-barrier-ms=(\d+) "
                     rb"deadline-ms=(\d+) stall-ms=(\d+) slow-episodes=(\d+) stalls=(\d+)$", re.M)


def thread_count(pid):
    """Linux: /proc; OpenBSD: ps -H lists each kernel-visible thread."""
    status = Path("/proc/%d/status" % pid)
    if status.exists():
        for row in status.read_text().splitlines():
            if row.startswith("Threads:"):
                return int(row.split()[1])
    return len(subprocess.run(["ps", "-H", "-o", "pid=", "-p", str(pid)],
                              stdout=subprocess.PIPE, text=True).stdout.split())


class SlowDiskSourceTests(unittest.TestCase):
    """What the source has to say, whether or not an image was built."""

    def test_the_committer_waits_with_a_deadline_and_the_reader_sheds(self):
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text()
        pipeline = owner[owner.index("(defun fnn-owner-commit-pipeline "):
                         owner.index("(defun fnn-owner-loops-snapshot")]
        # The barrier's issue and completion are disk events; the wait for
        # the syncer is timed by ACL2 and its expiry appends a clock event.
        self.assertIn("(fnn-owner-disk-event service :issue limits)", pipeline)
        self.assertIn("(fnn-owner-disk-event service :return)", pipeline)
        self.assertIn("(fnn-owner-disk-event service :clock)", pipeline)
        self.assertIn("(fnn-owner-disk-wait-ms service)", pipeline)
        self.assertIn(":timeout (/ ms 1000)", pipeline)
        self.assertLess(pipeline.index("(fnn-owner-start-syncer service gen)"),
                        pipeline.index("(fnn-owner-disk-event service :issue limits)"))
        # Slice 2: past H every member is told uncertain, once per barrier,
        # and the queued POSTs are shed; the told members are not answered
        # again at the COMPLETE.
        self.assertIn("(fnn-owner-disk-stalled-p service)", pipeline)
        self.assertIn("(fnn-owner-stall-release", pipeline)
        self.assertIn("(fnn-owner-journal-note service (length told) shed)", pipeline)
        # Lane time-bars (PRF-384): ACL2's ledger decides who the late
        # completion answers; the syncer carries its generation.
        self.assertIn("(fnn-core 'fn-otb-issue ledger)", pipeline)
        self.assertIn("(fnn-owner-answer-early ledger (append members next))", pipeline)
        self.assertIn("(fnn-owner-complete-generation ledger rgen members)", pipeline)
        self.assertNotIn("fnn-owner-unreleased", owner)
        event = owner[owner.index("(defun fnn-owner-disk-event "):owner.index("(defun fnn-owner-journal-note")]
        self.assertIn("'fn-otm-disk-step", event)
        self.assertIn("(fnn-journal-line entry)", event)
        # the entry is offered under the mutex that numbered it (batch AY:
        # offered after the release, entries landed out of sequence)
        self.assertLess(event.index("(fnn-journal-line entry)"),
                        event.index("(when line (fnn-log-line line))"))
        # the reading is taken inside the gate mutex, never passed in
        self.assertLess(event.index("(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))"),
                        event.index("(setq reading (fnn-owner-monotonic-ms))"))
        chunk = owner[owner.index("(defun fnn-owner-handle-chunk-read "):owner.index("(defun fnn-owner-exposure-idle")]
        self.assertLess(chunk.index("(fnn-owner-advance-clock)"),
                        chunk.index("(setq sched (fnn-owner-gate-sched-value service)"))
        self.assertIn("admit (fnn-core 'fn-otm-admit-post sched))", chunk)
        # Lane log-leftovers: the read gets the gate's value (the disk's
        # reason lines are ACL2's over it); PKT-858: a peer read admitted as
        # :reader runs only while the disk sheds.
        # Row A4 (c) (books/owner-cold-line.lisp, PRF-933): the read goes
        # through fnn-owner-chunk-span-no-io, which runs ACL2's
        # fn-owner-chunk-span over the same scheduler value, first with a
        # cold payload thrown out of the mutex (the line is then read off
        # it), else the whole read as before when the cache is off.
        self.assertIn("(fnn-owner-chunk-span-no-io cid incoming sched)", chunk)
        no_io = owner[owner.index("(defun fnn-owner-chunk-span-no-io "):
                      owner.index("(defun fnn-owner-cold-line ")]
        self.assertIn("'fn-owner-chunk-span cid 0 (length incoming) sched)", no_io)
        self.assertIn("'fn-owner-chunk-span cid 0 end sched)", no_io)
        self.assertIn("(fnn-core 'fn-otm-peer-read-proceeds-p class sched)", chunk)
        mux = (ROOT / "host" / "native" / "mux.lisp").read_text()
        self.assertIn("(fnn-owner-peer-read-class service)", mux)
        peer_class = owner[owner.index("(defun fnn-owner-peer-read-class "):owner.index("(defun fnn-owner-disk-stalled-p")]
        self.assertIn("'fn-otm-peer-read-class", peer_class)
        admit = owner[owner.index("(defun fnn-owner-disk-admission "):owner.index("(defun fnn-owner-disk-stalled-p")]
        self.assertIn("'fn-otm-admit-post", admit)
        # The read's admission and ACL2's reply lines naming the disk's
        # reason are ACL2's over one scheduler value, read once under the
        # gate mutex (fnn-owner-gate-sched-value) and handed to the read.
        value = owner[owner.index("(defun fnn-owner-gate-sched-value "):owner.index("(defun fnn-owner-peer-read-class ")]
        self.assertEqual(value.count("(fnn-owner-gate-sched gate)"), 1, value)
        self.assertIn("(fnn-owner-gate-mutex gate)", value)
        clock = owner[owner.index("(defun fnn-owner-advance-clock "):owner.index("(defun fnn-owner-finish ")]
        self.assertIn(":served", clock)
        control = (ROOT / "host" / "native" / "control.lisp").read_text()
        self.assertIn("(eq (fnn-owner-disk-admit service) :shed))\n                    :busy)", control)
        shed = owner[owner.index("(defun fnn-owner-shed-queued-locked "):]
        self.assertIn("'fn-owner-shed-outcome", shed[:2000])
        wrapper = (ROOT / "host" / "owner-host.lisp").read_text()
        # The served read is the credit read over the slots' read over the
        # time model's (lanes zero-copy-commit, admission-gap, credits):
        # the disk's classification runs first, and a POST the slots refuse
        # while the disk sheds is told the disk's reason
        # (books/owner-article-slots.lisp fn-oas-refusal-line).
        self.assertIn("(fn-mca-read-span\n", wrapper)
        credits = (ROOT / "books" / "owner-credits.lisp").read_text()
        self.assertIn("(r0 (fn-oas-read-span oc views id i end ", credits)
        slots = (ROOT / "books" / "owner-article-slots.lisp").read_text()
        body = slots[slots.index("(defun fn-oas-read-span "):]
        self.assertIn("(let ((r (fn-otm-read-span oc views id i end ", body[:900])
        self.assertIn("(fn-otm-post-command-reply s)",
                      slots[slots.index("(defun fn-oas-refusal-line "):][:400])
        self.assertIn("(fn-otm-shed-reply s)", wrapper)
        self.assertIn("(fn-owner-outcome id :refused state)", wrapper)
        live = (ROOT / "host" / "native-live-status-host.lisp").read_text()
        self.assertIn("(fn-otm-health-lines sched)", live)
        self.assertIn("(fn-otm-disk-lines sched)", live)

    def test_a_graceful_stop_drains_before_its_fence(self):
        """PKT-875 (PRF-357): after a SIGTERM the drain (ACL2's
        fn-osd-drain-next) runs before the fence; the I/O loops end only at
        the fence; the committer releases at the drain's deadline as at a
        stall.  `once' reaches the drain at the SIGTERM too (lane
        sigterm-hang: its wait returned only when its client ended)."""
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text()
        run = owner[owner.index("(defun fnn-owner-run "):owner.index("(defun fnn-owner-run-normalized")]
        self.assertLess(run.index("(fnn-owner-drain-service service)"),
                        run.index("(fnn-owner-stop-service service +fnn-exit-ok+))\n                  (fnn-owner-service-exit-code"))
        drain = owner[owner.index("(defun fnn-owner-drain-service "):owner.index("(defun fnn-owner-run ")]
        self.assertIn("(fnn-call 'fn-osd-drain-next s0 s limits awaiting unsent released)", drain)
        self.assertIn("(fnn-owner-sched-snapshot service)", drain)
        pipeline = owner[owner.index("(defun fnn-owner-commit-pipeline "):
                         owner.index("(defun fnn-owner-loops-snapshot")]
        self.assertIn("(fnn-owner-service-drain-release service)", pipeline)
        mux = (ROOT / "host" / "native" / "mux.lisp").read_text()
        run_loop = mux[mux.index("(defun fnn-mux-run "):mux.index("(defun fnn-mux-start ")]
        self.assertNotIn("*fnn-sigterm-requested*", run_loop)
        work = mux[mux.index("(defun fnn-mux-work "):mux.index("(defun fnn-mux-readable ")]
        self.assertIn("*fnn-sigterm-requested*", work)
        once = mux[mux.index("(defun fnn-mux-serve-once "):mux.index(";;; The connection budget")]
        self.assertIn("*fnn-sigterm-requested*", once)


@requires(DEVELOPER)
class SlowDiskNativeTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, DEVELOPER)
        self.root, self.store, self.port = self.node.root, self.node.store_path, self.node.port
        self.stall = self.root / "stall"
        # A = 64 KiB: this class tests the disk, and its stop case holds 17
        # articles in flight at once (8 mid-article, 8 mid-commit, the warm
        # one).  An article credit is the article's worst case as octet
        # lists (books/heap-store-figure.lisp fn-heap-article-reserve-octets,
        # 32 x (512 + A + HDR)): at A = 64 KiB and HDR = 16 KiB, 2,637,824
        # octets, 25 in the 64 MiB pool; at A = 1 MiB, 34,095,104 octets,
        # ONE (planning/evidence/credits-stall-2026-09-28.md).
        init = self.operator("init", "--max-article-octets", "65536", "fn.test")
        self.assertEqual(init.returncode, 0, init.stderr.decode())
        # Registered after the node, so it runs before the node's stop: a
        # stalled barrier never holds the stop.
        self.addCleanup(lambda: self.stall.unlink() if self.stall.exists() else None)
        self.owner = self.start_owner({"FN_NATIVE_TEST_DISK_STALL_FILE": str(self.stall)})

    def operator(self, *words, timeout=60):
        return self.node.operator(*words, timeout=timeout)

    def start_owner(self, extra):
        return self.node.start(env=extra)

    def reap(self, process):
        if self.stall.exists():
            self.stall.unlink()
        self.node.stop(expect=None, process=process)

    def owner_log(self, settle=0.3, limit=10.0):
        """Every owner's stderr this test started, in order, once the drains
        have stopped growing (the owner wrote it before the test looked)."""
        deadline = time.monotonic() + limit
        end = None
        while time.monotonic() < deadline:
            now = sum(process.stderr.end for process in self.node.processes)
            if now == end:
                break
            end = now
            time.sleep(settle)
        return b"".join(process.stderr.since(0) for process in self.node.processes)

    def connect(self):
        conn = socket.create_connection(("127.0.0.1", self.port), timeout=120)
        stream = conn.makefile("rwb")
        self.assertTrue(stream.readline().startswith(b"200"))
        return conn, stream

    def send_article(self, stream, msgid, body):
        stream.write(b"POST\r\n")
        stream.flush()
        line = stream.readline()
        self.assertTrue(line.startswith(b"340"), line)
        self.send_body(stream, msgid, body)

    def send_body(self, stream, msgid, body):
        stream.write(b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                     b"Subject: slow disk\r\nMessage-ID: <" + msgid + b">\r\n\r\n"
                     + body + b"\r\n.\r\n")
        stream.flush()

    def policy(self, slot, value):
        result = self.operator("policy", "set", slot, str(value))
        self.assertEqual(result.returncode, 0, (slot, result.stdout, result.stderr))
        return result

    def multiline(self, stream):
        while True:
            line = stream.readline()
            self.assertTrue(line, "the reply ended before the terminator")
            if line == b".\r\n":
                return

    def timed_read(self, stream, command, expect, multiline=False):
        started = time.monotonic()
        stream.write(command)
        stream.flush()
        line = stream.readline()
        self.assertTrue(line.startswith(expect), (command, line))
        if multiline:
            self.multiline(stream)
        return time.monotonic() - started

    def timed_operator(self, word):
        started = time.monotonic()
        result = self.operator(word, timeout=60)
        return time.monotonic() - started, result

    def test_a_cold_read_on_a_stalled_disk_answers_403_while_cached_reads_stay_flat(self):
        """Row A4 (c) (lane composed-owner-3; books/owner-cold-line.lisp,
        PRF-933).  Two articles are stored and the owner restarted, so both
        payloads are cold extents.  B is read once (warm).  The read device
        then stalls (FN_NATIVE_TEST_READ_STALL_FILE: a pread does not return).
        On connection 1 three pipelined commands, DATE, ARTICLE <A>, DATE,
        are answered IN ORDER: 111, then 403 (temporarily unavailable, not
        430) after the 5,000 ms dependency deadline and within a bound of
        it, then 111 (the session unchanged).  Meanwhile connection 2's
        cached ARTICLE <B> reads stay flat (each well under the deadline:
        neither the owner mutex nor the realizer's lock is held by the
        stalled read).  When the device comes back, ARTICLE <A> answers 220."""
        with node_log_on_failure(self.owner):
            conn, stream = self.connect()
            self.addCleanup(conn.close)
            self.send_article(stream, b"cold-a@example.invalid", b"article A")
            self.assertTrue(stream.readline().startswith(b"240"))
            self.send_article(stream, b"warm-b@example.invalid", b"article B")
            self.assertTrue(stream.readline().startswith(b"240"))
            conn.close()
            self.reap(self.owner)
            readstall = self.root / "readstall"
            self.addCleanup(lambda: readstall.unlink() if readstall.exists() else None)
            self.owner = self.start_owner({"FN_NATIVE_TEST_READ_STALL_FILE": str(readstall)})
            c1, s1 = self.connect()
            self.addCleanup(c1.close)
            c2, s2 = self.connect()
            self.addCleanup(c2.close)
            self.timed_read(s2, b"ARTICLE <warm-b@example.invalid>\r\n", b"220", multiline=True)
            readstall.write_bytes(b"")
            warm = []
            stop = threading.Event()

            def cached_reads():
                while not stop.is_set():
                    warm.append(self.timed_read(s2, b"ARTICLE <warm-b@example.invalid>\r\n",
                                                b"220", multiline=True))
                    time.sleep(0.1)

            reader = threading.Thread(target=cached_reads)
            reader.start()
            try:
                started = time.monotonic()
                s1.write(b"DATE\r\nARTICLE <cold-a@example.invalid>\r\nDATE\r\n")
                s1.flush()
                self.assertTrue(s1.readline().startswith(b"111"))
                line = s1.readline()
                waited = time.monotonic() - started
                self.assertTrue(line.startswith(b"403 article temporarily unavailable"), line)
                self.assertGreaterEqual(waited, 4.5, waited)
                self.assertLess(waited, 15.0, waited)
                self.assertTrue(s1.readline().startswith(b"111"))
            finally:
                stop.set()
                reader.join(timeout=30)
            self.assertGreaterEqual(len(warm), 5, warm)
            self.assertLess(max(warm), 1.5, warm)
            readstall.unlink()
            deadline = time.monotonic() + 30
            while True:
                s1.write(b"ARTICLE <cold-a@example.invalid>\r\n")
                s1.flush()
                line = s1.readline()
                if line.startswith(b"220"):
                    self.multiline(s1)
                    break
                self.assertTrue(line.startswith(b"403"), line)
                self.assertLess(time.monotonic(), deadline, "the page never came back")
                time.sleep(0.5)

    def test_a_retry_storm_on_a_stalled_disk_keeps_threads_and_reads_bounded(self):
        """Lane cold-read-ownership (Codex r31 F2; books/page-read-direct.lisp).
        While the read device stalls, a client retries a cold ARTICLE over
        and over.  Each retry used to start one more thread with its own
        buffer and orphan it at the deadline.  Now a read occupies one of
        ACL2's fixed cold workers (fn-pio-direct-workers) until its pread
        actually returns: the first retries wait out the dependency deadline
        (403 temporarily unavailable), and once every worker holds a stalled
        read the next ones are refused AT ONCE by name (403 cold read
        resources unavailable) -- no new thread, no new buffer.  The node's
        thread count does not grow with the retries.  When the device
        comes back every stalled read settles (cancelled: nothing is
        published for a request that timed out) and the article reads."""
        workers = 4  # books/profile-limits.lisp :cold-workers
        retries = 3 * workers
        with node_log_on_failure(self.owner):
            conn, stream = self.connect()
            self.addCleanup(conn.close)
            self.send_article(stream, b"storm-a@example.invalid", b"article A")
            self.assertTrue(stream.readline().startswith(b"240"))
            conn.close()
            self.reap(self.owner)
            readstall = self.root / "readstall"
            self.addCleanup(lambda: readstall.unlink() if readstall.exists() else None)
            self.owner = self.start_owner({"FN_NATIVE_TEST_READ_STALL_FILE": str(readstall)})
            pid = self.owner.pid
            c1, s1 = self.connect()
            self.addCleanup(c1.close)
            before = thread_count(pid)
            readstall.write_bytes(b"")
            timed_out, refused, peak = 0, 0, before
            for _ in range(retries):
                started = time.monotonic()
                s1.write(b"ARTICLE <storm-a@example.invalid>\r\n")
                s1.flush()
                line = s1.readline()
                waited = time.monotonic() - started
                peak = max(peak, thread_count(pid))
                if line.startswith(b"403 article temporarily unavailable; cold read resources unavailable"):
                    refused += 1
                    self.assertLess(waited, 2.0, (line, waited))
                else:
                    self.assertTrue(line.startswith(b"403 article temporarily unavailable"), line)
                    self.assertGreaterEqual(waited, 4.5, waited)
                    timed_out += 1
            print("NATIVE-COLD-STORM retries=%d timed-out=%d refused=%d threads=%d->%d"
                  % (retries, timed_out, refused, before, peak))
            self.assertEqual(timed_out, workers, (timed_out, refused))
            self.assertEqual(refused, retries - workers, (timed_out, refused))
            # A thread per retry would be RETRIES more; allow the owner's own
            # lazily started threads (fewer than one retry's worth each).
            self.assertLess(peak - before, workers, (before, peak))
            readstall.unlink()
            deadline = time.monotonic() + 30
            while True:
                s1.write(b"ARTICLE <storm-a@example.invalid>\r\n")
                s1.flush()
                line = s1.readline()
                if line.startswith(b"220"):
                    self.assertIn(b"article A", b"".join(iter(lambda: s1.readline(), b".\r\n")))
                    break
                self.assertTrue(line.startswith(b"403"), line)
                self.assertLess(time.monotonic(), deadline, "the page never came back")
                time.sleep(0.5)
            self.assertLess(thread_count(pid) - before, workers)

    def test_reads_and_control_stay_flat_while_the_disk_stalls_and_posts_are_refused_try_later(self):
        # Slice 2: H far past this test's stall (the posters of a batch
        # stalled past H are told uncertain; that is the next test's).
        self.policy("barrier-stall-ms", 120000)
        reader_conn, reader = self.connect()
        a_conn, a = self.connect()
        b_conn, b = self.connect()
        c_conn, c = self.connect()
        d_conn, d = self.connect()
        with reader_conn, a_conn, b_conn, c_conn, d_conn:
            # A healthy barrier first: W is stored, `health' says ok.
            self.send_article(c, b"warm@example.invalid", b"a healthy barrier")
            line = c.readline()
            self.assertTrue(line.startswith(b"240"), line)
            _, health = self.timed_operator("health")
            self.assertIsNotNone(DISK_OK.search(health.stdout), health.stdout)
            baseline = [self.timed_read(reader, b"GROUP fn.test\r\n", b"211") for _ in range(5)]

            # B's POST command is answered 340 while the disk is healthy;
            # its article is sent while the disk is slow (441 below).
            b.write(b"POST\r\n")
            b.flush()
            line = b.readline()
            self.assertTrue(line.startswith(b"340"), line)
            # The device stalls.  A's batch goes in flight and stays there.
            self.stall.write_bytes(b"")
            self.send_article(a, b"held@example.invalid", b"its barrier stalls")
            t0 = time.monotonic()
            reads, controls, healths = [], [], []
            slow_line = None
            refused = None
            refused_command, refused_command_at = None, None
            refused_at = None
            while time.monotonic() - t0 < STALL_SECONDS:
                reads.append(self.timed_read(reader, b"GROUP fn.test\r\n", b"211"))
                reads.append(self.timed_read(reader, b"ARTICLE <warm@example.invalid>\r\n",
                                             b"220", multiline=True))
                elapsed, status = self.timed_operator("status")
                self.assertEqual(status.returncode, 0, status.stderr.decode())
                controls.append((time.monotonic() - t0, elapsed))
                if time.monotonic() - t0 > 7.0 and refused is None:
                    elapsed, health = self.timed_operator("health")
                    healths.append(elapsed)
                    slow_line = DISK_SLOW.search(health.stdout)
                    self.assertIsNotNone(slow_line, health.stdout)
                    self.assertIsNotNone(DISK_SLOW.search(status.stdout), status.stdout)
                    # An article whose POST was answered 340 before the
                    # disk went slow: refused at once, with the reason;
                    # nothing stored (slice 1's 441).
                    sent = time.monotonic()
                    self.send_body(b, b"shed@example.invalid", b"refused try-later")
                    refused = b.readline()
                    refused_at = time.monotonic() - sent
                    # A POST command while the disk is slow: 440 with the
                    # reason, before any article is sent (slice 2).
                    sent = time.monotonic()
                    d.write(b"POST\r\n")
                    d.flush()
                    refused_command = d.readline()
                    refused_command_at = time.monotonic() - sent
                # A has no answer while the device is stalled.
                self.assertEqual(select.select([a_conn], [], [], 0)[0], [],
                                 "the held POST was answered while its barrier stalled")
                time.sleep(0.5)
            self.assertIsNotNone(refused, "no POST was sent during the slow window")
            # STAT during the stall: the held article is not visible (reader view).
            stat_held = self.timed_read(reader, b"STAT <held@example.invalid>\r\n", b"430")

            # The device comes back: A's 240, `health' ok with the latency.
            self.stall.unlink()
            back = time.monotonic()
            a_conn.settimeout(60)
            accepted = a.readline()
            accepted_after = time.monotonic() - back
            self.assertTrue(accepted.startswith(b"240"), accepted)
            _, health = self.timed_operator("health")
            ok = DISK_OK.search(health.stdout)
            self.assertIsNotNone(ok, health.stdout)
            last_barrier_ms, episodes = int(ok.group(2)), int(ok.group(6))
            # The next POST is accepted.
            self.send_article(c, b"after@example.invalid", b"after the stall")
            after = c.readline()
            # The reader's pin moves at its next GROUP (a reader keeps the
            # version it opened on until then).
            self.timed_read(reader, b"GROUP fn.test\r\n", b"211")
            stat_shed = self.timed_read(reader, b"STAT <shed@example.invalid>\r\n", b"430")
            stat_after = self.timed_read(reader, b"STAT <after@example.invalid>\r\n", b"223")
            stat_a = self.timed_read(reader, b"STAT <held@example.invalid>\r\n", b"223")
            for s in (reader, a, b, c, d):
                s.write(b"QUIT\r\n")
                s.flush()

        control_max = max(e for _, e in controls)
        early = [e for t, e in controls if t < STALL_SECONDS / 3]
        late = [e for t, e in controls if t > 2 * STALL_SECONDS / 3]
        print("disk stalled %.0fs: reads n=%d max=%.3fs (baseline max %.3fs); status n=%d max=%.3fs "
              "(first third max %.3fs, last third max %.3fs); health max %.3fs; %s; "
              "shed POST answered in %.3fs: %r; held POST 240 %.3fs after the device came back; "
              "health after: last-barrier-ms=%d slow-episodes=%d; next POST %r"
              % (STALL_SECONDS, len(reads), max(reads), max(baseline), len(controls), control_max,
                 max(early), max(late), max(healths or [0]),
                 slow_line.group(0).decode() if slow_line else None,
                 refused_at, refused, accepted_after, last_barrier_ms, episodes, after))
        # Flat: every read and control answer well inside a second-scale
        # bound while the barrier was pending 30 s, and no growth with it.
        self.assertLess(max(reads), 2.0, reads)
        self.assertLess(control_max, 5.0, controls)
        self.assertLess(max(late), max(early) + 2.0, (early, late))
        # The shed POST: ACL2's try-later 441 with the reason, promptly.
        # The article whose POST got 340 before the disk went slow: 441,
        # nothing stored (STAT 430 below).  Slice 2 runs the read with the
        # connection's posting bit off; the served machine's 441 and 440
        # carry the disk's reason (books/owner-time-admission.lisp
        # fn-otm-disk-effects puts ACL2's lines in place of the generic ones).
        self.assertTrue(refused.startswith(b"441 posting failed; the disk is slow (a write has waited "),
                        refused)
        self.assertTrue(refused.endswith(b": nothing was stored, try again later\r\n"), refused)
        self.assertLess(refused_at, 2.0, refused_at)
        self.assertTrue(refused_command.startswith(
            b"440 posting not permitted now; the disk is slow (a write has waited "), refused_command)
        self.assertTrue(refused_command.endswith(b", try again later\r\n"), refused_command)
        self.assertLess(refused_command_at, 2.0, refused_command_at)
        print("POST command during slow answered in %.3fs: %r" % (refused_command_at, refused_command))
        self.assertGreaterEqual(int(slow_line.group(1)), int(slow_line.group(2)))
        # The held POST: accepted once the device came back; the barrier's
        # latency recorded as at least the stall; one slow episode.
        self.assertLess(accepted_after, 10.0, accepted_after)
        self.assertGreaterEqual(last_barrier_ms, int(STALL_SECONDS * 1000) - 500, last_barrier_ms)
        self.assertEqual(episodes, 1)
        self.assertTrue(after.startswith(b"240"), after)
        self.assertLess(stat_held, 2.0)
        del stat_shed, stat_after, stat_a
        # The service log names the episode, entered and left, with figures.
        log = self.owner_log()
        self.assertIn(b"disk slow: a barrier has waited ", log)
        self.assertIn(b"disk recovered: the barrier completed after ", log)

    def test_a_stall_past_h_tells_the_posters_uncertain_and_the_articles_land(self):
        """Slice 2 (lane time-model-2; PRF-311, PRF-322, PRF-323): the three
        profile fields set by `policy set' (D 2 s, H 6 s, cadence 250 ms);
        a barrier stalled past H: its posters -- the batch in flight and the
        one prepared behind it -- are told the outcome is uncertain, never
        accepted or refused, within H plus a second; the POST queued behind
        them is refused try-later; a POST command is answered 440; a
        mutating control request is answered BUSY; reads stay flat.  When
        the device comes back the told articles are STORED (the documented
        ambiguity: RFC 3977 section 6.3.1, the client checks before it
        reposts), the refused one is not, health says ok with one stall,
        and the decision journal holds the run's events in sequence."""
        self.policy("barrier-deadline-ms", 2000)
        self.policy("barrier-stall-ms", 6000)
        self.policy("clock-event-ms", 250)
        reader_conn, reader = self.connect()
        conns = [self.connect() for _ in range(5)]
        (a_conn, a), (e_conn, e), (f_conn, f), (g_conn, g), (w_conn, w) = conns
        with reader_conn, a_conn, e_conn, f_conn, g_conn, w_conn:
            self.send_article(w, b"warm2@example.invalid", b"a healthy barrier")
            self.assertTrue(w.readline().startswith(b"240"))
            self.stall.write_bytes(b"")
            t0 = time.monotonic()
            self.send_article(a, b"stalled-a@example.invalid", b"in flight")
            time.sleep(0.3)
            self.send_article(e, b"stalled-e@example.invalid", b"prepared behind it")
            time.sleep(0.3)
            self.send_article(f, b"queued-f@example.invalid", b"queued behind both")
            # D passes: slow.  A mutating control request is BUSY at once.
            time.sleep(max(0.0, t0 + 3.0 - time.monotonic()))
            elapsed, health = self.timed_operator("health")
            self.assertIsNotNone(DISK_SLOW.search(health.stdout), health.stdout)
            # PRF-358 (provisional, PKT-853 (b)): slow is the line only.
            slow_health = health
            started = time.monotonic()
            busy = self.operator("policy", "set", "clock-event-ms", "500")
            busy_at = time.monotonic() - started
            reads = []
            answers = {}
            for name, conn, stream in (("a", a_conn, a), ("e", e_conn, e), ("f", f_conn, f)):
                conn.settimeout(30)
            # H passes: A and E are told uncertain, F refused try-later.
            deadline = t0 + 20
            pending = {"a": (a_conn, a), "e": (e_conn, e), "f": (f_conn, f)}
            while pending and time.monotonic() < deadline:
                reads.append(self.timed_read(reader, b"GROUP fn.test\r\n", b"211"))
                ready, _, _ = select.select([c for c, _ in pending.values()], [], [], 0.25)
                for name in list(pending):
                    conn, stream = pending[name]
                    if conn in ready:
                        at, line = time.monotonic() - t0, stream.readline()
                        # A and E are closed after their uncertain reply;
                        # F's connection stays open after its try-later.
                        rest = stream.readline() if name != "f" else None
                        answers[name] = (at, line, rest)
                        del pending[name]
            self.assertEqual(pending, {}, "not every poster was answered within 20 s")
            _, health = self.timed_operator("health")
            stalled = DISK_STALLED.search(health.stdout)
            self.assertIsNotNone(stalled, health.stdout)
            stalled_health = health
            g.write(b"POST\r\n")
            g.flush()
            refused_command = g.readline()
            # The device comes back.
            self.stall.unlink()
            time.sleep(1.0)
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline:
                _, health = self.timed_operator("health")
                ok = DISK_OK.search(health.stdout)
                if ok:
                    break
                time.sleep(0.5)
            self.assertIsNotNone(ok, health.stdout)
            self.send_article(w, b"after2@example.invalid", b"after the stall")
            after = w.readline()
            time.sleep(0.5)
            self.timed_read(reader, b"GROUP fn.test\r\n", b"211")
            stat = {}
            for msgid in (b"stalled-a", b"stalled-e", b"queued-f", b"after2"):
                reader.write(b"STAT <" + msgid + b"@example.invalid>\r\n")
                reader.flush()
                stat[msgid] = reader.readline()[:3]
            for stream in (reader, g, w):
                stream.write(b"QUIT\r\n")
                stream.flush()
        print("stall past H (D=2000 H=6000 cadence=250): answers %r; busy control %.3fs rc=%d %r; "
              "reads n=%d max=%.3fs; health %s; POST command %r; after recovery %s; STAT %r; next POST %r"
              % ({k: (round(v[0], 3), v[1], v[2]) for k, v in answers.items()}, busy_at,
                 busy.returncode, (busy.stdout + busy.stderr)[-200:], len(reads), max(reads),
                 stalled.group(0).decode(), refused_command, ok.group(0).decode(), stat, after))
        # BUSY: refused (try later), at once, nothing staged.
        self.assertNotEqual(busy.returncode, 0)
        self.assertIn(b"busy", (busy.stdout + busy.stderr).lower())
        self.assertLess(busy_at, 5.0)
        # The posters: A and E uncertain (ACL2's uncertain reply, then the
        # close) within H + 1.5 s of the stall's start; F refused try-later.
        for name in ("a", "e"):
            at, line, rest = answers[name]
            self.assertTrue(line.startswith(b"441"), (name, line))
            self.assertNotIn(b"try again later", line, (name, line))
            self.assertEqual(rest, b"", (name, rest))
            self.assertLess(at, 6.0 + 1.5, (name, at))
            self.assertGreater(at, 6.0 - 0.5, (name, at))
        at, line, _ = answers["f"]
        self.assertTrue(line.startswith(b"441 posting failed; the disk is stalled"), line)
        self.assertLess(at, 6.0 + 1.5, at)
        self.assertLess(max(reads), 2.0, reads)
        self.assertEqual(int(stalled.group(5)), 1)
        self.assertTrue(refused_command.startswith(
            b"440 posting not permitted now; the disk is stalled (a write has waited "), refused_command)
        self.assertTrue(refused_command.endswith(b", deadline 2000 ms), try again later\r\n"),
                        refused_command)
        # Recovery: the told articles are stored, the refused one is not.
        self.assertEqual(stat[b"stalled-a"], b"223", stat)
        self.assertEqual(stat[b"stalled-e"], b"223", stat)
        self.assertEqual(stat[b"queued-f"], b"430", stat)
        self.assertEqual(stat[b"after2"], b"223", stat)
        self.assertEqual(int(ok.group(7)), 1)
        self.assertTrue(after.startswith(b"240"), after)
        # PRF-358 (PKT-879): health's ninth state.  Slow: clear, exit 0.
        # Stalled: held with the stall's duration, exit 28.  Recovered: 0.
        print("health while slow: rc=%d %r; while stalled: rc=%d %r; after: rc=%d"
              % (slow_health.returncode, slow_health.stdout.split(b"\n")[0],
                 stalled_health.returncode, stalled_health.stdout.split(b"\n")[0],
                 health.returncode))
        self.assertEqual(slow_health.returncode, 0, slow_health.stdout)
        self.assertIn(b"\ndisk clear\n", slow_health.stdout)
        self.assertEqual(stalled_health.returncode, 28, stalled_health.stdout)
        self.assertTrue(stalled_health.stdout.startswith(b"health exit=28 state=disk\n"),
                        stalled_health.stdout)
        held = re.search(rb"^disk held mode=stalled pending-ms=(\d+) stall-ms=(\d+) "
                         rb"members=uncertain posts=try-later$", stalled_health.stdout, re.M)
        self.assertIsNotNone(held, stalled_health.stdout)
        self.assertGreaterEqual(int(held.group(1)), int(held.group(2)))
        self.assertEqual(health.returncode, 0, health.stdout)
        log = self.owner_log()
        self.assertIn(b"disk stalled: a barrier has waited ", log)
        self.assertIn(b"disk recovered after a stall: the barrier completed after ", log)
        # The decision journal: this run's segment, entries in sequence
        # (books/owner-time-journal.lisp: (SEQ OP READING A B C WORD)), its
        # codes looked up by name in the registry its defevent forms generate
        # (planning/events.json), never copied here.
        families = json.loads((ROOT / "planning" / "events.json").read_text())["families"]
        op = dict(families["fn-otm-op"]["codes"],
                  **{r["name"]: int(c) for c, r in families["fn-otm-op"]["reserved"].items()})
        word = families["fn-otm-word"]["codes"]
        journal = (self.store / "decisions" / "decisions.fnj").read_bytes()
        entries = [[int(x) for x in line.split(b" ")] for line in journal.split(b"\n") if line]
        start = max(i for i, entry in enumerate(entries) if entry[1] == op["start"])
        segment = entries[start + 1:]
        self.assertTrue(all(len(entry) == 7 for entry in entries))
        self.assertEqual([entry[0] for entry in segment], list(range(1, len(segment) + 1)))
        readings = [entry[2] for entry in segment
                    if entry[1] in (op["clock"], op["served"], op["issue"], op["return"])]
        self.assertEqual(readings, sorted(readings), "the recorded time went backwards")
        self.assertIn([op["issue"], 2000, 6000, 250], [[e[1], e[3], e[4], e[5]] for e in segment])
        self.assertTrue(any(e[1] in (op["clock"], op["served"]) and e[6] == word["became-stalled"]
                            for e in segment), "no :became-stalled")
        self.assertIn([op["note"], 2, 1], [[e[1], e[3], e[4]] for e in segment])
        self.assertTrue(any(e[1] == op["return"] and e[6] == word["recovered-from-stall"]
                            for e in segment), "no :recovered-from-stall")
        print("journal: %d entries in this run's segment, %d bytes in the file" % (len(segment), len(journal)))
        # The operator's replay (`store ROOT journal', ACL2's fn-otm-replay).
        replay = self.node.store("journal", timeout=120)
        print("store journal: rc=%d %r" % (replay.returncode, replay.stdout))
        self.assertEqual(replay.returncode, 0, (replay.stdout, replay.stderr))
        self.assertIn(b" replay=agrees", replay.stdout)

    def test_the_adopted_default_bars_classify_an_unresolved_write(self):
        """Lane time-bars (PRF-384, HST-031; planning/design-time-model-2026-09-27.md
        section 4b): the adopted DEFAULT bars, no policy row set -- D 5,000 ms,
        H 30,000 ms, the clock cadence 1,000 ms.  One POST's barrier stalls.
        Each answer's CLASSIFICATION is asserted here (the timings are printed
        and measured once, at the prerelease convergence checklist):
          * under D: health says disk ok, exit 0;
          * past D: health says disk slow (deadline-ms=5000 stall-ms=30000),
            exit 0; a new POST command is 440 try-later; the SAME article
            re-submitted on another connection is 440 too -- never an absence,
            never stored twice; reads are answered;
          * at H: the held poster is told uncertain (ACL2's 441, not a
            try-later), then closed -- at H, not at D; health is exit 28,
            disk stalled;
          * the device returns: the late completion is consumed once -- the
            told poster gets no second reply -- and the SAME article
            re-submitted is answered `this article is already stored here':
            explicit acceptance evidence, not a STAT;
          * a restart is a new clock domain: the journal's start entries carry
            the wall observation and no monotonic reading, and the replay of
            both runs' segments agrees."""
        reader_conn, reader = self.connect()
        conns = [self.connect() for _ in range(4)]
        (a_conn, a), (b_conn, b), (c_conn, c), (w_conn, w) = conns
        with reader_conn, a_conn, b_conn, c_conn, w_conn:
            self.send_article(w, b"warm-bars@example.invalid", b"a healthy barrier")
            self.assertTrue(w.readline().startswith(b"240"))
            self.stall.write_bytes(b"")
            t0 = time.monotonic()
            self.send_article(a, b"held-bars@example.invalid", b"its barrier stalls")
            time.sleep(max(0.0, t0 + 2.0 - time.monotonic()))
            under_d_at, under_d = self.timed_operator("health")
            time.sleep(max(0.0, t0 + 7.0 - time.monotonic()))
            slow_at, slow = self.timed_operator("health")
            b.write(b"POST\r\n")
            b.flush()
            new_command = b.readline()
            c.write(b"POST\r\n")
            c.flush()
            retry_during = c.readline()
            read_at = self.timed_read(reader, b"GROUP fn.test\r\n", b"211")
            self.assertEqual(select.select([a_conn], [], [], 0)[0], [],
                             "the held POST was answered before H")
            a_conn.settimeout(60)
            ready, _, _ = select.select([a_conn], [], [], max(0.0, t0 + 45.0 - time.monotonic()))
            told_at = time.monotonic() - t0
            told = a.readline() if ready else None
            closed = a.readline() if ready else None
            stalled_at, stalled = self.timed_operator("health")
            read_stalled_at = self.timed_read(reader, b"GROUP fn.test\r\n", b"211")
            self.stall.unlink()
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline:
                _, health = self.timed_operator("health")
                ok = DISK_OK.search(health.stdout)
                if ok:
                    break
                time.sleep(0.5)
            self.assertIsNotNone(ok, health.stdout)
            c.write(b"POST\r\n")
            c.flush()
            again = c.readline()
            self.assertTrue(again.startswith(b"340"), again)
            self.send_body(c, b"held-bars@example.invalid", b"its barrier stalls")
            retry_after = c.readline()
            for stream in (reader, b, c, w):
                stream.write(b"QUIT\r\n")
                stream.flush()
        print("default bars: health under D %.3fs rc=%d; slow %.3fs rc=%d; POST command %r; same-article "
              "retry during %r; read %.3fs; told %r at %.3fs then %r; stalled health %.3fs rc=%d; read "
              "while stalled %.3fs; recovered %s; same-article retry after %r"
              % (under_d_at, under_d.returncode, slow_at, slow.returncode, new_command, retry_during,
                 read_at, told, told_at, closed, stalled_at, stalled.returncode, read_stalled_at,
                 ok.group(0).decode(), retry_after))
        # Under D: ok, exit 0.  Past D: slow with the adopted defaults, exit 0.
        self.assertIsNotNone(DISK_OK.search(under_d.stdout), under_d.stdout)
        self.assertEqual(under_d.returncode, 0, under_d.stdout)
        slow_line = DISK_SLOW.search(slow.stdout)
        self.assertIsNotNone(slow_line, slow.stdout)
        self.assertEqual((int(slow_line.group(2)), int(slow_line.group(3))), (5000, 30000))
        self.assertEqual(slow.returncode, 0, slow.stdout)
        # Try-later, never absence: the POST command and the same article.
        for line in (new_command, retry_during):
            self.assertTrue(line.startswith(b"440 posting not permitted now; the disk is slow"), line)
        # At H (not at D): uncertain, then the close; one reply only.
        self.assertIsNotNone(told, "the held poster was not told within 45 s")
        self.assertTrue(told.startswith(b"441"), told)
        self.assertNotIn(b"try again later", told)
        self.assertEqual(closed, b"", closed)
        self.assertGreater(told_at, 30.0 - 0.5, told_at)
        self.assertEqual(stalled.returncode, 28, stalled.stdout)
        stalled_line = DISK_STALLED.search(stalled.stdout)
        self.assertIsNotNone(stalled_line, stalled.stdout)
        self.assertEqual(int(stalled_line.group(3)), 30000)
        # The late completion landed the article; the same article is
        # answered with the acceptance evidence.
        self.assertEqual(retry_after, b"441 posting failed; this article is already stored here\r\n")
        # A restart is a new clock domain.
        self.node.stop(process=self.owner)
        self.owner = self.start_owner({"FN_NATIVE_TEST_DISK_STALL_FILE": str(self.stall)})
        replay = self.node.store("journal", timeout=120)
        journal = (self.store / "decisions" / "decisions.fnj").read_bytes()
        entries = [[int(x) for x in line.split(b" ")] for line in journal.split(b"\n") if line]
        starts = [entry for entry in entries if entry[1] == 0 and entry[0] == 0]
        print("restart: %d start entries %r; store journal rc=%d %r"
              % (len(starts), starts[-2:], replay.returncode, replay.stdout))
        self.assertGreaterEqual(len(starts), 2, starts)
        for entry in starts:
            self.assertEqual(entry[2], 0, entry)
            self.assertEqual(entry[4], 1, entry)
        self.assertEqual(replay.returncode, 0, (replay.stdout, replay.stderr))
        self.assertIn(b" replay=agrees", replay.stdout)

    def test_a_full_disk_refuses_posts_before_the_write_and_recovers(self):
        """PRF-359 (PKT-872) and PRF-358 (lane health-truth): the store's
        filesystem observed below the need (FN_NATIVE_DISK_FREE=@FILE caps
        the statvfs observation at the number in FILE, read at every
        observation, on the developer image): a POST command is answered 440
        with the reason before its article, an article whose POST got 340
        before is answered 441, nothing stored, and `health' holds `disk'
        (exit 28, mode=full with the figures).  Room again: the next
        observation recovers, POSTs are accepted, health exit 0.  The owner
        never stops and nothing is uncertain."""
        self.reap(self.owner)
        cap = self.root / "disk-free"
        cap.write_text("1000000000000\n")
        self.owner = self.start_owner({"FN_NATIVE_TEST_DISK_STALL_FILE": str(self.stall),
                                       "FN_NATIVE_DISK_FREE": "@" + str(cap)})
        w_conn, w = self.connect()
        b_conn, b = self.connect()
        with w_conn, b_conn:
            self.send_article(w, b"room@example.invalid", b"room on the disk")
            self.assertTrue(w.readline().startswith(b"240"))
            before = self.operator("health")
            b.write(b"POST\r\n")
            b.flush()
            self.assertTrue(b.readline().startswith(b"340"))
            # The disk fills.  The next observation (health's, or a served
            # read's a cadence after the last) finds it full.
            cap.write_text("1000\n")
            full_health = self.operator("health")
            full_status = self.operator("status")
            time.sleep(1.2)
            started = time.monotonic()
            w.write(b"POST\r\n")
            w.flush()
            refused_command = w.readline()
            refused_command_at = time.monotonic() - started
            self.send_body(b, b"full@example.invalid", b"sent while the disk is full")
            refused = b.readline()
            # Room again.
            cap.write_text("1000000000000\n")
            time.sleep(1.2)
            self.send_article(w, b"after-full@example.invalid", b"room again")
            after = w.readline()
            after_health = self.operator("health")
            w.write(b"STAT <full@example.invalid>\r\n")
            w.flush()
            stat_full = w.readline()[:3]
            w.write(b"GROUP fn.test\r\nSTAT <after-full@example.invalid>\r\n")
            w.flush()
            w.readline()
            stat_after = w.readline()[:3]
            for stream in (w, b):
                stream.write(b"QUIT\r\n")
                stream.flush()
        print("full disk: health before rc=%d; full rc=%d %r; status rc=%d %r; POST command %.3fs %r; "
              "article %r; after %r; health after rc=%d; STAT full=%r after=%r"
              % (before.returncode, full_health.returncode, full_health.stdout.split(b"\n")[0],
                 full_status.returncode,
                 [l for l in full_status.stdout.split(b"\n") if l.startswith(b"disk ")],
                 refused_command_at, refused_command, refused, after, after_health.returncode,
                 stat_full, stat_after))
        self.assertEqual(before.returncode, 0, before.stdout)
        self.assertRegex(before.stdout, rb"(?m)^disk space: free-octets=\d+ need-octets=\d+$")
        self.assertEqual(full_health.returncode, 28, full_health.stdout)
        self.assertTrue(full_health.stdout.startswith(b"health exit=28 state=disk\n"), full_health.stdout)
        self.assertRegex(full_health.stdout,
                         rb"(?m)^disk held mode=full free-octets=1000 need-octets=\d+ posts=try-later$")
        self.assertRegex(full_health.stdout,
                         rb"(?m)^disk full: free-octets=1000 need-octets=\d+ posts=try-later$")
        self.assertEqual(full_status.returncode, 0, full_status.stdout)
        self.assertRegex(full_status.stdout, rb"(?m)^disk full: free-octets=1000 ")
        self.assertRegex(refused_command,
                         rb"^440 posting not permitted now; the disk is full \(1000 octets free, \d+ needed\), "
                         rb"try again later\r\n$")
        self.assertLess(refused_command_at, 2.0)
        self.assertRegex(refused,
                         rb"^441 posting failed; the disk is full \(1000 octets free, \d+ needed\): "
                         rb"nothing was stored, try again later\r\n$")
        self.assertTrue(after.startswith(b"240"), after)
        self.assertEqual(after_health.returncode, 0, after_health.stdout)
        self.assertEqual(stat_full, b"430")
        self.assertEqual(stat_after, b"223")
        self.assertIsNone(self.owner.poll(), "the owner stopped")
        log = self.owner_log()
        self.assertIn(b"disk full: 1000 octets free, ", log)
        self.assertIn(b"disk space recovered: ", log)
        self.assertNotIn(b"needs recovery", log)

    FULL_REFUSAL = (b"441 posting failed; the store is full: no capacity for this article "
                    b"(unaffordable); the node's operator can raise it\r\n")

    def test_a_full_store_refusal_is_told_while_another_barrier_stalls(self):
        """PRF-354 (lane full-vs-uncertain; books/owner-commit-steps.lisp
        fn-ocs-unstaged-start-tells-its-refusals): a POST the full store
        refuses wrote nothing, so its refusal is known before any barrier.
        It arrives behind a batch whose barrier is stalled (drained by the
        START-NEXT behind it, before the deadline D) and is answered the
        named refusal at once -- not held to the stall deadline H and then
        told uncertain, as it was when it waited in the next batch.  The
        stalled POST is untouched: no answer while its device is stalled,
        its 240 when it comes back; the refused article is not stored."""
        # A store of 8 MiB of history (a record of at most 2 MiB, an article
        # of at most 256 KiB; the transaction bound keeps the reservation
        # small), filled with 199,800-octet articles until the store refuses
        # one by name.
        self.reap(self.owner)
        shutil.rmtree(self.store)
        init = self.operator("init", "--profile", "default", "--max-article-octets", "262144",
                             "--max-record-octets", "2097152", "--max-history-octets", "8388608",
                             "--max-transactions", "10000", "fn.test")
        self.assertEqual(init.returncode, 0, (init.stdout, init.stderr))
        self.owner = self.start_owner({"FN_NATIVE_TEST_DISK_STALL_FILE": str(self.stall)})
        self.policy("barrier-deadline-ms", 2000)
        self.policy("barrier-stall-ms", 6000)
        big = (b"z" * 72 + b"\r\n") * 2700
        fill_conn, fill = self.connect()
        a_conn, a = self.connect()
        f_conn, f = self.connect()
        with fill_conn, a_conn, f_conn:
            stored = 0
            for n in range(100):
                self.send_article(fill, b"fill-%d@example.invalid" % n, big)
                line = fill.readline()
                if not line.startswith(b"240"):
                    break
                stored += 1
            with node_log_on_failure(self.owner):
                self.assertEqual(line, self.FULL_REFUSAL, (stored, line))
                self.assertGreater(stored, 0)
            # The device stalls; a small article still fits and goes in flight.
            self.stall.write_bytes(b"")
            t0 = time.monotonic()
            self.send_article(a, b"held-small@example.invalid", b"a small article that fits")
            time.sleep(0.3)
            # A large one does not fit: refused by name while A's barrier stalls.
            sent = time.monotonic()
            self.send_article(f, b"full-f@example.invalid", big)
            f_conn.settimeout(30)
            refused = f.readline()
            refused_at, refused_since_stall = time.monotonic() - sent, time.monotonic() - t0
            held_unanswered = select.select([a_conn], [], [], 0)[0] == []
            # F's connection stays open after its refusal.
            f.write(b"DATE\r\n")
            f.flush()
            date = f.readline()
            self.stall.unlink()
            a_conn.settimeout(60)
            accepted = a.readline()
            fill.write(b"STAT <full-f@example.invalid>\r\n")
            fill.flush()
            stat_f = fill.readline()
            fill.write(b"GROUP fn.test\r\n")
            fill.flush()
            fill.readline()
            fill.write(b"STAT <held-small@example.invalid>\r\n")
            fill.flush()
            stat_a = fill.readline()
            for stream in (fill, a, f):
                stream.write(b"QUIT\r\n")
                stream.flush()
        print("full store (%d articles of %d octets): refused %r in %.3fs (%.3fs into the stall); "
              "held POST unanswered then: %s; after the stall %r; STAT F %r, A %r"
              % (stored, len(big), refused, refused_at, refused_since_stall, held_unanswered,
                 accepted, stat_f, stat_a))
        with node_log_on_failure(self.owner):
            self.assertEqual(refused, self.FULL_REFUSAL)
            self.assertLess(refused_since_stall, 2.0, refused_since_stall)
            self.assertTrue(held_unanswered,
                            "the stalled POST was answered before its device came back")
            self.assertTrue(date.startswith(b"111"), date)
            self.assertTrue(accepted.startswith(b"240"), accepted)
            self.assertTrue(stat_f.startswith(b"430"), stat_f)
            self.assertTrue(stat_a.startswith(b"223"), stat_a)

    def sigterm(self):
        self.owner.signal(signal.SIGTERM)
        return time.monotonic()

    def stop_answers(self, streams, seconds):
        """Each stream's first line and whether the connection then closed
        (b"" after it), within SECONDS."""
        answers = {}
        deadline = time.monotonic() + seconds
        pending = dict(streams)
        while pending and time.monotonic() < deadline:
            ready, _, _ = select.select([c for c, _ in pending.values()], [], [], 0.25)
            for name in list(pending):
                conn, stream = pending[name]
                if conn in ready:
                    try:
                        line = stream.readline()
                    except OSError as error:
                        line = ("error %s" % error).encode()
                    answers[name] = (time.monotonic(), line)
                    del pending[name]
        return answers, pending

    def restart_and_stat(self, msgids):
        self.owner = self.start_owner({"FN_NATIVE_TEST_DISK_STALL_FILE": str(self.stall)})
        conn, stream = self.connect()
        with conn:
            stat = {}
            for msgid in msgids:
                stream.write(b"STAT <" + msgid + b">\r\n")
                stream.flush()
                stat[msgid] = stream.readline()[:3]
            stream.write(b"QUIT\r\n")
            stream.flush()
        return stat

    def test_a_graceful_stop_answers_the_posts_in_flight(self):
        """PKT-875 (lane health-truth-stop; PRF-357, books/owner-stop-drain.lisp):
        two POSTs in flight on a stalled barrier (the batch in flight and the
        one prepared behind it) when SIGTERM arrives.  The stop drains: the
        device comes back 1.5 s later and each poster is told 240, never a
        bare close; only then the owner exits 0.  Both articles are stored."""
        self.policy("barrier-deadline-ms", 2000)
        self.policy("barrier-stall-ms", 6000)
        (a_conn, a), (e_conn, e), (w_conn, w) = [self.connect() for _ in range(3)]
        with a_conn, e_conn, w_conn:
            self.send_article(w, b"warm-stop@example.invalid", b"a healthy barrier")
            self.assertTrue(w.readline().startswith(b"240"))
            self.stall.write_bytes(b"")
            self.send_article(a, b"stop-a@example.invalid", b"in flight at the stop")
            time.sleep(0.3)
            self.send_article(e, b"stop-e@example.invalid", b"prepared behind it")
            time.sleep(0.3)
            t0 = self.sigterm()
            time.sleep(1.5)
            still_running = self.owner.poll() is None
            self.stall.unlink()
            answers, pending = self.stop_answers({"a": (a_conn, a), "e": (e_conn, e)}, 20)
            code = self.owner.wait(timeout=30)
            exited = time.monotonic() - t0
        stopped = self.owner
        stat = self.restart_and_stat([b"stop-a@example.invalid", b"stop-e@example.invalid"])
        print("graceful stop (device back 1.5 s after SIGTERM): answers %r; exit %d after %.3fs; STAT %r"
              % ({k: (round(v[0] - t0, 3), v[1]) for k, v in answers.items()}, code, exited, stat))
        with node_log_on_failure(stopped):
            self.assertTrue(still_running, "the owner stopped before its posts in flight were answered")
            self.assertEqual(pending, {}, "a poster was not answered")
            for name in ("a", "e"):
                self.assertTrue(answers[name][1].startswith(b"240"), (name, answers[name]))
            self.assertEqual(code, 0)
            self.assertEqual(set(stat.values()), {b"223"}, stat)
            log = self.owner_log()
            self.assertIn(b"stopping: answering the posts in flight first", log)
            self.assertIn(b"stopping: drained after ", log)

    def test_a_graceful_stop_past_the_deadline_answers_uncertain(self):
        """PKT-875: SIGTERM with two POSTs on a barrier that does not return.
        No poster is told a bare close: each is told the uncertain 441
        (ACL2's `the outcome is uncertain', never `try again later') by H
        after the barrier's issue plus a second, the drain ends, and the fence
        waits for the device (the owner exits 0 once it returns)."""
        self.policy("barrier-deadline-ms", 2000)
        self.policy("barrier-stall-ms", 6000)
        (a_conn, a), (e_conn, e), (w_conn, w) = [self.connect() for _ in range(3)]
        with a_conn, e_conn, w_conn:
            self.send_article(w, b"warm-stop2@example.invalid", b"a healthy barrier")
            self.assertTrue(w.readline().startswith(b"240"))
            self.stall.write_bytes(b"")
            issued = time.monotonic()
            self.send_article(a, b"stop2-a@example.invalid", b"in flight at the stop")
            time.sleep(0.3)
            self.send_article(e, b"stop2-e@example.invalid", b"prepared behind it")
            time.sleep(0.3)
            t0 = self.sigterm()
            answers, pending = self.stop_answers({"a": (a_conn, a), "e": (e_conn, e)}, 20)
            rest = {}
            for name, (conn, stream) in (("a", (a_conn, a)), ("e", (e_conn, e))):
                if name in answers:
                    rest[name] = stream.readline()
            time.sleep(1.0)
            running_while_stalled = self.owner.poll() is None
            self.stall.unlink()
            code = self.owner.wait(timeout=60)
        stopped = self.owner
        stat = self.restart_and_stat([b"stop2-a@example.invalid", b"stop2-e@example.invalid"])
        print("graceful stop past H (device stalled): answers %r then %r; exit %d; STAT %r"
              % ({k: (round(v[0] - issued, 3), v[1]) for k, v in answers.items()}, rest, code, stat))
        with node_log_on_failure(stopped):
            self.assertEqual(pending, {}, "a poster was not answered")
            for name in ("a", "e"):
                at, line = answers[name]
                self.assertTrue(line.startswith(b"441"), (name, line))
                self.assertIn(b"uncertain", line, (name, line))
                self.assertNotIn(b"try again later", line, (name, line))
                self.assertEqual(rest[name], b"", (name, rest[name]))
                self.assertLess(at - issued, 6.0 + 1.5, (name, at - issued))
            self.assertTrue(running_while_stalled)
            self.assertEqual(code, 0)
            # Uncertain allows either; the device came back, so they landed.
            self.assertTrue(set(stat.values()) <= {b"223", b"430"}, stat)

    def test_a_stop_with_clients_mid_article_and_mid_commit_ends_by_its_deadline(self):
        """Lane sigterm-hang (PRF-357 fn-osd-drain-stops-by-the-deadline):
        SIGTERM with 8 clients mid-article (POST, 340, half a header, the
        descriptor held open) and 8 POSTs mid-commit on a stalled barrier.
        The clients mid-article are owed nothing and never hold the drain;
        the device returns 1.5 s after the SIGTERM and each committed poster
        is told its outcome (240, or ACL2's 441: uncertain or try-later),
        never a bare close; the clients mid-article are closed; the owner
        exits 0 within H + grace (6 s + 10 s) of the SIGTERM.  After a
        restart every poster told 240 has its article (STAT 223), and one
        told try-later has none (430)."""
        self.policy("barrier-deadline-ms", 4000)
        self.policy("barrier-stall-ms", 6000)
        middle = [self.connect() for _ in range(8)]
        posters = [self.connect() for _ in range(8)]
        w_conn, w = self.connect()
        try:
            self.send_article(w, b"warm-mix@example.invalid", b"a healthy barrier")
            self.assertTrue(w.readline().startswith(b"240"))
            for _conn, stream in middle:
                stream.write(b"POST\r\n")
                stream.flush()
                self.assertTrue(stream.readline().startswith(b"340"))
                stream.write(b"From: incomplete")
                stream.flush()
            self.stall.write_bytes(b"")
            msgids = [b"mix-%d@example.invalid" % n for n in range(8)]
            for (_conn, stream), msgid in zip(posters, msgids):
                self.send_article(stream, msgid, b"mid-commit at the stop")
            time.sleep(0.3)
            t0 = self.sigterm()
            time.sleep(1.5)
            still_running = self.owner.poll() is None
            self.stall.unlink()
            answers, pending = self.stop_answers(
                {"p%d" % n: posters[n] for n in range(8)}, 20)
            closed, open_middle = self.stop_answers(
                {"m%d" % n: middle[n] for n in range(8)}, 20)
            code = self.owner.wait(timeout=30)
            exited = time.monotonic() - t0
        finally:
            for conn, _stream in middle + posters + [(w_conn, w)]:
                conn.close()
        stopped = self.owner
        stat = self.restart_and_stat(msgids)
        print("stop with 8 mid-article and 8 mid-commit: answers %r; mid-article %r; exit %d after %.3fs; STAT %r"
              % (sorted(set(v[1][:3] for v in answers.values())),
                 sorted(set(v[1] for v in closed.values())), code, exited, stat))
        with node_log_on_failure(stopped):
            self.assertTrue(still_running)
            self.assertEqual(pending, {}, "a committed poster was not answered")
            self.assertEqual(open_middle, {}, "a client mid-article was not closed")
            for name, (_at, line) in closed.items():
                self.assertFalse(line.startswith((b"240", b"441")), (name, line))
            self.assertEqual(code, 0)
            self.assertLess(exited, 6.0 + 10.0, exited)
            for n, msgid in enumerate(msgids):
                line = answers["p%d" % n][1]
                self.assertTrue(line.startswith((b"240", b"441")), (n, line))
                if line.startswith(b"240"):
                    self.assertEqual(stat[msgid], b"223", (n, line))
                elif b"uncertain" in line:
                    self.assertIn(stat[msgid], (b"223", b"430"), (n, line))
                else:
                    self.assertEqual(stat[msgid], b"430", (n, line))
            log = self.owner_log()
            self.assertIn(b"stopping: answering the posts in flight first", log)
            self.assertIn(b"stopping: drained after ", log)

    def test_a_peer_is_told_to_retry_while_the_disk_is_slow(self):
        """PKT-858 (lane log-leftovers): while the disk sheds, a peer's read
        is a reader-class quantum under the disk-slow posture
        (books/owner-time-admission.lisp fn-otm-peer-read-class,
        fn-otm-read-span; books/peer-inbound.lisp fn-peer-shed-p): IHAVE is
        answered 436 with the reason and CHECK 431 (RFC 3977 section 6.3.2,
        RFC 4644 section 2.4: the retry class), at once, even for an article
        the node holds (the live node carries the batch in flight, so no
        duplicate answer is given under the posture), and nothing is
        stored.  When the device comes back the same offer is wanted (335)
        and transferred (235): the transit path is unchanged."""
        self.policy("barrier-deadline-ms", 2000)
        self.policy("barrier-stall-ms", 120000)
        added = self.operator("peer", "add", "slowpeer", "slowpeer.example.invalid", "127.0.0.2",
                              "9", "fn.*", "-", "127.0.0.2", "true")
        self.assertEqual(added.returncode, 0, (added.stdout, added.stderr))
        w_conn, w = self.connect()
        a_conn, a = self.connect()
        peer_conn = socket.create_connection(("127.0.0.1", self.port), timeout=60,
                                             source_address=("127.0.0.2", 0))
        peer = peer_conn.makefile("rwb")
        greeting = peer.readline()
        self.assertTrue(greeting.startswith(b"200"), greeting)

        def ask(line):
            started = time.monotonic()
            peer.write(line + b"\r\n")
            peer.flush()
            return peer.readline(), time.monotonic() - started

        with w_conn, a_conn, peer_conn:
            self.send_article(w, b"warm3@example.invalid", b"a healthy barrier")
            self.assertTrue(w.readline().startswith(b"240"))
            before_held, _ = ask(b"IHAVE <warm3@example.invalid>")
            before_new, _ = ask(b"CHECK <peer-new-1@example.invalid>")
            self.stall.write_bytes(b"")
            t0 = time.monotonic()
            self.send_article(a, b"held3@example.invalid", b"its barrier stalls")
            time.sleep(max(0.0, t0 + 3.5 - time.monotonic()))
            _, health = self.timed_operator("health")
            self.assertIsNotNone(DISK_SLOW.search(health.stdout), health.stdout)
            ihave_new, ihave_new_at = ask(b"IHAVE <peer-new-2@example.invalid>")
            check_new, check_new_at = ask(b"CHECK <peer-new-3@example.invalid>")
            ihave_held, ihave_held_at = ask(b"IHAVE <warm3@example.invalid>")
            self.assertEqual(select.select([a_conn], [], [], 0)[0], [],
                             "the held POST was answered while its barrier stalled")
            self.stall.unlink()
            a_conn.settimeout(60)
            accepted = a.readline()
            # The transit path after the recovery: the same offer is wanted
            # and the article transferred.
            deadline = time.monotonic() + 30
            while True:
                offer, _ = ask(b"IHAVE <peer-new-2@example.invalid>")
                if not offer.startswith(b"436") or time.monotonic() > deadline:
                    break
                time.sleep(0.5)
            transferred = None
            if offer.startswith(b"335"):
                peer.write(b"Path: slowpeer.example.invalid!not-for-mail\r\n"
                           b"From: peer@example.invalid\r\nNewsgroups: fn.test\r\n"
                           b"Subject: after the stall\r\nDate: "
                           + time.strftime("%a, %d %b %Y %H:%M:%S +0000", time.gmtime()).encode()
                           + b"\r\nMessage-ID: <peer-new-2@example.invalid>\r\n\r\nbody\r\n.\r\n")
                peer.flush()
                transferred = peer.readline()
            for stream in (w, a, peer):
                try:
                    stream.write(b"QUIT\r\n")
                    stream.flush()
                except OSError:
                    pass
        print("peer during slow: IHAVE new %r in %.3fs; CHECK new %r in %.3fs; IHAVE held %r in %.3fs; "
              "before: %r %r; after recovery: POST %r, IHAVE %r, transfer %r"
              % (ihave_new, ihave_new_at, check_new, check_new_at, ihave_held, ihave_held_at,
                 before_held, before_new, accepted, offer, transferred))
        self.assertTrue(before_held.startswith(b"435"), before_held)
        self.assertEqual(before_new, b"238 <peer-new-1@example.invalid>\r\n")
        self.assertEqual(ihave_new, b"436 retry later; the disk is slow\r\n")
        self.assertEqual(check_new, b"431 <peer-new-3@example.invalid>\r\n")
        self.assertEqual(ihave_held, b"436 retry later; the disk is slow\r\n")
        for at in (ihave_new_at, check_new_at, ihave_held_at):
            self.assertLess(at, 2.0, at)
        self.assertTrue(accepted.startswith(b"240"), accepted)
        self.assertTrue(offer.startswith(b"335"), offer)
        self.assertTrue(transferred is not None and transferred.startswith(b"235"), transferred)


if __name__ == "__main__":
    unittest.main()

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
import os
from pathlib import Path
import re
import select
import signal
import socket
import subprocess
import tempfile
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
# The developer image: the only one that honours a developer selector.
DEVELOPER = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
STALL_SECONDS = float(os.environ.get("FN_SLOW_DISK_STALL_SECONDS", "30"))
DISK_SLOW = re.compile(rb"^disk slow: barrier (\d+) ms pending deadline-ms=(\d+) stall-ms=(\d+) "
                       rb"slow-episodes=(\d+) stalls=(\d+) posts=try-later$", re.M)
DISK_STALLED = re.compile(rb"^disk stalled: barrier (\d+) ms pending deadline-ms=(\d+) stall-ms=(\d+) "
                          rb"slow-episodes=(\d+) stalls=(\d+) posts=try-later members=uncertain$", re.M)
DISK_OK = re.compile(rb"^disk ok: pending-ms=(\d+) last-barrier-ms=(\d+) max-barrier-ms=(\d+) "
                     rb"deadline-ms=(\d+) stall-ms=(\d+) slow-episodes=(\d+) stalls=(\d+)$", re.M)


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    return env


def executable(image):
    return image.is_file() and os.access(image, os.X_OK)


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


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
        self.assertLess(pipeline.index("(fnn-owner-start-syncer service)"),
                        pipeline.index("(fnn-owner-disk-event service :issue limits)"))
        # Slice 2: past H every member is told uncertain, once per barrier,
        # and the queued POSTs are shed; the told members are not answered
        # again at the COMPLETE.
        self.assertIn("(fnn-owner-disk-stalled-p service)", pipeline)
        self.assertIn("(fnn-owner-stall-release", pipeline)
        self.assertIn("(fnn-owner-journal-note service (length told) shed)", pipeline)
        self.assertIn("(fnn-owner-unreleased members released)", pipeline)
        event = owner[owner.index("(defun fnn-owner-disk-event "):owner.index("(defun fnn-owner-journal-note")]
        self.assertIn("'fn-otm-disk-step", event)
        self.assertIn("(fnn-journal-line entry)", event)
        # the reading is taken inside the gate mutex, never passed in
        self.assertLess(event.index("(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))"),
                        event.index("(setq reading (fnn-owner-monotonic-ms))"))
        chunk = owner[owner.index("(defun fnn-owner-handle-chunk-read "):owner.index("(defun fnn-owner-exposure-idle")]
        self.assertLess(chunk.index("(fnn-owner-advance-clock)"),
                        chunk.index("(multiple-value-setq (admit replies) (fnn-owner-read-admission service))"))
        self.assertIn("'fn-owner-chunk-span cid 0 (length incoming) admit replies)", chunk)
        admit = owner[owner.index("(defun fnn-owner-disk-admission "):owner.index("(defun fnn-owner-read-admission")]
        self.assertIn("'fn-otm-admit-post", admit)
        # The read's admission and ACL2's reply lines naming the disk's
        # reason come from one scheduler value (fn-otm-shed-replies).
        read = owner[owner.index("(defun fnn-owner-read-admission "):owner.index("(defun fnn-owner-disk-stalled-p")]
        self.assertEqual(read.count("(fnn-owner-gate-sched gate)"), 1, read)
        self.assertIn("(fnn-core 'fn-otm-admit-post sched)", read)
        self.assertIn("(fnn-core 'fn-otm-shed-replies sched)", read)
        clock = owner[owner.index("(defun fnn-owner-advance-clock "):owner.index("(defun fnn-owner-finish ")]
        self.assertIn(":served", clock)
        control = (ROOT / "host" / "native" / "control.lisp").read_text()
        self.assertIn("(eq (fnn-owner-disk-admit service) :shed))\n                    :busy)", control)
        shed = owner[owner.index("(defun fnn-owner-shed-queued-locked "):]
        self.assertIn("'fn-owner-shed-outcome", shed[:2000])
        wrapper = (ROOT / "host" / "owner-host.lisp").read_text()
        self.assertIn("(fn-otm-read-span\n", wrapper)
        self.assertIn("(fn-otm-shed-reply s)", wrapper)
        self.assertIn("(fn-owner-outcome id :refused state)", wrapper)
        live = (ROOT / "host" / "native-live-status-host.lisp").read_text()
        self.assertIn("(fn-otm-health-lines sched)", live)
        self.assertIn("(fn-otm-disk-lines sched)", live)


@unittest.skipUnless(executable(DEVELOPER), "no developer image at %s" % DEVELOPER)
class SlowDiskNativeTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="fn-slowdisk-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.config = self.root / "fn.toml"
        self.stall = self.root / "stall"
        self.port = free_port()
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        init = self.operator("init", "--max-article-octets", "1048576", "fn.test")
        self.assertEqual(init.returncode, 0, init.stderr.decode())
        self.log = open(self.root / "owner.stderr", "wb")
        self.addCleanup(self.log.close)
        self.addCleanup(lambda: self.stall.unlink() if self.stall.exists() else None)
        self.owner = self.start_owner({"FN_NATIVE_TEST_DISK_STALL_FILE": str(self.stall)})

    def operator(self, *words, timeout=60):
        return subprocess.run(
            [str(DEVELOPER), "--fn", "operator", str(self.config), *words],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False)

    def start_owner(self, extra):
        env = environment()
        env.update(extra)
        process = subprocess.Popen(
            [str(DEVELOPER), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=self.log, bufsize=0)
        self.addCleanup(self.reap, process)
        for _ in range(4):
            self.assertTrue(select.select([process.stdout], [], [], 180)[0],
                            "the owner did not become ready")
            line = process.stdout.readline()
            if line.startswith(b"LISTENING "):
                return process
            self.assertIsNone(process.poll(), "the owner exited before listening")
        self.fail("the owner's readiness output was malformed")

    def reap(self, process):
        if self.stall.exists():
            self.stall.unlink()
        if process.poll() is None:
            process.send_signal(signal.SIGTERM)
            try:
                process.wait(timeout=60)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=10)
        if process.stdout and not process.stdout.closed:
            process.stdout.close()

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
        # fn-otm-disk-reply-effects over fn-otm-shed-replies' lines).
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
        log = (self.root / "owner.stderr").read_bytes()
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
        log = (self.root / "owner.stderr").read_bytes()
        self.assertIn(b"disk stalled: a barrier has waited ", log)
        self.assertIn(b"disk recovered after a stall: the barrier completed after ", log)
        # The decision journal: this run's segment, entries in sequence
        # (books/owner-time-journal.lisp: (SEQ OP READING A B C WORD)).
        journal = (self.store / "decisions" / "decisions.fnj").read_bytes()
        entries = [[int(x) for x in line.split(b" ")] for line in journal.split(b"\n") if line]
        start = max(i for i, entry in enumerate(entries) if entry[1] == 0)
        segment = entries[start + 1:]
        self.assertTrue(all(len(entry) == 7 for entry in entries))
        self.assertEqual([entry[0] for entry in segment], list(range(1, len(segment) + 1)))
        readings = [entry[2] for entry in segment if entry[1] in (1, 2, 3, 4)]
        self.assertEqual(readings, sorted(readings), "the recorded time went backwards")
        self.assertIn([3, 2000, 6000, 250], [[e[1], e[3], e[4], e[5]] for e in segment])
        self.assertTrue(any(e[1] in (1, 2) and e[6] == 6 for e in segment), "no :became-stalled")
        self.assertIn([5, 2, 1], [[e[1], e[3], e[4]] for e in segment])
        self.assertTrue(any(e[1] == 4 and e[6] == 4 for e in segment), "no :recovered-from-stall")
        print("journal: %d entries in this run's segment, %d bytes in the file" % (len(segment), len(journal)))
        # The operator's replay (`store ROOT journal', ACL2's fn-otm-replay).
        replay = subprocess.run([str(DEVELOPER), "--fn", "store", str(self.store), "journal"],
                                cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=120, check=False)
        print("store journal: rc=%d %r" % (replay.returncode, replay.stdout))
        self.assertEqual(replay.returncode, 0, (replay.stdout, replay.stderr))
        self.assertIn(b" replay=agrees", replay.stdout)


if __name__ == "__main__":
    unittest.main()

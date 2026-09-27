"""A stalled disk on a native image (lane time-model, 2026-09-27; PRF-308,
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
DISK_SLOW = re.compile(rb"^disk slow: barrier (\d+) ms pending deadline-ms=(\d+) "
                       rb"slow-episodes=(\d+) posts=try-later$", re.M)
DISK_OK = re.compile(rb"^disk ok: pending-ms=(\d+) last-barrier-ms=(\d+) max-barrier-ms=(\d+) "
                     rb"deadline-ms=(\d+) slow-episodes=(\d+)$", re.M)


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
        self.assertIn("(fnn-owner-disk-event service :issue deadline)", pipeline)
        self.assertIn("(fnn-owner-disk-event service :return)", pipeline)
        self.assertIn("(fnn-owner-disk-event service :clock)", pipeline)
        self.assertIn("(fnn-owner-disk-wait-ms service)", pipeline)
        self.assertIn(":timeout (/ ms 1000)", pipeline)
        self.assertLess(pipeline.index("(fnn-owner-start-syncer service)"),
                        pipeline.index("(fnn-owner-disk-event service :issue deadline)"))
        event = owner[owner.index("(defun fnn-owner-disk-event "):owner.index("(defun fnn-owner-disk-wait-ms")]
        self.assertIn("'fn-otm-disk-event", event)
        # the reading is taken inside the gate mutex, never passed in
        self.assertIn("(fnn-owner-monotonic-ms) deadline)", event)
        chunk = owner[owner.index("(defun fnn-owner-handle-chunk-read "):owner.index("(defun fnn-owner-exposure-idle")]
        self.assertLess(chunk.index("(fnn-owner-disk-admit service)"),
                        chunk.index("(fnn-owner-note-queued service)"))
        admit = owner[owner.index("(defun fnn-owner-disk-admit "):owner.index("(defun fnn-owner-shed-queued-locked")]
        self.assertIn("'fn-otm-admit-post", admit)
        shed = owner[owner.index("(defun fnn-owner-shed-queued-locked "):]
        self.assertIn("'fn-owner-shed-outcome", shed[:2000])
        wrapper = (ROOT / "host" / "owner-host.lisp").read_text()
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
        stream.write(b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                     b"Subject: slow disk\r\nMessage-ID: <" + msgid + b">\r\n\r\n"
                     + body + b"\r\n.\r\n")
        stream.flush()

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
        reader_conn, reader = self.connect()
        a_conn, a = self.connect()
        b_conn, b = self.connect()
        c_conn, c = self.connect()
        with reader_conn, a_conn, b_conn, c_conn:
            # A healthy barrier first: W is stored, `health' says ok.
            self.send_article(c, b"warm@example.invalid", b"a healthy barrier")
            line = c.readline()
            self.assertTrue(line.startswith(b"240"), line)
            _, health = self.timed_operator("health")
            self.assertIsNotNone(DISK_OK.search(health.stdout), health.stdout)
            baseline = [self.timed_read(reader, b"GROUP fn.test\r\n", b"211") for _ in range(5)]

            # The device stalls.  A's batch goes in flight and stays there.
            self.stall.write_bytes(b"")
            self.send_article(a, b"held@example.invalid", b"its barrier stalls")
            t0 = time.monotonic()
            reads, controls, healths = [], [], []
            slow_line = None
            refused = None
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
                    # A new POST while the disk is slow: refused at once,
                    # with the reason; nothing stored.
                    sent = time.monotonic()
                    self.send_article(b, b"shed@example.invalid", b"refused try-later")
                    refused = b.readline()
                    refused_at = time.monotonic() - sent
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
            last_barrier_ms, episodes = int(ok.group(2)), int(ok.group(5))
            # The next POST is accepted.
            self.send_article(c, b"after@example.invalid", b"after the stall")
            after = c.readline()
            # The reader's pin moves at its next GROUP (a reader keeps the
            # version it opened on until then).
            self.timed_read(reader, b"GROUP fn.test\r\n", b"211")
            stat_shed = self.timed_read(reader, b"STAT <shed@example.invalid>\r\n", b"430")
            stat_after = self.timed_read(reader, b"STAT <after@example.invalid>\r\n", b"223")
            stat_a = self.timed_read(reader, b"STAT <held@example.invalid>\r\n", b"223")
            for s in (reader, a, b, c):
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
        self.assertTrue(refused.startswith(b"441 posting failed; the disk is slow"), refused)
        self.assertIn(b"nothing was stored, try again later", refused)
        self.assertLess(refused_at, 2.0, refused_at)
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


if __name__ == "__main__":
    unittest.main()

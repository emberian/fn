"""The owner's scheduler gate and render plans on a native image (HST-023,
PRF-248; lane owner-scheduler, 2026-09-26).

The owner mutex is entered through a gate that names each quantum's service
class; ACL2 picks the class that runs next (books/owner-scheduler.lisp
fn-osch-next) and folds every quantum's hold and wait into the lines
`health' prints (fn-osch-health-lines).  A served step returns a render plan
the connection's thread renders off the mutex in 64 KiB windows
(books/served-plan.lisp fn-splan-window).

What this module asserts on the image:
  * `health' carries the scheduler's five lines after the exposure and
    log-sink lines, with the classes that ran counted where they ran:
    reader quanta for the NNTP session, control quanta for the control
    socket's own requests, none for posters and transit;
  * a reply larger than one render window (an ARTICLE with a 200 KiB body)
    is served byte-identical to what was posted, dot-stuffed and terminated
    (the plan's windows concatenate to the reply);
  * under three tight-loop readers a control-socket request (`status') is
    answered within its 10 s deadline, every time, and no held quantum
    reached a second: the bound the gate gives control, observed.
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
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host-developer"))
# The developer image: the only one that honours a developer selector
# (FN_NATIVE_OWNER_TEST_BARRIER_MS); a production image refuses to start.
DEVELOPER = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))

SCHED_HEAD = re.compile(rb"^sched order=control,reader,poster,transit bound=(\d+) cursor=(\d+)$", re.M)
SCHED_ROW = re.compile(
    rb"^sched (control|reader|poster|transit) holds=(\d+) hold<1ms=(\d+) hold<10ms=(\d+) "
    rb"hold<100ms=(\d+) hold<1s=(\d+) hold>=1s=(\d+) hold-max-ms=(\d+) wait-max-ms=(\d+) waits>=1s=(\d+)$", re.M)


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


def stuffed(body):
    return b"".join((b"." + line if line.startswith(b".") else line) + b"\r\n"
                    for line in body.split(b"\r\n"))


class SchedulerSourceTests(unittest.TestCase):
    """What the source has to say, whether or not an image was built."""

    def test_every_owner_entry_is_gated_and_the_reply_leaves_the_mutex(self):
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text()
        serialized = owner[owner.index("(defun fnn-owner-serialized "):owner.index("(defun fnn-owner-consume-connection-fault")]
        self.assertIn("(fnn-owner-gated (service class)", serialized)
        # books/owner-commit-pipeline.lisp (lane log-2) over
        # books/owner-commit-steps.lisp (PKT-688 (4) slice 2): the gate's pick
        # and fold are fn-ocp-next / fn-ocp-observe, which are fn-ocs-next's
        # (fn-ocp-next-is-ocs-next; fn-ocm-next's pick outside a batch,
        # fn-osch-next's for the four classes: PRF-267, PRF-248).
        self.assertIn("'fn-ocp-next", owner)
        self.assertIn("'fn-ocp-observe", owner)
        # The committer's pipeline: START (it seals) as a :commit quantum, the
        # SYNC in the syncer thread with the owner released, at most one
        # START-NEXT (not sealed) behind it, then COMPLETE as a :commit
        # quantum, which seals the next batch only after the replies.
        batch = owner[owner.index("(defun fnn-owner-commit-pipeline "):owner.index("(defun fnn-owner-committer-loop")]
        self.assertIn("'fn-ocp-commit-event", owner)
        self.assertIn("'fn-ocp-committer-wake", owner)
        self.assertLess(batch.index("(fnn-owner-commit-start-locked service)"),
                        batch.index("(fnn-owner-start-syncer service)"))
        self.assertLess(batch.index("(fnn-owner-start-syncer service)"),
                        batch.index("(fnn-owner-commit-start-locked service :seal nil)"))
        self.assertLess(batch.index("(sb-thread:join-thread syncer"),
                        batch.index("(fnn-owner-commit-complete-locked service :complete members deferred)"))
        self.assertLess(batch.index("(fnn-owner-commit-complete-locked service :complete members deferred)"),
                        batch.index("(fnn-log-seal-open-batch store)"))
        self.assertEqual(batch.count("(fnn-owner-start-syncer service)"), 1)
        syncer = owner[owner.index("(defun fnn-owner-commit-sync "):owner.index("(defun fnn-owner-commit-complete-locked")]
        self.assertIn("(fnn-log-sync-sealed-batch ", syncer)
        control = (ROOT / "host" / "native" / "control.lisp").read_text()
        live = control[control.index("(defun fnn-control-live-status-answer "):control.index("(defun fnn-control-handle-client")]
        self.assertIn(":inspect))", live)
        # Each member's reply is the release ACL2 names (fn-ocs-member-releases,
        # keystone fn-ocs-members-told-only-after-the-barrier): the COMPLETE
        # takes ACL2's action, never a host-computed flag, and the inline
        # commit asks fn-ocs-commit-step for its steps.
        complete = owner[owner.index("(defun fnn-owner-commit-complete-locked "):owner.index("(defun fnn-owner-commit-step-action")]
        self.assertIn("'fn-ocs-member-releases action", complete)
        self.assertNotIn("(cons :close (second m))", complete)
        inline = owner[owner.index("(defun fnn-owner-commit-queued-locked "):owner.index("(defun fnn-owner-commit-event ")]
        self.assertIn("fnn-owner-commit-step-action", inline)
        self.assertIn("'fn-ocs-commit-step", owner)
        # fnn-core answers an mv function's FIRST value (the action): taking
        # (first ...) of that keyword is a memory fault at nil in the saved
        # image's compiled code (the operator post's inline commit, AW r4).
        step = owner[owner.index("(defun fnn-owner-commit-step-action "):owner.index("(defun fnn-owner-commit-queued-locked ")]
        self.assertIn("(fnn-core 'fn-ocs-commit-step phase event)", step)
        self.assertNotIn("(first (fnn-core", step)
        commit_class = (ROOT / "books" / "owner-commit-class.lisp").read_text()
        self.assertIn("(fn-osch-next (fn-ocm-sched s) w)", commit_class)
        self.assertIn("(fn-osch-observe (fn-ocm-sched s) class hold-ms wait-ms)", commit_class)
        self.assertIn("'fn-splan-window", owner)
        self.assertNotIn("fnn-owner-reply-from-buffer", owner)
        self.assertNotIn("(defun fnn-owner-exposure-wait", owner)
        chunk = owner[owner.index("(defun fnn-owner-handle-chunk "):owner.index("(defun fnn-owner-exposure-idle")]
        self.assertIn("'fn-owner-exposure-charge", chunk)
        self.assertIn("'fn-splan-step-plan", chunk)
        self.assertNotIn("fnn-owner-send", chunk)
        wrapper = (ROOT / "host" / "owner-host.lisp").read_text()
        self.assertNotIn("(defun fn-owner-reply-buffer", wrapper)
        self.assertIn("fn-splan-step-make", wrapper)


@unittest.skipUnless(executable(IMAGE), "no native image at %s" % IMAGE)
class SchedulerNativeTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="fn-sched-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.config = self.root / "fn.toml"
        self.port = free_port()
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        init = self.operator("init", "--max-article-octets", "1048576", "fn.test")
        self.assertEqual(init.returncode, 0, init.stderr.decode())
        self.owner = self.start_owner()

    def operator(self, *words, timeout=60):
        return subprocess.run(
            [str(IMAGE), "--fn", "operator", str(self.config), *words],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False)

    def start_owner(self, extra=None, image=None, stderr=None):
        env = environment()
        env.update(extra or {})
        process = subprocess.Popen(
            [str(image or IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE,
            stderr=stderr or subprocess.DEVNULL, bufsize=0)
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
        if process.poll() is None:
            process.send_signal(signal.SIGTERM)
            try:
                process.wait(timeout=30)
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

    def post(self, stream, msgid, body):
        stream.write(b"POST\r\n")
        stream.flush()
        self.assertTrue(stream.readline().startswith(b"340"))
        stream.write(b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                     b"Subject: scheduler\r\nMessage-ID: <" + msgid + b">\r\n\r\n"
                     + stuffed(body) + b".\r\n")
        stream.flush()
        reply = stream.readline()
        self.assertTrue(reply.startswith(b"240"), reply)

    def multiline(self, stream):
        lines = []
        while True:
            line = stream.readline()
            self.assertTrue(line, "the reply ended before the terminator")
            if line == b".\r\n":
                return b"".join(lines)
            lines.append(line)

    def sched(self):
        health = self.operator("health")
        text = health.stdout
        self.assertTrue(text.startswith(b"health exit="), text)
        head = SCHED_HEAD.search(text)
        self.assertIsNotNone(head, text.decode("ascii", "replace"))
        rows = {m.group(1).decode(): tuple(int(g) for g in m.groups()[1:])
                for m in SCHED_ROW.finditer(text)}
        self.assertEqual(sorted(rows), ["control", "poster", "reader", "transit"], text)
        # The log-sink line precedes the scheduler's (fn-nh-report-exit-of-render-and-more:
        # the exit is the verdict's whatever follows).
        self.assertLess(text.index(b"log-sink "), text.index(b"sched order="), text)
        return int(head.group(1)), rows

    def test_health_carries_the_scheduler_lines_and_counts_the_classes(self):
        # Each class counts its own quanta and no other's: a reader
        # connection's steps are reader holds, the health requests control
        # holds, one submission through the control socket exactly one poster
        # hold (host/native/owner.lisp fnn-owner-control-submit-serialized),
        # and with no peer configured the transit class holds only the feed
        # worker's idle polls (host/native/feed-service.lisp fnn-feed-worker:
        # fnn-feed-peer-list every +fnn-feed-poll-seconds+ = 1/20 s, one
        # :transit quantum each), so they grow with the window and by no more
        # than it allows.
        bound, before = self.sched()
        self.assertEqual(bound, 3)
        started = time.monotonic()
        conn, stream = self.connect()
        with conn:
            for _ in range(10):
                stream.write(b"GROUP fn.test\r\n")
                stream.flush()
                self.assertTrue(stream.readline().startswith(b"211"))
            stream.write(b"QUIT\r\n")
            stream.flush()
        payload = self.root / "poster.eml"
        payload.write_bytes(b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                            b"Subject: the poster class\r\n"
                            b"Date: Sun, 27 Sep 2026 04:00:00 +0000\r\n"
                            b"Message-ID: <sched-poster@example.invalid>\r\n\r\n"
                            b"one poster quantum\r\n")
        posted = self.operator("post", "--message-id", "<sched-poster@example.invalid>",
                               "--payload", str(payload), "--group", "fn.test", timeout=120)
        self.assertEqual(posted.returncode, 0,
                         posted.stdout.decode("ascii", "replace") + posted.stderr.decode("ascii", "replace"))
        time.sleep(0.5)
        bound, after = self.sched()
        elapsed = time.monotonic() - started
        # holds, then the five buckets, hold-max, wait-max, waits>=1s
        self.assertGreaterEqual(after["reader"][0] - before["reader"][0], 10,
                                (before, after))
        self.assertGreater(after["control"][0], before["control"][0], (before, after))
        self.assertEqual(after["poster"][0] - before["poster"][0], 1, (before, after))
        transit = after["transit"][0] - before["transit"][0]
        self.assertGreaterEqual(transit, 1, (before, after))
        self.assertLessEqual(transit, int(elapsed * 20) + 2, (elapsed, before, after))
        for name, row in after.items():
            self.assertEqual(sum(row[1:6]), row[0], (name, row))

    def test_a_reply_larger_than_a_render_window_is_the_posted_article(self):
        body = b"\r\n".join((b"." if n % 40 == 0 else b"line %d %s" % (n, b"x" * 60))
                            for n in range(3000))
        self.assertGreater(len(body), 2 * 65536)
        conn, stream = self.connect()
        with conn:
            self.post(stream, b"window@example.invalid", body)
            stream.write(b"GROUP fn.test\r\n")
            stream.flush()
            self.assertTrue(stream.readline().startswith(b"211"))
            stream.write(b"ARTICLE <window@example.invalid>\r\n")
            stream.flush()
            status = stream.readline()
            self.assertTrue(status.startswith(b"220"), status)
            article = self.multiline(stream)
            self.assertTrue(article.endswith(b"\r\n\r\n" + stuffed(body)), article[-200:])
            stream.write(b"BODY <window@example.invalid>\r\n")
            stream.flush()
            self.assertTrue(stream.readline().startswith(b"222"))
            self.assertEqual(self.multiline(stream), stuffed(body))
            stream.write(b"QUIT\r\n")
            stream.flush()

    def test_control_requests_are_answered_under_three_tight_loop_readers(self):
        conn, stream = self.connect()
        with conn:
            for n in range(200):
                self.post(stream, b"storm-%d@example.invalid" % n, b"body %d\r\n" % n + b"y" * 1500)
            stream.write(b"QUIT\r\n")
            stream.flush()
        stop = threading.Event()
        errors = []

        def reader(index):
            try:
                c, s = self.connect()
                with c:
                    n = 1
                    while not stop.is_set():
                        s.write(b"GROUP fn.test\r\n")
                        s.flush()
                        if not s.readline().startswith(b"211"):
                            errors.append("reader %d: GROUP refused" % index)
                            return
                        s.write(b"OVER %d-%d\r\n" % (max(1, n - 20), n))
                        s.flush()
                        if s.readline().startswith(b"224"):
                            self.multiline(s)
                        s.write(b"ARTICLE %d\r\n" % n)
                        s.flush()
                        if s.readline().startswith(b"220"):
                            self.multiline(s)
                        n = n % 200 + 1
            except Exception as error:  # noqa: BLE001 -- reported below
                errors.append("reader %d: %r" % (index, error))

        threads = [threading.Thread(target=reader, args=(i,), daemon=True) for i in range(3)]
        for thread in threads:
            thread.start()
        time.sleep(1.0)
        latencies = []
        try:
            for _ in range(12):
                started = time.monotonic()
                status = self.operator("status", timeout=30)
                latencies.append(time.monotonic() - started)
                self.assertEqual(status.returncode, 0, status.stderr.decode())
                self.assertIn(b"transactions=", status.stdout)
                time.sleep(0.25)
        finally:
            stop.set()
            for thread in threads:
                thread.join(timeout=30)
        self.assertEqual(errors, [])
        # The deadline the qualification's client used (PKT-321); every one of
        # these is a control quantum admitted within the bound.
        self.assertLess(max(latencies), 10.0, latencies)
        bound, rows = self.sched()
        self.assertGreaterEqual(rows["control"][0], 12, rows)
        self.assertGreater(rows["reader"][0], 12, rows)
        print("control status under 3 readers: n=%d max=%.3fs p50=%.3fs; sched control=%s reader=%s"
              % (len(latencies), max(latencies), sorted(latencies)[len(latencies) // 2],
                 rows["control"], rows["reader"]))

    @unittest.skipUnless(executable(DEVELOPER), "no developer image at %s" % DEVELOPER)
    def group_count(self, stream):
        stream.write(b"GROUP fn.test\r\n")
        stream.flush()
        line = stream.readline()
        self.assertTrue(line.startswith(b"211 "), line)
        return int(line.split()[1])

    def stat(self, stream, msgid):
        stream.write(b"STAT <" + msgid + b">\r\n")
        stream.flush()
        return stream.readline()

    def begin_post(self, stream, msgid, body):
        stream.write(b"POST\r\n")
        stream.flush()
        self.assertTrue(stream.readline().startswith(b"340"))
        stream.write(b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                     b"Subject: in flight\r\nMessage-ID: <" + msgid + b">\r\n\r\n"
                     + stuffed(body) + b".\r\n")
        stream.flush()

    def test_status_and_readers_are_answered_while_a_batch_barrier_is_in_flight(self):
        # PKT-688 (4) slice 2 and PKT-828 (books/owner-commit-steps.lisp,
        # books/owner-reader-view.lisp).  The developer selector holds the
        # committer's barrier open for 6 s with the owner RELEASED.  While it
        # is open: `status' (the :inspect class) is answered; a reader's GROUP
        # and STAT (the :reader class) are answered too
        # (fn-ocs-in-flight-admits-only-inspect-commit-and-reader), at the
        # reader view: the in-flight article is not counted and not found
        # (fn-ocvm-reader-view-is-the-completed-prefix); the POST's 240 leaves
        # only after the barrier (fn-ocs-members-told-only-after-the-barrier),
        # and from then on the reader counts and finds it.
        self.reap(self.owner)
        hold = 6.0
        self.owner = self.start_owner({"FN_NATIVE_OWNER_TEST_BARRIER_MS": str(int(hold * 1000))},
                                      image=DEVELOPER)
        reader_conn, reader = self.connect()
        poster_conn, poster = self.connect()
        with reader_conn, poster_conn:
            before = self.group_count(reader)
            self.begin_post(poster, b"in-flight@example.invalid", b"held at the barrier\r\n")
            posted = time.monotonic()
            time.sleep(0.5)
            during = self.group_count(reader)
            during_at = time.monotonic() - posted
            stat_during = self.stat(reader, b"in-flight@example.invalid")
            answered = []
            for _ in range(2):
                status = self.operator("status", timeout=30)
                answered.append(time.monotonic() - posted)
                self.assertEqual(status.returncode, 0, status.stderr.decode())
                self.assertIn(b"transactions=", status.stdout)
            reply = poster.readline()
            accepted = time.monotonic() - posted
            after = self.group_count(reader)
            stat_after = self.stat(reader, b"in-flight@example.invalid")
            reader.write(b"QUIT\r\n")
            reader.flush()
            poster.write(b"QUIT\r\n")
            poster.flush()
        print("barrier held %.1fs: status answered at %s; GROUP at %.3fs (%d, before %d, after %d); "
              "STAT during %r; 240 at %.3fs"
              % (hold, ["%.3f" % a for a in answered], during_at, during, before, after,
                 stat_during, accepted))
        self.assertTrue(reply.startswith(b"240"), reply)
        # The 240 waited for the barrier (the selector applies only to the
        # log route's committer: a store that did not batch fails here).
        self.assertGreaterEqual(accepted, hold - 0.1, accepted)
        # Both status requests and the reader were answered while the barrier
        # was open, the reader at the durable view.
        self.assertLess(max(answered), hold - 0.5, answered)
        self.assertLess(during_at, hold - 0.5, during_at)
        self.assertEqual(during, before)
        self.assertFalse(stat_during.startswith(b"223"), stat_during)
        # After the COMPLETE the article is counted and found.
        self.assertEqual(after, before + 1)
        self.assertTrue(stat_after.startswith(b"223"), stat_after)
        bound, rows = self.sched()
        self.assertEqual(sorted(rows), ["control", "poster", "reader", "transit"])

    def test_the_next_batch_is_prepared_while_the_previous_one_syncs(self):
        # PKT-828 (books/owner-commit-pipeline.lisp START-NEXT,
        # books/owner-reader-view.lisp).  Barrier held 4 s.  POST A's batch
        # goes in flight; POST B, sent 1 s later, is prepared BEHIND that
        # barrier (the developer trace line; fn-olr-take-never-joins-the-
        # batch-in-flight) and sealed by A's COMPLETE, so its 240 comes one
        # barrier after A's, not two.  A reader during A's barrier counts
        # neither; between A's 240 and B's it counts A and not B; after B's,
        # both.
        self.reap(self.owner)
        hold = 4.0
        trace = open(self.root / "pipeline.stderr", "wb")
        self.addCleanup(trace.close)
        self.owner = self.start_owner({"FN_NATIVE_OWNER_TEST_BARRIER_MS": str(int(hold * 1000)),
                                       "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE": "1"},
                                      image=DEVELOPER, stderr=trace)
        reader_conn, reader = self.connect()
        a_conn, a = self.connect()
        b_conn, b = self.connect()
        with reader_conn, a_conn, b_conn:
            before = self.group_count(reader)
            self.begin_post(a, b"pipe-a@example.invalid", b"first batch\r\n")
            t0 = time.monotonic()
            time.sleep(1.0)
            self.begin_post(b, b"pipe-b@example.invalid", b"second batch\r\n")
            time.sleep(0.5)
            count1 = self.group_count(reader)
            at1 = time.monotonic() - t0
            reply_a = a.readline()
            at_a = time.monotonic() - t0
            count2 = self.group_count(reader)
            stat_a2 = self.stat(reader, b"pipe-a@example.invalid")
            stat_b2 = self.stat(reader, b"pipe-b@example.invalid")
            reply_b = b.readline()
            at_b = time.monotonic() - t0
            count3 = self.group_count(reader)
            stat_b3 = self.stat(reader, b"pipe-b@example.invalid")
            for stream in (reader, a, b):
                stream.write(b"QUIT\r\n")
                stream.flush()
        self.reap(self.owner)
        trace.flush()
        lines = (self.root / "pipeline.stderr").read_bytes()
        print("pipeline (barrier %.1fs): GROUP %d at %.3fs; A 240 at %.3fs; GROUP %d; "
              "B 240 at %.3fs; GROUP %d (before %d); trace %r"
              % (hold, count1, at1, at_a, count2, at_b, count3, before,
                 [l for l in lines.splitlines() if b"pipeline" in l or b"start:" in l]))
        self.assertTrue(reply_a.startswith(b"240"), reply_a)
        self.assertTrue(reply_b.startswith(b"240"), reply_b)
        self.assertIn(b"prepared behind the barrier", lines, lines[-2000:])
        # During A's barrier the reader counts neither.
        self.assertLess(at1, hold - 0.5, at1)
        self.assertEqual(count1, before)
        # Between the two COMPLETEs: A, not B.
        self.assertEqual(count2, before + 1)
        self.assertTrue(stat_a2.startswith(b"223"), stat_a2)
        self.assertFalse(stat_b2.startswith(b"223"), stat_b2)
        # B was prepared behind A's barrier: its 240 is one barrier after A's.
        self.assertGreaterEqual(at_a, hold - 0.1, at_a)
        self.assertLess(at_b, at_a + hold + 1.5, (at_a, at_b))
        self.assertEqual(count3, before + 2)
        self.assertTrue(stat_b3.startswith(b"223"), stat_b3)


    def test_a_redeem_during_a_barrier_waits_for_the_complete_without_holding_the_owner(self):
        # PKT-828 open item 2 (books/owner-reader-read.lisp).  An XREDEEM PASS
        # publishes a configuration record: its reply (281) promises the
        # credential is durable, and the record is a configuration record,
        # not a log record, so it runs in a quantum of its own of ACL2's
        # publication class (fnn-owner-redeem-quantum, fn-ocs-publication-
        # class), which the scheduler never admits while a batch is in flight
        # (fn-ocs-a-publication-waits-for-the-complete).  Barrier held 4 s: a
        # POST's batch goes in flight; the PASS, sent 0.5 s in, is answered
        # 281 only after the COMPLETE (with the 240, not before it), while a
        # reader's GROUP 1 s in is answered inside the barrier (the redeem
        # holds nothing while it waits).  The account then logs in.
        import ssl
        self.reap(self.owner)
        hold = 4.0
        cert, key = self.root / "cert.pem", self.root / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key),
                        "-out", str(cert), "-days", "2", "-nodes", "-subj", "/CN=127.0.0.1",
                        "-addext", "subjectAltName=IP:127.0.0.1"], check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        tls_port = free_port()
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\ntls_port = {}\n'
            'tls_cert = "{}"\ntls_key = "{}"\n'
            '[control]\npath = "{}"\n[auth]\nprotected_only = true\n'.format(
                self.store, self.port, tls_port, cert, key, self.control),
            encoding="ascii")
        self.owner = self.start_owner({"FN_NATIVE_OWNER_TEST_BARRIER_MS": str(int(hold * 1000))},
                                      image=DEVELOPER)
        invited = self.operator("account", "invite", "--expires", "3600")
        self.assertEqual(invited.returncode, 0, invited.stderr.decode())
        codes = re.findall(rb"^[0-9a-f]{32}$", invited.stdout, re.M)
        self.assertEqual(len(codes), 1, invited.stdout)
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        context.check_hostname = False
        context.verify_mode = ssl.CERT_NONE

        def tls():
            raw = socket.create_connection(("127.0.0.1", tls_port), timeout=120)
            conn = context.wrap_socket(raw)
            stream = conn.makefile("rwb")
            self.assertTrue(stream.readline().startswith(b"200"))
            return conn, stream

        redeem_conn, redeem = tls()
        reader_conn, reader = self.connect()
        poster_conn, poster = self.connect()
        with redeem_conn, reader_conn, poster_conn:
            redeem.write(b"XREDEEM " + codes[0] + b" robin\r\n")
            redeem.flush()
            self.assertTrue(redeem.readline().startswith(b"381"))
            before = self.group_count(reader)
            self.begin_post(poster, b"redeem-barrier@example.invalid", b"held at the barrier\r\n")
            t0 = time.monotonic()
            time.sleep(0.5)
            redeem.write(b"XREDEEM PASS battery-staple-horse\r\n")
            redeem.flush()
            time.sleep(0.5)
            during = self.group_count(reader)
            during_at = time.monotonic() - t0
            redeemed = redeem.readline()
            redeemed_at = time.monotonic() - t0
            posted = poster.readline()
            posted_at = time.monotonic() - t0
            for stream in (redeem, reader, poster):
                stream.write(b"QUIT\r\n")
                stream.flush()
        login_conn, login = tls()
        with login_conn:
            login.write(b"AUTHINFO USER robin\r\n")
            login.flush()
            user = login.readline()
            login.write(b"AUTHINFO PASS battery-staple-horse\r\n")
            login.flush()
            authed = login.readline()
            login.write(b"QUIT\r\n")
            login.flush()
        print("redeem during a barrier (%.1fs): GROUP %d at %.3fs (before %d); 281 at %.3fs %r; "
              "240 at %.3fs; login %r %r"
              % (hold, during, during_at, before, redeemed_at, redeemed[:3], posted_at,
                 user[:3], authed[:3]))
        self.assertTrue(posted.startswith(b"240"), posted)
        self.assertTrue(redeemed.startswith(b"281"), redeemed)
        # The reader was served inside the barrier while the PASS waited.
        self.assertLess(during_at, hold - 0.5, during_at)
        self.assertEqual(during, before)
        # The publication waited for the batch's COMPLETE.
        self.assertGreaterEqual(redeemed_at, hold - 0.1, redeemed_at)
        self.assertTrue(user.startswith(b"381"), user)
        self.assertTrue(authed.startswith(b"281"), authed)

if __name__ == "__main__":
    unittest.main()

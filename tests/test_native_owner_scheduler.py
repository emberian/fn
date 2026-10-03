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
import re
import socket
import struct
import subprocess
import threading
import time
import unittest

from tests.native_harness import ROOT, Node, executable, free_port, native_image, requires

IMAGE = native_image("FN_NATIVE_HOST", "build/fn-host-developer")
# The developer image: the only one that honours a developer selector
# (FN_NATIVE_OWNER_TEST_BARRIER_MS); a production image refuses to start.
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")

CHECKPOINT_DONE = re.compile(rb"CHECKPOINT auto sequence=(\d+)")
SCHED_HEAD = re.compile(rb"^sched order=control,reader,poster,transit bound=(\d+) cursor=(\d+)$", re.M)
SCHED_ROW = re.compile(
    rb"^sched (control|reader|poster|transit) holds=(\d+) hold<1ms=(\d+) hold<10ms=(\d+) "
    rb"hold<100ms=(\d+) hold<1s=(\d+) hold>=1s=(\d+) hold-max-ms=(\d+) wait-max-ms=(\d+) waits>=1s=(\d+)$", re.M)


def stuffed(body):
    return b"".join((b"." + line if line.startswith(b".") else line) + b"\r\n"
                    for line in body.split(b"\r\n"))


class SchedulerSourceTests(unittest.TestCase):
    """What the source has to say, whether or not an image was built."""

    def test_every_owner_entry_is_gated_and_the_reply_leaves_the_mutex(self):
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text()
        serialized = owner[owner.index("(defun fnn-owner-serialized "):owner.index("(defun fnn-owner-consume-connection-fault")]
        self.assertIn("(fnn-owner-gated (service class)", serialized)
        # books/owner-time-model.lisp (lane time-model: fn-otm-next-is-ocp-next)
        # over books/owner-commit-pipeline.lisp (lane log-2) over
        # books/owner-commit-steps.lisp (PKT-688 (4) slice 2): the gate's pick
        # and fold are fn-ocp-next / fn-ocp-observe, which are fn-ocs-next's
        # (fn-ocp-next-is-ocs-next; fn-ocm-next's pick outside a batch,
        # fn-osch-next's for the four classes: PRF-267, PRF-248).
        self.assertIn("'fn-otm-next", owner)
        self.assertIn("'fn-otm-observe", owner)
        # The committer's pipeline: START (it seals) as a :commit quantum, the
        # SYNC in the syncer thread with the owner released, at most one
        # START-NEXT (not sealed) behind it, then COMPLETE as a :commit
        # quantum, which seals the next batch only after the replies.
        batch = owner[owner.index("(defun fnn-owner-commit-pipeline "):owner.index("(defun fnn-owner-committer-loop")]
        self.assertIn("'fn-otm-commit-event", owner)
        self.assertIn("'fn-otm-committer-wake", owner)
        self.assertLess(batch.index("(fnn-owner-commit-start-locked service)"),
                        batch.index("(fnn-owner-start-syncer service gen job)"))
        self.assertLess(batch.index("(fnn-owner-start-syncer service gen job)"),
                        batch.index("(fnn-owner-commit-start-locked service :seal nil)"))
        self.assertLess(batch.index("(sb-thread:join-thread syncer"),
                        batch.index("service :complete members deferred)"))
        self.assertLess(batch.index("service :complete members deferred)"),
                        batch.index("(fnn-log-seal-capture store)"))
        self.assertEqual(batch.count("(fnn-owner-start-syncer service gen job)"), 1)
        # Lane owner-offlock: the syncer runs the batch JOB (its phases are
        # ACL2's, books/owner-queued-work.lisp); the barrier is its :fence.
        syncer = owner[owner.index("(defun fnn-owner-batch-fence "):owner.index("(defun fnn-owner-batch-effect ")]
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


@requires(IMAGE)
class SchedulerNativeTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE)
        self.root, self.store, self.port = self.node.root, self.node.store_path, self.node.port
        self.config, self.control = self.node.config, self.node.control
        init = self.operator("init", "--max-article-octets", "1048576", "fn.test")
        self.assertEqual(init.returncode, 0, init.stderr.decode())
        self.owner = self.start_owner()

    def operator(self, *words, timeout=60):
        return self.node.operator(*words, timeout=timeout)

    def start_owner(self, extra=None, image=None):
        return self.node.start(image=image, env=extra)

    def reap(self, process):
        self.node.stop(expect=None, process=process)

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

    @unittest.skipUnless(executable(DEVELOPER), "no developer image at %s" % DEVELOPER)
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

    @unittest.skipUnless(executable(DEVELOPER), "no developer image at %s" % DEVELOPER)
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
        self.owner = self.start_owner({"FN_NATIVE_OWNER_TEST_BARRIER_MS": str(int(hold * 1000)),
                                       "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE": "1"},
                                      image=DEVELOPER)
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
        lines = self.owner.stderr.since(0)
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


    @unittest.skipUnless(executable(DEVELOPER), "no developer image at %s" % DEVELOPER)
    def test_a_control_request_is_admitted_under_sustained_post_load(self):
        # Lane durability-bugs (row I3; PKT-700/701's owner, scheduler-3's
        # finding; SCN-195, PRF-901).  Barrier held 1.5 s; four posters POST
        # back to back, so a member is always queued behind the batch in
        # flight.  Before the lane the committer prepared a next batch behind
        # every barrier (START-NEXT) and the COMPLETE sealed it, so a batch was
        # always in flight and a mutating control request (`group create',
        # the :control class, which flight shuts out) waited as long as the
        # POSTs kept coming.  Now a waiting control request stops the
        # pipeline (fn-ocp-wake BLOCKED): at most two more batches are sealed
        # (fn-ocf-control-waits-at-most-the-bound), so it is answered within
        # three barriers plus its own quantum, while the posters keep going.
        self.reap(self.owner)
        hold = 1.5
        self.owner = self.start_owner({"FN_NATIVE_OWNER_TEST_BARRIER_MS": str(int(hold * 1000)),
                                       "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE": "1"},
                                      image=DEVELOPER)
        stop = threading.Event()
        errors, accepted, deferred = [], [], []

        def poster(index):
            try:
                conn, stream = self.connect()
                with conn:
                    n = 0
                    while not stop.is_set():
                        stream.write(b"POST\r\n")
                        stream.flush()
                        line = stream.readline()
                        if line.startswith(b"440"):
                            # RFC 3977 6.3.1: posting not permitted now
                            # (the in-flight memory admission); try later.
                            deferred.append(line)
                            time.sleep(0.2)
                            continue
                        if not line.startswith(b"340"):
                            errors.append("poster %d: POST answered %r" % (index, line))
                            return
                        stream.write(b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                                     b"Subject: load\r\nMessage-ID: <load-%d-%d@example.invalid>"
                                     b"\r\n\r\nsustained\r\n.\r\n" % (index, n))
                        stream.flush()
                        line = stream.readline()
                        if not line.startswith(b"240"):
                            errors.append("poster %d: article answered %r" % (index, line))
                            return
                        accepted.append(time.monotonic())
                        n += 1
                    stream.write(b"QUIT\r\n")
                    stream.flush()
            except Exception as error:  # noqa: BLE001 -- reported below
                errors.append("poster %d: %r" % (index, error))

        threads = [threading.Thread(target=poster, args=(i,), daemon=True) for i in range(4)]
        for thread in threads:
            thread.start()
        try:
            # Let the pipeline fill: a batch in flight and one behind it.
            time.sleep(3 * hold)
            started = time.monotonic()
            created = self.operator("group", "create", "fn.fair", timeout=60)
            answered = time.monotonic() - started
            during = sum(1 for t in accepted if started <= t <= started + answered)
            time.sleep(2 * hold)
            after = sum(1 for t in accepted if t > started + answered)
        finally:
            stop.set()
            for thread in threads:
                thread.join(timeout=60)
        self.reap(self.owner)
        trace = [l for l in self.owner.stderr.since(0).splitlines() if b"pipeline" in l]
        print("pipeline trace (last 12): %r" % trace[-12:])
        print("control under sustained POST (barrier %.1fs): group create answered in %.3fs; "
              "POSTs accepted while it waited %d, in the next %.1fs %d; total %d; 440 deferrals %d"
              % (hold, answered, during, 2 * hold, after, len(accepted), len(deferred)))
        self.assertEqual(errors, [])
        self.assertEqual(created.returncode, 0, created.stderr.decode())
        # At most seven barriers by the keystone (the batch in flight, the
        # one open behind it, one START that was due, the pass budget's);
        # in practice two or three.  Before the lane: never, while POSTs came.
        self.assertLess(answered, 7 * hold + 3.0, answered)
        # The posters were never starved in turn: POSTs kept being accepted.
        self.assertGreater(after, 0)

    @unittest.skipUnless(executable(DEVELOPER), "no developer image at %s" % DEVELOPER)
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

    def peer_connect(self, source="127.0.0.9"):
        conn = socket.create_connection(("127.0.0.1", self.port), timeout=120,
                                        source_address=(source, 0))
        stream = conn.makefile("rwb")
        self.assertTrue(stream.readline().startswith(b"200"))
        return conn, stream

    def ask(self, stream, line):
        stream.write(line + b"\r\n")
        stream.flush()
        return stream.readline()

    @unittest.skipUnless(executable(DEVELOPER), "no developer image at %s" % DEVELOPER)
    def test_a_hostile_peer_racing_a_durable_completion_gets_no_second_copy(self):
        # Row A2 (composed boundary under a hostile peer; lane composed-owner-5).
        # A POST's batch is held at its barrier (4 s) while a configured peer
        # (source 127.0.0.9) OPENS its session and offers the same Message-ID
        # every way it can: IHAVE, CHECK, and a TAKETHIS carrying a DIFFERENT
        # body; a second peer session sends half a TAKETHIS and resets.  The
        # owner relation across both is owner-relation-2's
        # (books/owner-host-relation.lisp): the peer open keeps the Store and
        # the committed view (fn-ohr-open-peer-keeps-store-and-view,
        # fn-ohr-open-peer-preserves-ocl-relation) and the durable completion
        # keeps the relation over every connection, the peer's included
        # (fn-ohr-finish-synced-preserves-ocl-relation).  So: the peer is never
        # invited to send the in-flight id (no 335/238) and never told a copy
        # was taken (no 235/239); the reset costs the poster nothing (240);
        # after the COMPLETE the same peer session is told it is held (435,
        # 438); the article is the poster's, once, and stays so across a
        # restart.
        self.reap(self.owner)
        policy = self.operator("policy", "set", "path-identity", "fn-a2.example")
        self.assertEqual(policy.returncode, 0, policy.stderr.decode())
        added = self.operator("peer", "add", "hostile", "hostile.example", "127.0.0.1", "9",
                              "fn.*", "-", "127.0.0.9", "true")
        self.assertEqual(added.returncode, 0, added.stderr.decode())
        hold = 4.0
        self.owner = self.start_owner({"FN_NATIVE_OWNER_TEST_BARRIER_MS": str(int(hold * 1000))},
                                      image=DEVELOPER)
        msgid = b"a2-race@example.invalid"
        mid = b"<" + msgid + b">"
        poster_conn, poster = self.connect()
        reader_conn, reader = self.connect()
        with poster_conn, reader_conn:
            self.begin_post(poster, msgid, b"the poster's body")
            time.sleep(0.5)
            peer_conn, peer = self.peer_connect()
            with peer_conn:
                offered = self.ask(peer, b"IHAVE " + mid)
                self.assertTrue(offered[:3] in (b"435", b"436"), offered)
                self.assertTrue(self.ask(peer, b"MODE STREAM").startswith(b"203"))
                checked = self.ask(peer, b"CHECK " + mid)
                self.assertTrue(checked[:3] in (b"438", b"431"), checked)
                peer.write(b"TAKETHIS " + mid + b"\r\n"
                           b"Path: hostile.example!not-for-mail\r\nFrom: peer@example.invalid\r\n"
                           b"Newsgroups: fn.test\r\nSubject: a second copy\r\n"
                           b"Date: Mon, 28 Sep 2026 08:00:00 +0000\r\n"
                           b"Message-ID: " + mid + b"\r\n\r\nthe peer's body\r\n.\r\n")
                peer.flush()
                took = peer.readline()
                self.assertTrue(took[:3] in (b"439", b"436"), took)
                self.assertIn(mid, took)
                # A second peer session: half a TAKETHIS, then a reset.
                rst_conn, rst = self.peer_connect()
                self.assertTrue(self.ask(rst, b"MODE STREAM").startswith(b"203"))
                rst.write(b"TAKETHIS <a2-reset@example.invalid>\r\nPath: hostile.example\r\n"
                          b"Newsgroups: fn.test\r\n")
                rst.flush()
                rst_conn.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
                rst_conn.close()
                reply = poster.readline()
                self.assertTrue(reply.startswith(b"240"), reply)
                # After the COMPLETE the same peer session reads it as held.
                self.assertTrue(self.ask(peer, b"IHAVE " + mid).startswith(b"435"))
                self.assertTrue(self.ask(peer, b"CHECK " + mid).startswith(b"438"))
                self.ask(peer, b"QUIT")
            # The reader predates the post (its pinned view); a fresh one sees it.
            fresh_conn, fresh = self.connect()
            with fresh_conn:
                self.assertTrue(self.stat(fresh, msgid).startswith(b"223"))
                self.assertEqual(self.stat(fresh, b"a2-reset@example.invalid")[:3], b"430")
                fresh.write(b"QUIT\r\n")
                fresh.flush()
            for stream in (reader, poster):
                stream.write(b"QUIT\r\n")
                stream.flush()
        self.reap(self.owner)
        self.owner = self.start_owner()
        conn, stream = self.connect()
        with conn:
            self.assertEqual(self.group_count(stream), 1)
            stream.write(b"BODY " + mid + b"\r\n")
            stream.flush()
            self.assertTrue(stream.readline().startswith(b"222"))
            self.assertEqual(self.multiline(stream), b"the poster's body\r\n")
            stream.write(b"QUIT\r\n")
            stream.flush()

    def wait_stderr(self, process, pattern, deadline=180.0):
        end = time.monotonic() + deadline
        while time.monotonic() < end:
            match = pattern.search(process.stderr.since(0))
            if match:
                return match
            self.assertIsNone(process.poll(), "the owner exited while waiting")
            time.sleep(0.1)
        return None

    def article_body(self, stream, what):
        stream.write(b"BODY " + what + b"\r\n")
        stream.flush()
        status = stream.readline()
        if not status.startswith(b"222"):
            return status, None
        return status, self.multiline(stream)

    @unittest.skipUnless(executable(DEVELOPER), "no developer image at %s" % DEVELOPER)
    def test_the_a6_campaign_keeps_accepted_history_through_one_integrated_scenario(self):
        # Row A6, GPT-6's integrated campaign (planning/review-2026-09-28-gpt6.md),
        # in ONE scenario on the developer image: every completion delayed at
        # its barrier (0.6 s), the extent cache off (every payload read cold:
        # cache pressure), an OLD reader pinned before new writes, a snapshot
        # (the checkpoint publication, which reads the live arena off the
        # mutex under its generation pin, books/arena-reader-pins.lisp) racing
        # the old reader's reads, then a crash (SIGKILL) with one completion
        # still held at its barrier, and recovery.  Accepted history stays
        # accepted (every 240 is readable, byte for byte, after the crash); no
        # root loses a page (the old reader reads every article it pinned,
        # during the snapshot); the article whose completion the crash cut is
        # all there or not there -- never a damaged body.
        self.reap(self.owner)
        env = {"FN_NATIVE_OWNER_TEST_BARRIER_MS": "600", "FN_NATIVE_EXTENT_CACHE_TEST_OFF": "1"}
        self.owner = self.start_owner(env, image=DEVELOPER)
        bodies = {}

        def posted(i):
            return (b"campaign article %d\r\n" % i + b"line %d of a longer body\r\n" % i * 40)[:-2]

        def body_of(i):
            # what BODY answers: the posted lines, each CRLF-terminated
            return posted(i) + b"\r\n"

        conn, writer = self.connect()
        with conn:
            for i in range(1, 7):
                msgid = b"a6-%d@example.invalid" % i
                self.post(writer, msgid, posted(i))
                bodies[msgid] = body_of(i)
            old_conn, old = self.connect()
            with old_conn:
                self.assertEqual(self.group_count(old), 6)
                for i in range(7, 11):
                    msgid = b"a6-%d@example.invalid" % i
                    self.post(writer, msgid, posted(i))
                    bodies[msgid] = body_of(i)
                asked = self.operator("store", "checkpoint")
                self.assertEqual(asked.returncode, 0, asked.stderr.decode())
                # The old reader's pinned archive, read while the snapshot runs.
                for number in range(1, 7):
                    status, got = self.article_body(old, b"%d" % number)
                    self.assertTrue(status.startswith(b"222"), (number, status))
                    self.assertEqual(got, body_of(number), number)
                self.assertIsNotNone(self.wait_stderr(self.owner, CHECKPOINT_DONE),
                                     "the snapshot did not publish")
                for i in range(1, 7):
                    msgid = b"<a6-%d@example.invalid>" % i
                    self.assertEqual(self.article_body(old, msgid)[1], body_of(i), msgid)
                fresh_conn, fresh = self.connect()
                with fresh_conn:
                    self.assertEqual(self.group_count(fresh), 10)
                    for msgid, body in bodies.items():
                        self.assertEqual(self.article_body(fresh, b"<" + msgid + b">")[1], body, msgid)
            # A completion held at its barrier when the owner dies.
            cut = b"a6-cut@example.invalid"
            self.begin_post(writer, cut, posted(11))
            time.sleep(0.2)
            self.owner.kill()
        self.reap(self.owner)
        self.owner = self.start_owner()
        conn, stream = self.connect()
        with conn:
            count = self.group_count(stream)
            self.assertIn(count, (10, 11))
            for msgid, body in bodies.items():
                self.assertEqual(self.article_body(stream, b"<" + msgid + b">")[1], body, msgid)
            status, got = self.article_body(stream, b"<" + cut + b">")
            if count == 11:
                self.assertEqual(got, body_of(11))
            else:
                self.assertTrue(status.startswith(b"430"), status)
            stream.write(b"QUIT\r\n")
            stream.flush()

if __name__ == "__main__":
    unittest.main()

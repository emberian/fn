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
        self.assertIn("'fn-osch-next", owner)
        self.assertIn("'fn-osch-observe", owner)
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

    def start_owner(self):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, bufsize=0)
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


if __name__ == "__main__":
    unittest.main()

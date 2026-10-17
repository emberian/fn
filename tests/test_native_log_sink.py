"""The owner never waits on its log (PKT-508, PRF-187, SCN-116).

The owner used to write each service-log line under its log mutex from the
thread that decided it, under the owner mutex.  With stderr on a pipe nobody
reads, about 500 POSTs filled the pipe's 64 KiB, the write blocked, and the
whole node stopped answering, the control socket included
(planning/evidence/exposure-reply-size-2026-09-26.md section 4).  Now a line
is offered to a queue ACL2 admits or drops (books/log-sink.lisp
fn-log-sink-offer) and one writer thread drains it outside every owner lock.

The native case starts `operator CONFIG run' with stderr on a pipe this test
does not read, posts 2,000 articles over NNTP, and asks `health': every POST
is answered 240, `health' answers with its exit and the log-sink line shows
lines pending behind the full pipe.  Then it drains stderr and reads the sink
empty, every offered line written, and the owner stops cleanly on SIGTERM.
"""
import re
import subprocess
import threading
import time
import unittest

from tests.campaign import native_cuts
from tests.native_harness import ROOT, Node, article, native_image, requires, wait_for_announcement

IMAGE = native_image("FN_NATIVE_HOST")
POSTS = 2000
SINK = re.compile(rb"^log-sink pending=(\d+) dropped=(\d+) written=(\d+)$", re.M)


class LogSinkSourceTests(unittest.TestCase):
    """What the source has to say, whether or not an image was built."""

    def test_the_line_writer_offers_and_never_writes_under_the_queue_mutex(self):
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="utf-8")
        body = io[io.index("(defun fnn-log-offer "):io.index("(defun fnn-log-sink-snapshot")]
        self.assertIn("'fn-log-sink-offer", body)
        self.assertNotIn("fnn-write-all", body)
        self.assertNotIn("write-sequence", body)
        line = io[io.index("(defun fnn-log-line "):io.index("(defun fnn-exit ")]
        self.assertIn("(fnn-log-offer :log octets)", line)
        err = io[io.index("(defun fnn-err "):io.index("(defvar *fnn-owner-log-fd*")]
        self.assertIn("(fnn-log-offer :stderr", err)

    def test_the_owner_runs_the_writer_for_its_whole_service(self):
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="utf-8")
        run = owner[owner.index("(defun fnn-owner-run "):owner.index("(defun fnn-owner-run-normalized")]
        self.assertIn("(fnn-log-writer-start)", run)
        # The stop is the settlement's physical join, on both of the run's
        # exits (the settled stop and the unwind that claimed the run):
        # ACL2 decides from the join what happens to the pending lines.
        self.assertGreaterEqual(run.count("(setq log-close-action (fnn-owner-log-settlement))"), 2)
        settlement = native_cuts.host_function(owner, "fnn-owner-log-settlement")
        self.assertIn("(fnn-log-writer-stop)", settlement)
        self.assertIn("(fnn-core 'fn-ort-log-close-action observation", settlement)


@requires(IMAGE)
class LogSinkNativeTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE)
        self.node.init(timeout=60)

    def operator(self, *words, timeout=60):
        return self.node.operator(*words, timeout=timeout)

    def start_owner(self):
        # The subject: stderr is a pipe this test does not read until it
        # chooses to, so the harness's draining start is deliberately not used.
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.node.config), "run"],
            cwd=ROOT, env=self.node.environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0)
        self.addCleanup(self.reap, process)
        wait_for_announcement(process, b"LISTENING ")
        return process

    @staticmethod
    def reap(process):
        if process.poll() is None:
            process.kill()
            process.wait(timeout=10)
        for stream in (process.stdout, process.stderr):
            stream.close()

    def post_many(self, count):
        replies = []
        with self.node.session() as client:
            for n in range(count):
                first, final = client.post(article(
                    "<log-sink-%d@example.invalid>" % n, subject="an undrained log",
                    date=None))
                self.assertTrue(first.startswith(b"340"), first)
                replies.append(final.rstrip(b"\r\n"))
        return replies

    def sink(self):
        health = self.operator("health")
        found = SINK.search(health.stdout)
        self.assertIsNotNone(found, health.stdout.decode("ascii", "replace"))
        self.assertTrue(health.stdout.startswith(b"health exit="), health.stdout)
        return health, tuple(int(g) for g in found.groups())

    def test_an_unread_stderr_does_not_stop_the_node(self):
        owner = self.start_owner()
        replies = self.post_many(POSTS)
        self.assertEqual(len(replies), POSTS)
        self.assertEqual(set(replies), {b"240 article received OK"})
        # The control socket answers with the pipe full.
        health, (pending, dropped, written) = self.sink()
        first = health.stdout.split(b"\n", 1)[0]
        self.assertEqual(health.returncode, int(first[len(b"health exit="):][:2]),
                         health.stdout.decode())
        print("under the unread pipe: log-sink pending={} dropped={} written={}".format(
            pending, dropped, written))
        self.assertGreater(pending, 0, "the writer was not behind the unread pipe")
        self.assertGreaterEqual(pending + dropped + written, POSTS)

        # Read stderr now: the writer drains, and nothing was lost.
        lines = []
        reader = threading.Thread(
            target=lambda: lines.extend(owner.stderr), daemon=True)
        reader.start()
        deadline = time.monotonic() + 30
        while True:
            _, (pending, dropped, written) = self.sink()
            if pending == 0 or time.monotonic() > deadline:
                break
            time.sleep(0.2)
        print("after draining: log-sink pending={} dropped={} written={}".format(
            pending, dropped, written))
        self.assertEqual(pending, 0)
        self.assertEqual(dropped, 0)
        self.assertGreaterEqual(written, POSTS)

        owner.terminate()
        self.assertEqual(owner.wait(timeout=60), 0)
        reader.join(timeout=10)
        # `written' counts every item the one writer wrote: stderr lines and
        # the decision journal's entries (STORE/decisions/decisions.fnj,
        # destination :journal since PKT-872), one line each.  Lines the
        # owner wrote before its writer started reach stderr uncounted.
        journal = self.node.store_path / "decisions" / "decisions.fnj"
        entries = journal.read_bytes().count(b"\n") if journal.exists() else 0
        print("stderr lines={} journal entries={} written={}".format(
            len(lines), entries, written))
        self.assertGreaterEqual(len(lines) + entries, written)
        self.assertGreaterEqual(len(lines), POSTS)


if __name__ == "__main__":
    unittest.main()

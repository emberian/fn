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


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
POSTS = 2000
SINK = re.compile(rb"^log-sink pending=(\d+) dropped=(\d+) written=(\d+)$", re.M)


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
        self.assertIn("(fnn-log-writer-stop)", run)


@unittest.skipUnless(executable(IMAGE), "build/fn-host is required (FN_NATIVE_HOST)")
class LogSinkNativeTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="fn-log-sink-")
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
        init = self.operator("init", "fn.test")
        self.assertEqual(init.returncode, 0, init.stderr.decode())

    def operator(self, *words, timeout=60):
        return subprocess.run(
            [str(IMAGE), "--fn", "operator", str(self.config), *words],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False)

    def start_owner(self):
        # stderr is a pipe this test does not read until it chooses to.
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0)
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
            process.send_signal(signal.SIGKILL)
            process.wait(timeout=10)
        for stream in (process.stdout, process.stderr):
            if stream and not stream.closed:
                stream.close()

    def post_many(self, count):
        replies = []
        with socket.create_connection(("127.0.0.1", self.port), timeout=60) as conn:
            stream = conn.makefile("rwb")
            self.assertTrue(stream.readline().startswith(b"200"))
            for n in range(count):
                stream.write(b"POST\r\n")
                stream.flush()
                self.assertTrue(stream.readline().startswith(b"340"))
                stream.write(b"From: author@example.invalid\r\n"
                             b"Newsgroups: fn.test\r\n"
                             b"Subject: an undrained log\r\n"
                             b"Message-ID: <log-sink-%d@example.invalid>\r\n"
                             b"\r\nbody\r\n.\r\n" % n)
                stream.flush()
                replies.append(stream.readline().rstrip(b"\r\n"))
            stream.write(b"QUIT\r\n")
            stream.flush()
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
        self.assertEqual(pending, 0)
        self.assertEqual(dropped, 0)
        self.assertGreaterEqual(written, POSTS)

        owner.send_signal(signal.SIGTERM)
        self.assertEqual(owner.wait(timeout=60), 0)
        reader.join(timeout=10)
        self.assertGreaterEqual(len(lines), written)


if __name__ == "__main__":
    unittest.main()

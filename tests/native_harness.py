"""One way for a test or gate to start a native node: drained from birth, stopped by PID.

A native node logs to stdout and stderr for as long as it serves.  A test
that starts it with `stdout=PIPE, stderr=PIPE` and reads only the readiness
line leaves both pipes to fill: past the kernel's 64 KiB the node's next log
write blocks, in the owner while it holds its log mutex (PKT-505), so a long
test wedges the server it is measuring (feed-queue, 2026-09-28: the peering
harness stopped a node past ~1,000 transits and cleanup timed out).  A
harness that can block its subject can mask a bug or cause one.

`start(argv, ...)` returns a `NativeProcess` whose two pipes are read from
the moment it exists by one thread each, into a bounded buffer per stream
(`limit` bytes, the oldest dropped first and counted), so the node never
blocks on its log and a failure can still print what it said last.
`announcement(prefix)` waits for a stdout line under one deadline and, on
failure, stops the node and raises with both tails -- an owner that refuses
to start says why on stderr, and that reason is now in the failure
(feed-queue's first ask).  `stop()` signals the PID (SIGTERM, then SIGKILL
after `grace` seconds), reaps it, joins the readers and closes the pipes; it
is idempotent and returns the exit status.

This is the draining start and the PID stop only.  The wider harness (store
init, peered pairs, NNTP sessions, outcome names) is lane python-diet's T2
(planning/python-diet-2026-09-28.md, "MERGE (T2): one native harness").
"""
import os
import signal
import subprocess
import threading
import time

DEFAULT_LIMIT = 4 * 1024 * 1024
TAIL_BYTES = 8192


class Drain:
    """One pipe, read to EOF on a thread into a bounded buffer.

    `data` holds the last `limit` bytes; `dropped` counts the bytes before
    them, so an absolute offset (a cursor) stays meaningful after trimming.
    """

    def __init__(self, pipe, limit=DEFAULT_LIMIT, name="stream"):
        self.pipe = pipe
        self.limit = limit
        self.data = bytearray()
        self.dropped = 0
        self.closed = False
        self.condition = threading.Condition()
        self.thread = threading.Thread(target=self._run, name="drain-" + name,
                                       daemon=True)
        self.thread.start()

    def _run(self):
        descriptor = self.pipe.fileno()
        while True:
            try:
                chunk = os.read(descriptor, 65536)
            except OSError:
                chunk = b""
            with self.condition:
                if not chunk:
                    self.closed = True
                    self.condition.notify_all()
                    return
                self.data += chunk
                excess = len(self.data) - self.limit
                if excess > 0:
                    del self.data[:excess]
                    self.dropped += excess
                self.condition.notify_all()

    @property
    def end(self):
        with self.condition:
            return self.dropped + len(self.data)

    def since(self, offset):
        """The retained bytes from absolute OFFSET on (from the oldest kept
        byte when OFFSET was trimmed away)."""
        with self.condition:
            start = max(0, offset - self.dropped)
            return bytes(self.data[start:])

    def tail(self, count=TAIL_BYTES):
        with self.condition:
            prefix = b"[... %d bytes not kept] " % self.dropped if self.dropped else b""
            return prefix + bytes(self.data[-count:])

    def wait_for(self, predicate, offset, deadline):
        """Wait until PREDICATE(bytes since OFFSET) returns an end offset
        (relative to OFFSET) or the stream closes or DEADLINE passes.
        Returns (text, end) or (text, None)."""
        with self.condition:
            while True:
                start = max(0, offset - self.dropped)
                text = bytes(self.data[start:])
                found = predicate(text)
                if found is not None:
                    return text[:found], self.dropped + start + found
                remaining = deadline - time.monotonic()
                if self.closed or remaining <= 0:
                    return text, None
                self.condition.wait(min(remaining, 0.5))

    def join(self, timeout=10):
        self.thread.join(timeout)


def _line_starting(prefix):
    def find(text):
        position = 0
        while True:
            newline = text.find(b"\n", position)
            if newline < 0:
                return None
            if text.startswith(prefix, position):
                return newline + 1
            position = newline + 1
    return find


def _line_containing(marker):
    def find(text):
        at = text.find(marker)
        if at < 0:
            return None
        newline = text.find(b"\n", at)
        return None if newline < 0 else newline + 1
    return find


class NativeProcess:
    """A started node: the Popen, its two drains, a stdout cursor."""

    def __init__(self, process, limit=DEFAULT_LIMIT):
        self.process = process
        self.pid = process.pid
        self.stdout = Drain(process.stdout, limit, "stdout")
        self.stderr = Drain(process.stderr, limit, "stderr")
        self.cursor = 0
        self.stopped = False

    # The subset of Popen a test reads.
    def poll(self):
        return self.process.poll()

    @property
    def returncode(self):
        return self.process.returncode

    def wait(self, timeout=None):
        return self.process.wait(timeout=timeout)

    def signal(self, number):
        """Signal the PID unless it has been reaped (a reaped PID can be reused)."""
        if self.process.poll() is None:
            try:
                os.kill(self.pid, number)
            except ProcessLookupError:
                pass

    def terminate(self):
        self.signal(signal.SIGTERM)

    def kill(self):
        self.signal(signal.SIGKILL)

    def stop(self, grace=30, kill_wait=15):
        """SIGTERM, wait GRACE seconds, SIGKILL, reap; join the readers and
        close the pipes.  Idempotent; returns the exit status."""
        if not self.stopped:
            self.terminate()
            try:
                self.process.wait(timeout=grace)
            except subprocess.TimeoutExpired:
                self.kill()
                self.process.wait(timeout=kill_wait)
            self.finish()
        return self.process.returncode

    def finish(self):
        """After the process is reaped: let the readers reach EOF, close."""
        if self.stopped:
            return
        self.stopped = True
        for drain in (self.stdout, self.stderr):
            drain.join()
            try:
                drain.pipe.close()
            except OSError:
                pass

    def diagnostics(self):
        status = self.process.poll()
        return "exit={}; stdout tail={!r}; stderr tail={}".format(
            status, self.stdout.tail(),
            self.stderr.tail().decode("utf-8", "replace"))

    def fail(self, reason):
        """Stop the node and raise with both tails."""
        self.stop(grace=10)
        raise AssertionError("{}; {}".format(reason, self.diagnostics()))

    def announcement(self, prefix, timeout=180):
        """The first stdout line (from the cursor) that starts with PREFIX,
        advancing the cursor past it; on a deadline or an exit, `fail`."""
        text, end = self.stdout.wait_for(_line_starting(prefix), self.cursor,
                                         time.monotonic() + timeout)
        if end is None:
            self.fail("native announcement {!r} not seen within {} s".format(prefix, timeout))
        self.cursor = end
        line_start = text.rfind(b"\n", 0, len(text) - 1) + 1
        return text[line_start:]

    def output_until(self, marker, timeout=45):
        """Stdout from the cursor through the line containing MARKER,
        advancing the cursor; on a deadline or an exit, `fail`."""
        text, end = self.stdout.wait_for(_line_containing(marker), self.cursor,
                                         time.monotonic() + timeout)
        if end is None:
            self.fail("native marker {!r} absent after {} s".format(marker, timeout))
        self.cursor = end
        return text

    def communicate(self, timeout=None):
        """Popen.communicate for a drained process: wait for it to exit on its
        own (TimeoutExpired as Popen raises it, the process left running),
        then (stdout the cursor has not passed, the retained stderr)."""
        self.process.wait(timeout=timeout)
        self.finish()
        return self.output_since_cursor(), self.stderr.since(0)

    def output_since_cursor(self):
        """Stdout the cursor has not passed (call after `stop` for all of it)."""
        text = self.stdout.since(self.cursor)
        self.cursor = self.stdout.end
        return text


def start(argv, *, limit=DEFAULT_LIMIT, **popen):
    """Start ARGV with both pipes drained from birth (see the module doc)."""
    popen.setdefault("bufsize", 0)
    process = subprocess.Popen([str(word) for word in argv], stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, **popen)
    return NativeProcess(process, limit=limit)

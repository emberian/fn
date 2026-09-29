"""The one way a native test or gate starts, talks to and stops a node.

Four layers, each usable alone (planning/python-diet-2026-09-28.md, T2):

* Processes.  `start(argv)` returns a `NativeProcess` whose stdout and
  stderr are read from birth by one thread each into bounded buffers, so a
  node never blocks on its own log (PKT-505: a pipe nobody reads fills at
  64 KiB and the owner's next log write blocks while it holds its log
  mutex).  `announcement(prefix)` waits under one deadline and on failure
  stops the node and raises with both tails, stderr's refusal lines first
  (feed-queue: an owner refusal visible only on stderr).  `stop()` signals
  the PID (SIGTERM, then SIGKILL) and reaps; idempotent.  The Popen-shaped
  helpers the older modules used (`wait_for_announcement`,
  `stop_and_diagnostics`, `start_filed`) are kept for the modules not yet
  on `Node`.

* Outcomes.  `EXIT` is ACL2's code table, read from
  books/outcome-class.lisp `*fn-outcome-codes*` (the table the image's
  `+fnn-exit-*+` constants are built from, host/native/io.lisp), never
  written out by hand here; `assert_outcome(case, result, EXIT.UNCERTAIN)`
  names the class it wanted and the one it got, and never collapses
  uncertain into refused.

* Nodes.  `Node(case, image)` is one scratch tree (fn.toml, store, control
  socket, a free loopback port) and the verbs a test runs on it:
  `operator(...)`, `store(...)`, `init(...)`, `start()` (the owner, drained,
  ready on its `LISTENING PORT` line, stopped at cleanup), `stop(expect)`,
  `post(...)`, `session()`, `log_on_failure()`.  The environment is the
  deployed control stack by default (`deployed_stack`, PKT-876).  A cut
  point is `start(env={"FN_NATIVE_CONTROL_FAULT": cut})` on the developer
  image, and `died_at(cut)` asserts the owner stopped there.

* Clients.  `Client` is one NNTP connection over octets (plain, STARTTLS or
  implicit TLS, bounded reads), and `article(...)` builds a test article.

`native_image(NAME)`, NAME a literal, is how a module names the image it
tests; tools/native_env.py reads those calls as the module's own reads, so
hbox_native.sh still refuses a module whose image the run did not build.
The ACL2 printed-value parsers (`acl2_result`, `acl2_octets`, ...) are
here so no native module imports tools/run_store.py for them.
"""
import contextlib
import os
from pathlib import Path
import re
import signal
import socket
import ssl
import subprocess
import tempfile
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
                excess = 0 if self.limit is None else len(self.data) - self.limit
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

    def next_line(self, timeout=60):
        """The next stdout line after the cursor (a developer cut's marker),
        advancing the cursor; on a deadline or an exit, `fail`."""
        def first(text):
            at = text.find(b"\n")
            return None if at < 0 else at + 1
        text, end = self.stdout.wait_for(first, self.cursor, time.monotonic() + timeout)
        if end is None:
            self.fail("no stdout line within {} s".format(timeout))
        self.cursor = end
        return text

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
        then (stdout the cursor has not passed, the retained stderr).  A
        stream that outgrew its limit fails here, never returns truncated:
        start a process whose whole output is read with `limit=None`."""
        self.process.wait(timeout=timeout)
        self.finish()
        for drain in (self.stdout, self.stderr):
            if drain.dropped:
                raise AssertionError("{}: {} octets past the {}-octet limit were not kept; "
                                     "start it with limit=None".format(
                                         drain.thread.name, drain.dropped, drain.limit))
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
    native = NativeProcess(process, limit=limit)
    _register(argv, native)
    return native


# --- Stderr of a failed test ---------------------------------------------------
#
# Every process `start` or `start_filed` begins is recorded under the test
# that started it.  When that test fails, tools/test_budget.py (the runner
# hbox_native uses) prints each process's stderr digest after the failure
# and writes the whole stderr to $FN_NATIVE_STDERR_DIR/<test>-<n>-<label>.stderr:
# the owner's reason for refusing was on a stderr deleted with the test's
# temporary directory (entry-guards-2, feed-queue, 2026-09-28/29).  A
# passing test's records are dropped.

_STARTED = {}


def current_test_id():
    """The id of the unittest.TestCase whose method is on the stack, or None."""
    import sys
    import unittest
    frame = sys._getframe(1)
    while frame is not None:
        candidate = frame.f_locals.get("self")
        if isinstance(candidate, unittest.TestCase):
            return candidate.id()
        frame = frame.f_back
    return None


def _register(argv, process, path=None):
    test = current_test_id()
    if test is None:
        return
    words = [str(word) for word in argv]
    label = "-".join([Path(words[0]).name] + [w.lstrip("-") for w in words[1:3]
                                              if not w.startswith("/")])
    # A file log is read through a handle of our own: the test's cleanup
    # may delete the file (its temporary directory) before the failure is
    # reported, and an open handle keeps the bytes.
    handle = None
    if path is not None:
        try:
            handle = open(path, "rb")
        except OSError:
            handle = None
    if test not in _STARTED:
        # Tests run one at a time in a process: another test's records are
        # from a test that has ended (a runner other than test_budget's
        # never forgets them), so at most one test's processes are held.
        for other in list(_STARTED):
            forget(other)
    _STARTED.setdefault(test, []).append((re.sub(r"[^A-Za-z0-9._-]", "_", label),
                                          process, handle))


def _stderr_bytes(process, handle):
    if isinstance(process, NativeProcess):
        return process.stderr.since(0)
    if handle is not None:
        try:
            handle.seek(0)
            return handle.read()
        except (OSError, ValueError):
            pass
    return b""


def failure_stderr(test, keep=None):
    """Each process TEST started: its label, exit and stderr digest; the whole
    stderr written under KEEP when given.  Empty when it started none."""
    parts = []
    for number, (label, process, handle) in enumerate(_STARTED.get(test, ()), 1):
        text = _stderr_bytes(process, handle)
        where = ""
        if keep:
            directory = Path(keep)
            directory.mkdir(parents=True, exist_ok=True)
            path = directory / "{}-{}-{}.stderr".format(
                ".".join(test.split(".")[-2:]), number, label)
            path.write_bytes(text)
            where = " (kept: {})".format(path)
        parts.append("-- {} process {} [{}] exit={}{}\n{}".format(
            test, number, label, process.poll(), where, stderr_digest(text)))
    return "\n".join(parts)


def forget(test):
    for _, _, handle in _STARTED.pop(test, ()):
        if handle is not None:
            handle.close()


def stop_and_diagnostics(process, timeout=10, stderr_path=None):
    """Stop before collecting pipes; an idle live server will not close stderr.

    The answer names the exit status, and says where stderr went when the
    caller did not pipe it: an empty `stderr=' from a process whose stderr
    was a file read as a silent failure (lane ops-fixes, 2026-09-27: the
    owner had refused by name, into a file the harness then removed).
    STDERR_PATH is that file, whose tail is included."""
    exited = process.poll()
    if exited is None:
        process.terminate()
    try:
        _, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        _, stderr = process.communicate(timeout=timeout)
    status = ("exit={}".format(exited) if exited is not None
              else "stopped by the harness (exit={})".format(process.returncode))
    if process.stderr is None and stderr_path is None:
        return "{} (not piped: the caller redirected stderr)".format(status)
    text = (stderr or b"")
    if stderr_path is not None:
        try:
            with open(stderr_path, "rb") as handle:
                text += handle.read()
        except OSError as error:
            text += "(cannot read {}: {})".format(stderr_path, error).encode()
    return "{} {}".format(status, stderr_digest(text))


# The tail of stderr kept in a startup diagnostic, and how many of its
# refusal lines are quoted first.
STDERR_TAIL = 8192
REFUSAL_LINES = 8


def stderr_digest(text):
    """STDERR (octets) as a diagnostic: every `refused' line first, then the tail.

    A start refused for memory (lane ops-fixes) prints its refusal and then
    the parts that do not fit; a long enough breakdown pushed the one line
    that says why (`fn: refused init-budget-cannot-hold-profile ...',
    `machine-cannot-hold-profile') out of the kept tail, and a lane read the
    failure as a silent one (feed-queue, 2026-09-27).  The refusal lines are
    read from the whole of stderr, whatever its length."""
    decoded = (text or b"").decode("utf-8", "replace")
    refusals = [line.strip() for line in decoded.splitlines()
                if " refused " in " {} ".format(line) or line.startswith("refused ")]
    parts = []
    if refusals:
        parts.append("refused lines ({}): {}".format(
            len(refusals), " | ".join(refusals[:REFUSAL_LINES])))
    size = len(text or b"")
    if size > STDERR_TAIL:
        parts.append("stderr (last {} of {} octets):\n{}".format(
            STDERR_TAIL, size, decoded[-STDERR_TAIL:]))
    else:
        parts.append("stderr:\n{}".format(decoded))
    return "\n".join(parts)


def node_log_digest(log_path):
    """The node's log at LOG_PATH as a diagnostic: the lines that name an
    uncertain outcome or a fault first (the owner writes one for every
    uncertain answer it gives: host/native/owner.lisp
    fnn-owner-attempt-handlers, fnn-owner-commit-complete-locked), then
    stderr_digest's refusals and tail."""
    try:
        with open(log_path, "rb") as handle:
            text = handle.read()
    except OSError as error:
        return "(cannot read the node's log {}: {})".format(log_path, error)
    decoded = text.decode("utf-8", "replace")
    reasons = [line.strip() for line in decoded.splitlines()
               if "uncertain" in line or " fault" in line]
    head = ("uncertain/fault lines ({}): {}\n".format(len(reasons), " | ".join(reasons[:REFUSAL_LINES]))
            if reasons else "")
    return head + stderr_digest(text)


@contextlib.contextmanager
def node_log_on_failure(log_path):
    """Attach the node's log to any assertion that fails inside the block;
    LOG_PATH is a file or a NativeProcess (its retained stderr).

    A reply assertion that fails says what the client saw; why the node
    answered so is in its log, which a test's temporary tree removes with
    the test (lane full-vs-uncertain, 2026-09-28: a `441 ... uncertain' seen
    once at a full store left no evidence of its reason).  Wrap every block
    that asserts a node's replies:

        with node_log_on_failure(self.tmp / "owner.log"):
            self.assertEqual(reply, expected)
    """
    try:
        yield
    except AssertionError as error:
        raise AssertionError("{}\n--- the node's log ({}) ---\n{}".format(
            error, getattr(log_path, "pid", log_path), _log_digest(log_path))) from None


def wait_for_announcement(process, prefix, timeout=180, max_bytes=8192, stderr_path=None):
    """Read bounded startup lines under one deadline, including CONTROL first.

    Read the descriptor directly so select does not overlook a second line
    already buffered by Python's BufferedReader.
    """
    import os
    import select
    import time
    deadline = time.monotonic() + timeout
    buffered = b""
    observed = b""
    try:
        while len(observed) < max_bytes:
            while b"\n" in buffered:
                line, buffered = buffered.split(b"\n", 1)
                line += b"\n"
                if line.startswith(prefix):
                    return line
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not select.select([process.stdout], [], [], remaining)[0]:
                raise AssertionError("native startup deadline expired")
            chunk = os.read(process.stdout.fileno(), min(4096, max_bytes - len(observed)))
            if not chunk:
                raise AssertionError("native startup ended before announcement")
            observed += chunk
            buffered += chunk
        raise AssertionError("native startup output exceeded byte bound")
    except (AssertionError, OSError) as error:
        # stderr first and on its own lines: it is where the node says why
        # it did not start (feed-queue's ask, 2026-09-27).
        diagnostic = stop_and_diagnostics(process, stderr_path=stderr_path)
        raise AssertionError("{}; process {}\nstdout={!r}".format(
            error, diagnostic, observed)) from error


def runtime_sbcl(image):
    """The SBCL that runs IMAGE, as (executable, environment), or None.

    A raw-stub test reads host/native/*.lisp with the reader of the runtime it
    ships on: the host code names symbols (sb-bsd-sockets:sockopt-error) that
    an older system SBCL does not export.  FN_SBCL overrides; otherwise the
    runtime named by IMAGE's wrapper (a build/fn-host* script or a frozen
    image directory's runtime/sbcl); otherwise `sbcl` on PATH.
    """
    import os
    import re
    import shutil
    from pathlib import Path
    env = dict(os.environ)
    if env.get("FN_SBCL"):
        return env["FN_SBCL"], env
    image = Path(image)
    frozen = image.parent / "runtime" / "sbcl"
    if os.access(frozen, os.X_OK):
        env["SBCL_HOME"] = str(image.parent / "runtime" / "sbcl-home") + "/"
        return str(frozen), env
    try:
        wrapper = image.read_text(encoding="utf-8", errors="replace")
    except OSError:
        wrapper = ""
    runtime = re.search(r'^exec "([^"$]+)" ', wrapper, re.M)
    home = re.search(r"^export SBCL_HOME='([^']+)'", wrapper, re.M)
    if runtime and os.access(runtime.group(1), os.X_OK):
        if home:
            env["SBCL_HOME"] = home.group(1)
        return runtime.group(1), env
    found = shutil.which("sbcl")
    return (found, env) if found else None


class AcceptThenClosePeer:
    """A loopback peer that accepts each connection and closes it at once.

    The outage a contact meets after its connection exists: a socket was
    produced, no transfer completed, so the host reads the transfer
    `:uncertain` (host/native/bp-service.lisp, specs/bp-node-machine.md
    "any failure after the connection exists stays `:uncertain`").  A port
    with nothing listening is the other outage, a connect that never
    produced a socket, which reads `:failed`; see `refused_port`.
    `accepted` counts the connections, so a test can assert that the outage
    it staged is the one it meant.
    """

    def __init__(self):
        import socket
        import threading
        self.listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(16)
        self.listener.settimeout(0.2)
        self.port = self.listener.getsockname()[1]
        self.accepted = 0
        self._stopped = threading.Event()
        self._thread = threading.Thread(target=self._serve, daemon=True)
        self._thread.start()

    def _serve(self):
        import socket
        while not self._stopped.is_set():
            try:
                connection, _ = self.listener.accept()
            except socket.timeout:
                continue
            except OSError:
                return
            self.accepted += 1
            connection.close()

    def close(self):
        self._stopped.set()
        self._thread.join(timeout=5)
        self.listener.close()


def refused_port():
    """A loopback socket bound and never listening, and its port.

    Connecting to it is refused (no socket is produced) for as long as the
    caller holds the socket open, and no other process can take the port.
    """
    import socket
    reservation = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    reservation.bind(("127.0.0.1", 0))
    return reservation, reservation.getsockname()[1]


def start_filed(argv, log_path, **popen):
    """Start a native process with stdout on a pipe and stderr in LOG_PATH.

    A native server logs to stderr for as long as it serves.  On a pipe the
    test does not read, the 64 KiB kernel buffer fills and the server's next
    log write blocks, in the owner while it holds its log mutex (PKT-505), so
    a long test wedges the server it is measuring.  A file never fills.  The
    returned process's `stderr' is a read handle on LOG_PATH (reading it after
    the process stops yields the whole log, as the pipe did) and
    `stderr_path' names the file.
    """
    with open(log_path, "wb") as log:
        process = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=log,
                                   bufsize=0, **popen)
    process.stderr = open(log_path, "rb")
    process.stderr_path = log_path
    _register(argv, process, log_path)
    return process


def next_log_number(case):
    """1, 2, ... per test case: one stderr file per process a test starts."""
    case.native_log_count = getattr(case, "native_log_count", 0) + 1
    return case.native_log_count


def native_peer_add(image, store, words, env, cwd):
    """`operator CONFIG peer add WORDS...` on STORE with no owner running (the
    offline configuration record, books/native-operator.lisp's grammar: NAME
    PATH HOST PORT INBOUND|- OUTBOUND|- SOURCE-ADDRESS STREAMING).  The
    format-9 store is read by the image, not by tools/run_store.py (which
    reads only the per-file layout).  CONFIG is a scratch fn.toml beside
    STORE naming only it.  Returns the CompletedProcess."""
    from pathlib import Path
    config = Path(store).parent / (Path(store).name + "-peer.toml")
    config.write_text('[store]\npath = "{}"\n'.format(store), encoding="ascii")
    return subprocess.run([str(image), "--fn", "operator", str(config), "peer", "add", *words],
                          cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          env=env, timeout=180, check=False)


# --- Outcomes ---------------------------------------------------------------

ROOT = Path(__file__).resolve().parent.parent
from tools.outcome_codes import (  # noqa: E402,F401  (re-exported: the one table, read from ACL2's book)
    EXIT, EXIT_FAULT, EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, EXIT_USAGE, OUTCOME_BOOK,
    outcome_codes, outcome_name)


def _text(octets):
    if isinstance(octets, bytes):
        return octets.decode("utf-8", "replace")
    return "" if octets is None else str(octets)


def assert_outcome(case, result, expected, *, log=None):
    """RESULT (a CompletedProcess or a status) exited EXPECTED.

    The message names both classes and carries stdout and stderr, and LOG's
    digest when LOG (a path or a NativeProcess) is given; uncertain is never
    accepted where refused was asked for, or the reverse."""
    status = getattr(result, "returncode", result)
    if status == expected:
        return result
    detail = ""
    if hasattr(result, "returncode"):
        detail = "\nstdout={}\nstderr={}".format(
            _text(result.stdout)[-8192:], stderr_digest(result.stderr or b""))
    if log is not None:
        detail += "\n--- the node's log ---\n" + _log_digest(log)
    case.fail("expected {} ({}), got {} ({}){}".format(
        outcome_name(expected), int(expected), outcome_name(status), status, detail))


# --- ACL2 printed values (moved from tools/run_store.py) -------------------

class Acl2ValueError(ValueError):
    pass


ACL2_PROMPT = b"ACL2 !>"  # tools/run_store.py PROMPT, the bridge session's prompt
ARENA_RESULT_PREFIX = b"(NIL "
ARENA_RESULT_SUFFIX = b" <fn-arena> <state>)"


def acl2_result(output, prompt=ACL2_PROMPT):
    """The printed value of one bridge call (the text before the prompt).  An
    entry that seals into the payload arena prints `(NIL VALUE <fn-arena>
    <state>)`; its VALUE is the answer, and a non-nil error flag is left for
    the value's parser to refuse."""
    data = output.strip()
    if not data.endswith(prompt):
        raise Acl2ValueError("unexpected ACL2 bridge result")
    body = data[:-len(prompt)].strip()
    if (body.upper().startswith(ARENA_RESULT_PREFIX)
            and body.lower().endswith(ARENA_RESULT_SUFFIX)):
        body = body[len(ARENA_RESULT_PREFIX):-len(ARENA_RESULT_SUFFIX)].strip()
    return body


def acl2_octets(output):
    """A printed list of octets, in linear time (no backtracking pattern)."""
    body = acl2_result(output)
    if body == b"NIL":
        return b""
    if len(body) < 2 or body[:1] != b"(" or body[-1:] != b")":
        raise Acl2ValueError("ACL2 returned a non-octet result")
    values = []
    for token in body[1:-1].split():
        if not token.isdigit() or int(token) > 255:
            raise Acl2ValueError("ACL2 returned a non-octet")
        values.append(int(token))
    return bytes(values)


def acl2_nat(output):
    body = acl2_result(output)
    if not re.fullmatch(rb"[0-9]+", body):
        raise Acl2ValueError("ACL2 returned a non-natural")
    return int(body)


def acl2_boolean(output):
    body = acl2_result(output).upper()
    if body in (b"T", b"NIL"):
        return body == b"T"
    raise Acl2ValueError("ACL2 returned a non-boolean")


def acl2_keyword(output):
    body = acl2_result(output).upper()
    if not re.fullmatch(rb":[A-Z0-9-]+", body):
        raise Acl2ValueError("ACL2 returned a non-keyword: {!r}".format(body))
    return body.decode("ascii").lower()[1:]


# --- The image's own ACL2 session ------------------------------------------

ACL2_SESSION_PROMPT = re.compile(rb"ACL2 [a-z]*!?>+\s*\Z")


class Acl2Session:
    """`fn acl2 session` of a developer image (host/native/acl2-session.lisp):
    ACL2's loop over the image's own certified world, for the fixtures only
    ACL2 may compute (a content identity, a BP request, bundle or fragment a
    scripted peer sends, a staged store frame).  `call(form)` returns what
    ACL2 printed up to and including its prompt, the shape `acl2_result`
    and its siblings parse.  It replaces the retired Python host's bridge
    session (tools/run_store.py Acl2Store): no second ACL2, no books to
    include, and nothing here computes a value ACL2 owns."""

    def __init__(self, image=None, *, timeout=120):
        if image is None:
            image = native_image("FN_NATIVE_DEVELOPER_HOST")
            if not executable(image):
                image = native_image("FN_NATIVE_DTN_DEVELOPER_HOST")
        self.image = Path(image)
        self.timeout = timeout
        self.proc = subprocess.Popen(
            # The session is the test's own ACL2, not the node under test: it
            # runs at ACL2's save-exec stack (64 MiB, what the retired bridge
            # session had), because printing a 49 KiB bundle's octet list
            # recurses past the deployed node's 1 MiB control stack.
            [str(self.image), "--fn", "acl2", "session"], cwd=ROOT,
            env=environment({"SBCL_USER_ARGS": "--control-stack-size 64MB"}, stack=False),
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        try:
            self._until_prompt()
            # The bridge's mode: invariant-risk checks without warning text.
            self.call("(set-check-invariant-risk t)")
        except BaseException:
            self.close()
            raise

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()

    def _until_prompt(self, timeout=None):
        import select
        data = bytearray()
        timeout = timeout or self.timeout
        deadline = time.monotonic() + timeout
        fd = self.proc.stdout.fileno()
        while not ACL2_SESSION_PROMPT.search(data[-64:]):
            left = deadline - time.monotonic()
            if left <= 0:
                raise Acl2ValueError("no ACL2 prompt within {} s: {!r}".format(
                    timeout, bytes(data[-400:])))
            ready, _, _ = select.select([fd], [], [], left)
            if ready:
                chunk = os.read(fd, 65536)
                if not chunk:
                    raise Acl2ValueError("the ACL2 session ended (exit {}): {!r}".format(
                        self.proc.poll(), bytes(data[-400:])))
                data += chunk
        return bytes(data)

    def call(self, form, timeout=None):
        """FORM (text) evaluated; ACL2's printed value and its prompt.  The
        image's world already holds every book it was built with; an
        `include-book` here would load a book's source over it, uncertified
        (the image's tree need not hold certificates), and is refused.  An
        `ld` of a tool's own program file (tools/synth-log-store.lisp) is
        the tool's business."""
        if re.match(r"\s*\(include-book\s", form, re.IGNORECASE):
            raise Acl2ValueError("the image's world is loaded; no include-book in a session")
        self.proc.stdin.write(form.encode("utf-8") + b"\n")
        self.proc.stdin.flush()
        output = self._until_prompt(timeout)
        return ACL2_SESSION_PROMPT.sub(ACL2_PROMPT, output)

    @staticmethod
    def literal(octets):
        """OCTETS as an ACL2 list of naturals, `(72 101 ...)`."""
        return "(" + " ".join(str(octet) for octet in octets) + ")"

    def text(self, octets):
        """A form whose value is OCTETS as the string ACL2's record fields hold."""
        return "(fn-store-octets->string '" + self.literal(octets) + ")"

    def subject(self, msgid, article):
        """ARTICLE's canonical subject identity, as the text a record field
        carries (books/identity.lisp: fn-store-subject-id-of-payload, then
        fn-store-identity-text).  MSGID is accepted for the old call shape
        (run_store.metadata) and not part of the subject."""
        del msgid
        return acl2_octets(self.call(
            "(fn-store-identity-text (fn-store-subject-id-of-payload '"
            + self.literal(article) + "))"))

    def bp_request(self, fields, article):
        """The BP application request (books/bp-adu.lisp fn-bpa-encode of
        fn-bpa-make-request) of FIELDS -- work, subject, source, destination,
        policy, origin, authorization, terms, each octets -- and ARTICLE."""
        return acl2_octets(self.call(
            "(fn-bpa-encode (fn-bpa-make-request "
            + " ".join(self.text(value) for value in fields)
            + " '" + self.literal(article) + "))"))

    def close(self):
        proc, self.proc = getattr(self, "proc", None), None
        if proc is None:
            return
        with contextlib.suppress(OSError, ValueError):
            proc.stdin.write(b":q\n")
            proc.stdin.close()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
        proc.stdout.close()


# --- Images and the environment ------------------------------------------

# Where each image variable points when unset (tools/native_env.py IMAGES
# names which built image satisfies it).
IMAGE_DEFAULTS = {
    "FN_NATIVE_HOST": "build/fn-host",
    "FN_NATIVE_DEVELOPER_HOST": "build/fn-host-developer",
    "FN_NATIVE_REFERENCE_HOST": "build/fn-host-reference",
    "FN_NATIVE_DEVELOPER_STRIPPED_HOST": "build/fn-host-developer-stripped",
    "FN_NATIVE_CRASH_HOST": "build/fn-host-developer",
    "FN_NATIVE_BP_HOST": "build/fn-host-dtn",
    "FN_NATIVE_CONTACT_SENDER": "build/fn-host-dtn",
    "FN_NATIVE_CONTACT_RECEIVER": "build/fn-host-dtn",
    "FN_NATIVE_DTN_HOST": "build/fn-host-dtn",
    "FN_NATIVE_DTN_DEVELOPER_HOST": "build/fn-host-dtn-developer",
}


def native_image(variable, default=None):
    """The image VARIABLE names, else DEFAULT (a path, relative to the tree),
    else the variable's usual image.  Call it with the variable's name as a
    literal: tools/native_env.py counts `native_image("NAME"` as a read."""
    value = os.environ.get(variable)
    if value:
        return Path(value)
    return ROOT / (default if default is not None else IMAGE_DEFAULTS[variable])


def executable(image):
    image = Path(image)
    return image.is_file() and os.access(image, os.X_OK)


def requires(*images):
    """unittest.skipUnless every IMAGE is an executable, naming the ones absent."""
    import unittest
    absent = [str(image) for image in images if not executable(image)]
    return unittest.skipUnless(not absent, "native image required: {}".format(", ".join(absent)))


def deployed_stack(env):
    """PKT-876: every native test runs at the deployed control stack.  The
    image's own launcher carries ACL2's figure (tools/build_native_host.sh
    writes books/heap-reservation.lisp fn-heap-stack-kib, 1,024 KiB, where
    ACL2's save-exec wrote 64 MiB), the figure the installed launcher
    (packaging/fn) passes a node.  FN_TEST_CONTROL_STACK_KB runs the image at
    another figure (SBCL_USER_ARGS comes after the launcher's own option, so
    it wins), and only with FN_TEST_CONTROL_STACK_REASON naming why: a wider
    stack hides the deaths the deployed node dies of."""
    kib = os.environ.get("FN_TEST_CONTROL_STACK_KB")
    if kib:
        if not kib.isdigit():
            raise ValueError("FN_TEST_CONTROL_STACK_KB is not a decimal: %r" % kib)
        if not os.environ.get("FN_TEST_CONTROL_STACK_REASON", "").strip():
            raise ValueError("FN_TEST_CONTROL_STACK_KB=%s needs FN_TEST_CONTROL_STACK_REASON: "
                             "the default is the deployed stack" % kib)
        env["SBCL_USER_ARGS"] = "--control-stack-size {}KB".format(kib)
    return env


_SELECTORS = []


def developer_selectors():
    """The developer-image selectors host/native/io.lisp registers
    (`+fnn-developer-selectors+`): a test sets one for one start only, so
    `environment` never inherits one from the shell."""
    if not _SELECTORS:
        source = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="utf-8")
        found = re.search(r"\(defparameter \+fnn-developer-selectors\+\s+'\((.*?)\)\)", source, re.S)
        if not found:
            raise RuntimeError("host/native/io.lisp: +fnn-developer-selectors+ not found")
        _SELECTORS.extend(re.findall(r'"(FN_[A-Z0-9_]+)"', found.group(1)))
    return tuple(_SELECTORS)


def environment(extra=None, *, stack=True):
    """The environment a native process gets: the shell's, at the deployed
    control stack (STACK), without the ACL2 customization or system books,
    without FN_HOST or any developer selector, plus EXTRA (a None value
    removes)."""
    env = dict(os.environ)
    if stack:
        deployed_stack(env)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    for name in ("ACL2_SYSTEM_BOOKS", "FN_HOST") + developer_selectors():
        env.pop(name, None)
    for name, value in (extra or {}).items():
        if value is None:
            env.pop(name, None)
        else:
            env[name] = str(value)
    return env


def free_port():
    """A loopback port nothing held a moment ago."""
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def run(argv, *, env=None, timeout=180, cwd=None, stdin=None, input=None, text=False):
    """ARGV to completion with both streams captured (a CompletedProcess);
    TEXT decodes both (UTF-8, undecodable octets replaced)."""
    result = subprocess.run([str(word) for word in argv], cwd=cwd or ROOT,
                            env=env or environment(), stdin=stdin, input=input,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=timeout, check=False)
    if text:
        result.stdout, result.stderr = (stream.decode("utf-8", "replace")
                                        for stream in (result.stdout, result.stderr))
    return result


def class_case(cls):
    """A case whose cleanups are CLS's class cleanups, for a Node made in
    setUpClass that lives as long as the class."""
    import unittest
    case = unittest.TestCase()
    case.addCleanup = cls.addClassCleanup
    return case


def scratch(case, prefix="fn-native-"):
    """A temporary directory removed when CASE's test ends."""
    directory = tempfile.TemporaryDirectory(prefix=prefix)
    case.addCleanup(directory.cleanup)
    return Path(directory.name)


# --- Nodes ------------------------------------------------------------------

class Node:
    """One node's scratch tree and the verbs a test runs on it.

    ROOT/fn.toml names ROOT/store, a loopback listener on a free port and
    ROOT/control.sock (LISTENER/CONTROL False leave a section out; TLS is
    the text of a [tls] section; EXTRA is appended verbatim).  Every process
    `start` makes is stopped when CASE's test ends.  LAUNCHER is an
    installed `bin/fn` (it supplies `--fn` itself) run in place of the image
    when a verb names no image; `use_tls` adds an implicit-TLS listener."""

    def __init__(self, case, image, *, root=None, name="node", listener=True,
                 control=True, tls=None, extra="", env=None, port=None, launcher=None):
        self.case = case
        self.image = Path(image)
        self.launcher = launcher
        self.listening = 1 if listener else 0
        self.tls_port = None
        self.name = name
        self.root = Path(root) if root is not None else scratch(case) / name
        self.root.mkdir(parents=True, exist_ok=True)
        self.store_path = self.root / "store"
        self.config = self.root / "fn.toml"
        self.control = self.root / "control.sock" if control else None
        self.port = (port or free_port()) if listener else None
        self.env = dict(env or {})
        self.process = None
        self.processes = []
        self.write_config(listener=listener, tls=tls, extra=extra)
        case.addCleanup(self.stop_all)

    def write_config(self, *, listener=True, tls=None, extra="", protected_only=False):
        """fn.toml; EXTRA follows the [listener] fields (inside that table)."""
        text = '[store]\npath = "{}"\n'.format(self.store_path)
        if listener:
            text += '[listener]\nhost = "127.0.0.1"\nport = {}\n'.format(self.port)
            text, extra = text + extra, ""
        if self.control is not None:
            text += '[control]\npath = "{}"\n'.format(self.control)
        if tls:
            text += "[tls]\n" + tls.rstrip("\n") + "\n"
        if protected_only:
            text += "[auth]\nprotected_only = true\n"
        text += extra
        self.config.write_text(text, encoding="utf-8")

    def use_tls(self, *, alt_name=False, protected_only=True):
        """A second, implicit-TLS listener (`tls_port`) with a fresh
        self-signed certificate for 127.0.0.1 (with the IP SAN when
        ALT_NAME), and `[auth] protected_only` as asked."""
        self.tls_port = free_port()
        self.cert, key = self.root / "cert.pem", self.root / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout",
                        str(key), "-out", str(self.cert), "-days", "2", "-nodes",
                        "-subj", "/CN=127.0.0.1",
                        *(("-addext", "subjectAltName=IP:127.0.0.1") if alt_name else ())],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.listening = 2
        self.write_config(extra='tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n'.format(
            self.tls_port, self.cert, key), protected_only=protected_only)
        return self

    def environment(self, extra=None):
        merged = {"FN_NATIVE_HOST": None} if self.launcher else {}
        merged.update(self.env)
        merged.update(extra or {})
        return environment(merged)

    def argv(self, image, words):
        if self.launcher and image is None:
            return [self.launcher, *words]
        return [image or self.image, "--fn", *words]

    def invoke(self, *words, image=None, env=None, timeout=180, input=None, expect=None):
        """`IMAGE --fn WORDS...` to completion; with EXPECT, assert its class."""
        result = run(self.argv(image, words), env=self.environment(env),
                     timeout=timeout, input=input)
        if expect is not None:
            assert_outcome(self.case, result, expect,
                           log=self.process if self.process is not None else None)
        return result

    def operator(self, *words, **options):
        return self.invoke("operator", self.config, *words, **options)

    def store(self, *words, **options):
        return self.invoke("store", self.store_path, *words, **options)

    def init(self, *groups, profile=None, expect=EXIT.OK, **options):
        """`operator CONFIG init [--profile P] GROUP...` (default fn.test)."""
        words = (["--profile", profile] if profile else []) + list(groups or ("fn.test",))
        return self.operator("init", *words, expect=expect, **options)

    def start(self, *, image=None, env=None, ready=b"LISTENING ", timeout=180, verb=("run",),
              limit=DEFAULT_LIMIT):
        """`operator CONFIG run`, drained (LIMIT octets kept per stream),
        returned once READY is on stdout."""
        process = start(self.argv(image, ("operator", self.config, *verb)),
                        cwd=ROOT, env=self.environment(env), limit=limit)
        self.processes.append(process)
        self.process = process
        if ready and self.listening > 1:
            # Several listeners announce in either order.
            for _ in range(self.listening):
                process.announcement(b"LISTENING", timeout=timeout)
        elif ready:
            line = process.announcement(ready, timeout=timeout)
            if ready == b"LISTENING " and self.port is not None:
                self.case.assertEqual(line, "LISTENING {}\n".format(self.port).encode(),
                                      "{} announced {!r}".format(self.name, line))
        return process

    def start_store_owner(self, *, once=True, fault=None, connections=8, env=None, image=None):
        """`owner run STORE 0 ONCE N [FAULT]`, the store owner on an ephemeral
        port, drained and stopped at cleanup; (process, announced port)."""
        words = ["owner", "run", self.store_path, "0", "1" if once else "0", str(connections)]
        process = start(self.argv(image, words + ([fault] if fault else [])),
                        cwd=ROOT, env=self.environment(env))
        self.processes.append(process)
        self.process = process
        return process, int(process.announcement(b"LISTENING ").split()[1])

    def try_start(self, *, image=None, env=None, timeout=180):
        """(the owner, None) once it announces LISTENING, or (the exited
        owner, its stderr) when it refuses to start: for a case whose
        subject is the refusal."""
        process = start(self.argv(image, ("operator", self.config, "run")),
                        cwd=ROOT, env=self.environment(env))
        self.processes.append(process)
        self.process = process
        text, end = process.stdout.wait_for(_line_starting(b"LISTENING "), 0,
                                            time.monotonic() + timeout)
        if end is not None:
            process.cursor = end
            return process, None
        if process.poll() is None:
            process.fail("the owner neither announced nor exited within {} s".format(timeout))
        process.finish()
        return process, process.stderr.since(0).decode("utf-8", "replace")

    def stop(self, expect=EXIT.OK, process=None, grace=60):
        """SIGTERM the owner and assert it exited EXPECT (None: any)."""
        process = process or self.process
        status = process.stop(grace=grace)
        if expect is not None:
            assert_outcome(self.case, status, expect, log=process)
        return status

    def exited(self, expect, timeout=60, process=None):
        """Wait for the owner to exit on its own and assert its class."""
        process = process or self.process
        try:
            status = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            process.fail("{} did not exit within {} s".format(self.name, timeout))
        process.finish()
        assert_outcome(self.case, status, expect, log=process)
        return status

    def stop_all(self):
        for process in self.processes:
            process.terminate()
        for process in self.processes:
            process.stop(grace=30)

    def post(self, message_id, payload, *, group="fn.test", expect=None, **options):
        """`operator CONFIG post` of PAYLOAD (octets) under MESSAGE_ID."""
        path = self.root / "post-{}.eml".format(len(list(self.root.glob("post-*.eml"))))
        path.write_bytes(payload)
        return self.operator("post", "--message-id", message_id, "--payload", path,
                             "--group", group, expect=expect, **options)

    def session(self, **options):
        return Client(self.port, **options)

    def log_on_failure(self, process=None):
        return node_log_on_failure(process or self.process)


def _log_digest(log):
    if isinstance(log, NativeProcess):
        return "exit={}\n{}".format(log.poll(), stderr_digest(log.stderr.since(0)))
    return node_log_digest(log)


_DIAGNOSTIC_DIR = "FN_NATIVE_TEST_DIAGNOSTIC_DIR"


def keep_diagnostics(case, nodes):
    """At CASE's end, append each owner's retained stderr to
    FN_NATIVE_TEST_DIAGNOSTIC_DIR/<test>-<node>.stderr when that is set.
    Register before the nodes exist: cleanups run last-first, so this runs
    after the nodes' own cleanup has stopped every owner."""
    keep = os.environ.get(_DIAGNOSTIC_DIR)
    if not keep:
        return

    def write():
        directory = Path(keep)
        directory.mkdir(parents=True, exist_ok=True)
        for node in nodes:
            path = directory / (case.id().rsplit(".", 1)[-1] + "-" + node.name + ".stderr")
            with path.open("ab") as out:
                for process in node.processes:
                    out.write(process.stderr.since(0))
    case.addCleanup(write)


# --- Clients ----------------------------------------------------------------

def client_context():
    """TLS 1.2+ with no verification: the tests assert the node's policy,
    not a certificate chain."""
    context = ssl.create_default_context()
    context.check_hostname = False
    context.verify_mode = ssl.CERT_NONE
    context.minimum_version = ssl.TLSVersion.TLSv1_2
    return context


class Client:
    """One NNTP connection over octets.  Every read is bounded by TIMEOUT;
    `line()` returns the line with its CRLF, `block()` a dot-terminated
    block with the stuffing undone.  IMPLICIT_TLS opens TLS before the
    greeting (RFC 8143); `starttls()` upgrades after a 382 (RFC 4642)."""

    def __init__(self, port, *, host="127.0.0.1", timeout=60, implicit_tls=None,
                 greeting=(b"200", b"201"), source=None, server_hostname=None):
        self.sock = socket.create_connection(
            (host, port), timeout=timeout,
            source_address=(source, 0) if source else None)
        self.sock.settimeout(timeout)
        self.host = host
        self.server_hostname = server_hostname or host
        self.buffer = bytearray()
        self.offset = 0
        try:
            if implicit_tls is not None:
                self.sock = implicit_tls.wrap_socket(self.sock,
                                                     server_hostname=self.server_hostname)
            self.greeting = self.line()
        except BaseException:
            self.sock.close()
            raise
        if greeting and not self.greeting[:3] in greeting:
            self.close(quit=False)
            raise AssertionError("greeting {!r}".format(self.greeting))

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()

    def line(self, limit=None):
        """The next line with its CRLF.  No length is assumed (a served line
        is as long as the stored article's, D27); LIMIT, when a case asks for
        one, fails a longer line.  Linear in what is read: the buffer is a
        bytearray consumed from an offset and compacted when half spent."""
        scanned = self.offset
        while True:
            at = self.buffer.find(b"\r\n", max(self.offset, scanned - 1))
            if at >= 0:
                line = bytes(self.buffer[self.offset:at + 2])
                self.offset = at + 2
                if self.offset > (1 << 20) and self.offset * 2 > len(self.buffer):
                    del self.buffer[:self.offset]
                    self.offset = 0
                return line
            scanned = len(self.buffer)
            if limit is not None and scanned - self.offset > limit:
                raise AssertionError("an NNTP line past {} octets".format(limit))
            chunk = self.sock.recv(1 << 20)
            if not chunk:
                raise EOFError("the node closed the connection")
            self.buffer += chunk

    @property
    def pending(self):
        """Octets received and not yet returned by `line`."""
        return bytes(self.buffer[self.offset:])

    def send(self, octets):
        self.sock.sendall(octets)

    def command(self, text):
        """Send TEXT (octets or str, CRLF added) and return the status line."""
        if isinstance(text, str):
            text = text.encode("utf-8")
        self.send(text + b"\r\n")
        return self.line()

    def block(self):
        lines = []
        while True:
            line = self.line()
            if line == b".\r\n":
                return b"".join(lines)
            lines.append(line[1:] if line.startswith(b"..") else line)

    def multiline(self, text):
        """(status, body) for a command whose success status carries a block."""
        status = self.command(text)
        return status, (self.block() if status[:1] in b"12" and status[:3] != b"111" else b"")

    def post(self, article, verb=b"POST", tolerate_send_error=False):
        """POST (or IHAVE <id>: VERB) ARTICLE; (first status, final status or None).
        TOLERATE_SEND_ERROR: a node that answers an oversize article and
        closes before it has all of it resets the send; read its reply anyway."""
        first = self.command(verb)
        if not first.startswith((b"340", b"335")):
            return first, None
        try:
            self.send(dot_stuff(article) + b".\r\n")
        except OSError:
            if not tolerate_send_error:
                raise
        return first, self.line()

    def article(self, message_id):
        """The served octets of ARTICLE MESSAGE_ID, or None when not 220."""
        status, body = self.multiline(b"ARTICLE " + _octets(message_id))
        return body if status.startswith(b"220") else None

    def starttls(self, context=None):
        status = self.command(b"STARTTLS")
        if status.startswith(b"382"):
            if self.pending:
                raise AssertionError("octets followed the 382 before the handshake")
            self.sock = (context or client_context()).wrap_socket(
                self.sock, server_hostname=self.server_hostname)
        return status

    def close(self, quit=True):
        if quit:
            try:
                self.send(b"QUIT\r\n")
            except OSError:
                pass
        try:
            self.sock.close()
        except OSError:
            pass


def _octets(value):
    return value.encode("utf-8") if isinstance(value, str) else value


def dot_stuff(article):
    """ARTICLE, CRLF-terminated, with a dot doubled at the start of every
    line (RFC 3977 3.1.1); lines are split at CRLF only, never a bare CR or LF."""
    if not article.endswith(b"\r\n"):
        article += b"\r\n"
    return b"\r\n".join(b"." + line if line.startswith(b".") else line
                         for line in article.split(b"\r\n"))


def article(message_id, *, groups="fn.test", subject="native test",
            sender="author@example.invalid", date="Mon, 21 Sep 2026 09:00:00 +0000",
            body=b"body\r\n", headers=()):
    """A test article as CRLF octets (DATE None leaves Date out)."""
    lines = ["From: " + sender, "Newsgroups: " + groups, "Subject: " + subject]
    if date:
        lines.append("Date: " + date)
    lines.append("Message-ID: " + _octets(message_id).decode("utf-8"))
    lines.extend(headers)
    head = "".join(line + "\r\n" for line in lines).encode("utf-8")
    return head + b"\r\n" + _octets(body)

#!/usr/bin/env python3
"""A live ACL2 session over one book, driven a form at a time from the shell.

The wrong loop for proof work is `certify-book`: twenty minutes a closure on
the farm, and a red at the bottom hides everything above it (the review of
2026-09-22, planning/review-2026-09-22-proof-engineering.md, F1 and F5).  The
right loop is one ACL2 process with the book's certified dependencies
included from the cache -- seconds -- and the book's own events loaded up to
the one that fails, where each `defthm` attempt costs what the prover spends
on it and nothing else.  This tool is that process, kept alive behind a Unix
socket so that an agent (or a person) can talk to it from any shell.

    python3 tools/proof_repl.py start sni books/store-node-invariants \\
        --upto fn-sn-finish-preserves-state
    python3 tools/proof_repl.py send sni '(defthm try1 ... :hints (...))'
    python3 tools/proof_repl.py send sni '(accumulated-persistence t)' --full
    python3 tools/proof_repl.py status sni
    python3 tools/proof_repl.py stop sni

`start` acquires a complete, ACL2-compatible certificate set for the book's
local include closure from the cache. An incompatible or missing dependency
refuses startup before a session is created. It then starts ACL2 through
`tools/acl2` (so the machine-wide slot pool holds), sets the connected book
directory to `books/`, and sends the book's top-level forms in order up to
the named event, stopping at the first form ACL2 refuses.  `send` delivers
one complete form and answers with what ACL2 printed, trimmed to the key
checkpoints and the summary unless `--full`; an event form is wrapped in
`with-prover-time-limit` (default 60 s, `--limit`), so a search that stops
returning costs a minute, not a session.  Everything ACL2 prints is also in
build/proof-repl/<name>/log.

What a green here means: that ACL2 admitted the form in a session whose
dependencies are cached certificates.  It is not a certificate; when the
proof is found, put the event in the book and certify the book.
"""
from __future__ import annotations

import argparse
import contextlib
import fcntl
import json
import os
from pathlib import Path
import queue
import re
import shutil
import signal
import socket
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import theory_check  # noqa: E402
import acl2_slots  # noqa: E402
import acl2_toolchain  # noqa: E402
import certs  # noqa: E402

SESSIONS = ROOT / "build" / "proof-repl"
SENTINEL = "FN-REPL-DONE"
EVENT_HEADS = ("defthm", "defthmd", "defun", "defund", "defrule", "defruled",
               "encapsulate", "verify-guards", "thm", "defthm-flag", "mutual-recursion",
               "defconst", "define", "defines", "make-event")
ERROR_MARKS = ("ACL2 Error", "HARD ACL2 ERROR", "ACL2 Halted")


# --- reading a book as raw top-level forms ---------------------------------

def spans(text: str) -> list[tuple[int, int]]:
    """The (start, end) of each top-level form, quotes included, comments not."""
    depth = 0
    start = None
    pending_quote = None
    found = []
    for match in theory_check.TOKEN.finditer(text):
        kind = match.lastgroup
        if kind in ("comment", "block"):
            continue
        if depth == 0:
            if kind == "quote":
                pending_quote = match.start() if pending_quote is None else pending_quote
                continue
            if kind == "open":
                start = pending_quote if pending_quote is not None else match.start()
                depth = 1
            elif kind in ("atom", "string"):
                begin = pending_quote if pending_quote is not None else match.start()
                found.append((begin, match.end()))
            pending_quote = None
            continue
        if kind == "open":
            depth += 1
        elif kind == "close":
            depth -= 1
            if depth == 0:
                found.append((start, match.end()))
                start = None
    if depth != 0:
        raise ValueError("unbalanced parentheses")
    return found


def forms(text: str) -> list[str]:
    return [text[a:b] for a, b in spans(text)]


HEAD = re.compile(r"^\(\s*(?:local\s+\(\s*)?([^\s()]+)(?:\s+([^\s()]+))?", re.IGNORECASE)


def head_and_name(form: str) -> tuple[str, str | None]:
    """('defthm', 'foo') for an event form; (head, None) otherwise."""
    match = HEAD.match(form)
    if not match:
        return form.strip("()' \n")[:32].lower(), None
    head = match.group(1).lower()
    named = match.group(2) is not None and (head in EVENT_HEADS or head.startswith("def"))
    return head, (match.group(2).lower() if named else None)


def is_event(form: str) -> bool:
    head, _ = head_and_name(form)
    return head in EVENT_HEADS or head.startswith("def")


# --- the ACL2 process --------------------------------------------------------

class Acl2:
    """One ACL2 child with a reader thread and a sentinel after every form."""

    def __init__(self, label: str, log_path: Path):
        self.log = open(log_path, "a", encoding="utf-8")
        self.process = subprocess.Popen(
            [sys.executable, str(ROOT / "tools" / "acl2"), "--label", label],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, bufsize=1, cwd=ROOT, start_new_session=True)
        # Do not reap this group leader until shutdown has signalled the
        # group. Its unreaped PID cannot be reused for an unrelated group.
        self.pgid = self.process.pid
        self._terminated = False
        self.lines: queue.Queue = queue.Queue()
        self.counter = 0
        self.reader = threading.Thread(target=self._pump, daemon=True)
        self.reader.start()

    def _pump(self) -> None:
        assert self.process.stdout is not None
        for line in self.process.stdout:
            self.log.write(line)
            self.log.flush()
            self.lines.put(line)
        self.lines.put(None)

    def alive(self) -> bool:
        return self.process.returncode is None and self.reader.is_alive()

    def send(self, form: str, timeout: float) -> tuple[str, bool]:
        """Deliver one form; answer (what ACL2 printed, timed out?)."""
        assert self.process.stdin is not None
        self.counter += 1
        marker = f"{SENTINEL} {self.counter}"
        self.log.write(">>> " + form.rstrip() + "\n")
        self.process.stdin.write(form.rstrip() + "\n")
        self.process.stdin.write(f'(cw "~%{marker}~%")\n')
        self.process.stdin.flush()
        collected: list[str] = []
        deadline = time.monotonic() + timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return "".join(collected), True
            try:
                line = self.lines.get(timeout=min(remaining, 1.0))
            except queue.Empty:
                if not self.alive():
                    return "".join(collected) + "\n[ACL2 exited]\n", False
                continue
            if line is None:
                return "".join(collected) + "\n[ACL2 exited]\n", False
            if line.strip() == marker:
                return "".join(collected), False
            collected.append(line)

    def kill(self) -> None:
        if self._terminated:
            return
        # The slot wrapper and ACL2 share the fresh group rooted at the
        # unreaped wrapper. Signal that one owned group before wait() can
        # recycle its leader PID; never select processes by name or label.
        if self.process.returncode is None:
            self._signal_group(signal.SIGTERM)
            self.reader.join(timeout=1)
            self._signal_group(signal.SIGKILL)
        self.process.wait(timeout=5)
        self.reader.join(timeout=5)
        if self.reader.is_alive():
            raise RuntimeError("proof-repl: output remains open after session termination")
        self._terminated = True
        self.log.close()
        if self.process.stdin is not None:
            # A graceful good-bye may leave a buffered sentinel whose reader
            # has already exited. Closing that pipe is still successful cleanup.
            with contextlib.suppress(BrokenPipeError):
                self.process.stdin.close()
        if self.process.stdout is not None:
            self.process.stdout.close()

    def _signal_group(self, number: int) -> None:
        try:
            os.killpg(self.pgid, number)
        except ProcessLookupError:
            pass
        except PermissionError:
            # Darwin reports EPERM for a group containing only exited
            # processes. It is safe only when every output holder reached EOF.
            if self.reader.is_alive():
                raise


def errored(output: str) -> bool:
    return any(mark in output for mark in ERROR_MARKS)


def brief(output: str, keep: int = 60) -> str:
    """The checkpoints and the summary, not the whole proof."""
    lines = [line for line in output.splitlines() if line.strip() not in ("ACL2 !>", "")]
    if len(lines) <= keep:
        return "\n".join(lines)
    anchors = [i for i, line in enumerate(lines)
               if line.startswith("*** Key checkpoint") or "ACL2 Error" in line
               or line.startswith("Summary") or "HARD ACL2 ERROR" in line]
    if anchors:
        first = anchors[0]
        return "\n".join(lines[:4] + ["..."] + lines[first:])
    return "\n".join(lines[:4] + ["..."] + lines[-keep:])


def wrap_limit(form: str, limit: float | None) -> str:
    if limit and is_event(form):
        return f"(with-prover-time-limit {int(limit)} {form})"
    return form


# --- the session server ------------------------------------------------------

def session_dir(name: str) -> Path:
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", name):
        raise SystemExit(f"proof-repl: session name {name!r}: letters, digits, . _ - only")
    return SESSIONS / name


def session_lock_path(name: str) -> Path:
    session_dir(name)  # validate the name before constructing a lock path
    return SESSIONS / ".locks" / name


def open_session_lock(name: str) -> int | None:
    """Claim one name before cache acquisition, passing this lock to serve."""
    path = session_lock_path(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_CREAT | os.O_RDWR, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        os.close(fd)
        return None
    return fd


def serve(name: str, book: str, upto: str | None, through: str | None,
          limit: float, load_timeout: float, lock_fd: int) -> int:
    directory = session_dir(name)
    directory.mkdir(parents=True, exist_ok=True)
    state_path = directory / "state.json"
    sock_path = directory / "sock"
    state = {"name": name, "book": book, "pid": os.getpid(), "loaded": [],
             "stopped_at": None, "error": None, "ready": False, "sends": 0}

    def save() -> None:
        staged = directory / f".state-{os.getpid()}.tmp"
        staged.write_text(json.dumps(state, indent=1))
        os.replace(staged, state_path)

    acl2 = None
    server = None
    bound = False
    try:
        save()
        source = ROOT / f"{book}.lisp"
        text = source.read_text(encoding="utf-8")
        acl2 = Acl2(f"proof-repl {name}", directory / "log")
        output, timed_out = acl2.send(f'(set-cbd "{source.parent}/")', load_timeout)
        if timed_out or errored(output):
            state["stopped_at"] = "set-cbd"
            state["error"] = "load timed out" if timed_out else brief(output)
        else:
            stop_after = (through or "").lower()
            stop_before = (upto or "").lower()
            for form in forms(text):
                head, event = head_and_name(form)
                if stop_before and event == stop_before:
                    break
                output, timed_out = acl2.send(form, load_timeout)
                if timed_out or errored(output):
                    state["stopped_at"] = event or head
                    state["error"] = ("load timed out" if timed_out else brief(output))
                    break
                state["loaded"].append(event or head)
                if stop_after and event == stop_after:
                    break
        if timed_out:
            acl2.kill()
        state["ready"] = acl2.alive()
        save()

        server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            server.bind(str(sock_path))
        except OSError as error:
            state["error"] = f"session socket unavailable: {error}"
            state["ready"] = False
            save()
            return 1
        bound = True
        server.listen(4)
        while acl2.alive():
            connection, _ = server.accept()
            with connection:
                request = json.loads(read_all(connection))
                answer = handle(request, acl2, state, limit)
                if request.get("op") == "stop":
                    # A successful stop reply means the process group and
                    # endpoint are gone, not merely that a request was read.
                    acl2.kill()
                    state["ready"] = False
                    sock_path.unlink(missing_ok=True)
                save()
                connection.sendall(json.dumps(answer).encode("utf-8"))
                if request.get("op") == "stop":
                    break
    finally:
        if server is not None:
            server.close()
        if acl2 is not None:
            acl2.kill()
        state["ready"] = False
        save()
        if bound:
            sock_path.unlink(missing_ok=True)
        os.close(lock_fd)
    return 0


def handle(request: dict, acl2: Acl2, state: dict, default_limit: float) -> dict:
    op = request.get("op", "send")
    if op == "status":
        return {"state": state}
    if op == "stop":
        try:
            acl2.send("(good-bye)", 1)
        except (BrokenPipeError, OSError):
            # A dead ACL2 cannot acknowledge, but the server still owns and
            # tears down its original process group before replying.
            pass
        return {"stopped": True}
    form = request["form"]
    try:
        count = len(spans(form))
    except ValueError as error:
        return {"error": True, "output": f"not one complete form: {error}"}
    if count != 1:
        return {"error": True, "output": f"send exactly one form, not {count}"}
    limit = request.get("limit") or default_limit
    started = time.monotonic()
    output, timed_out = acl2.send(wrap_limit(form, limit), limit * 1.5 + 30)
    elapsed = round(time.monotonic() - started, 1)
    state["sends"] += 1
    if timed_out:
        acl2.kill()
        state["ready"] = False
        return {"error": True, "timed_out": True, "elapsed": elapsed,
                "output": output + "\n[session killed: no sentinel within the hard limit]"}
    return {"error": errored(output), "elapsed": elapsed, "output": output}


def read_all(connection: socket.socket) -> bytes:
    chunks = []
    while True:
        chunk = connection.recv(65536)
        if not chunk:
            return b"".join(chunks)
        chunks.append(chunk)


# --- the client ----------------------------------------------------------------

def ask(name: str, request: dict, timeout: float = 3600) -> dict:
    sock_path = session_dir(name) / "sock"
    if not sock_path.exists():
        raise SystemExit(f"proof-repl: no live session {name!r} (start it first)")
    client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    client.settimeout(timeout)
    client.connect(str(sock_path))
    client.sendall(json.dumps(request).encode("utf-8"))
    client.shutdown(socket.SHUT_WR)
    return json.loads(read_all(client))


def install_closure(book: str) -> tuple[bool, str]:
    """Acquire all dependencies under the same ACL2 used by the REPL child."""
    try:
        names = [name for name in certs.closure(ROOT, book) if name != book]
    except (OSError, certs.UnreadableBook, ValueError) as error:
        return False, f"proof-repl: cannot read {book}'s closure: {error}"
    if not names:
        return True, "no dependencies to install"
    configured = os.environ.get("FN_ACL2", "acl2")
    found = (configured if "/" in configured else shutil.which(configured))
    if not found:
        return False, f"proof-repl: no ACL2 executable at {configured!r}"
    acl2 = Path(found).expanduser().resolve()
    fingerprint = acl2_toolchain.fingerprint(acl2)
    if not fingerprint.qualified or fingerprint.identity is None:
        return False, ("proof-repl: unqualified ACL2 launcher/core/runtime: "
                       + fingerprint.reason)
    try:
        # The alist probe starts ACL2 directly. Hold the same machine-wide
        # slot that the subsequent interactive wrapper will take.
        with acl2_slots.slot(f"proof-repl cache {book}"):
            report = certs.install_artifact_set(
                ROOT, certs.cache_directory(), [book],
                toolchain_identity=fingerprint.identity,
                dependencies_only=True, purge_on_miss=True, acl2=acl2)
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        return False, f"proof-repl: certificate acquisition failed: {error}"
    if report.artifact_set is None:
        return False, ("proof-repl: no complete compatible cached dependency set; "
                       + ", ".join(report.uncached))
    return True, "\n".join(report.lines())


def start(args) -> int:
    directory = session_dir(args.name)
    lock_fd = open_session_lock(args.name)
    if lock_fd is None:
        print(f"proof-repl: session {args.name!r} is starting or live; stop it first")
        return 2
    try:
        # A server started by the older tool has no name lock. Do not probe
        # its socket: an empty or interrupted probe is malformed JSON to the
        # old server and can terminate that still-live proof session.
        old_sock = directory / "sock"
        if old_sock.exists():
            print(f"proof-repl: session {args.name!r} has a socket; "
                  "stop it or inspect the stale endpoint before restarting")
            return 2
        acquired, detail = install_closure(args.book)
        print(detail)
        if not acquired:
            return 1
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "state.json").unlink(missing_ok=True)
        with open(directory / "server.log", "a", encoding="utf-8") as log:
            command = [sys.executable, __file__, "serve", args.name, args.book,
                       "--limit", str(args.limit), "--load-timeout", str(args.load_timeout),
                       "--lock-fd", str(lock_fd)]
            if args.upto:
                command += ["--upto", args.upto]
            if args.through:
                command += ["--through", args.through]
            subprocess.Popen(command, stdout=log, stderr=log, cwd=ROOT,
                             start_new_session=True, pass_fds=(lock_fd,))
        deadline = time.monotonic() + args.load_timeout * 3 + 60
        while time.monotonic() < deadline:
            state_path = directory / "state.json"
            if state_path.exists():
                try:
                    state = json.loads(state_path.read_text())
                except (FileNotFoundError, json.JSONDecodeError):
                    time.sleep(0.05)
                    continue
                if state.get("ready") and (directory / "sock").exists():
                    break
                if state.get("error") and not state.get("ready"):
                    print(f"proof-repl: session {args.name!r} failed during load; "
                          f"see {directory / 'log'}")
                    return 1
            time.sleep(0.5)
        else:
            print("proof-repl: the session did not become ready; see", directory / "log")
            return 1
        return status(args)
    finally:
        os.close(lock_fd)


def status(args) -> int:
    state_path = session_dir(args.name) / "state.json"
    if not state_path.exists():
        print(f"proof-repl: no session {args.name!r}")
        return 1
    state = json.loads(state_path.read_text())
    live = (session_dir(args.name) / "sock").exists()
    print(f"proof-repl {state['name']}: {state['book']}, "
          f"{'live' if live else 'not live'}, {len(state['loaded'])} forms loaded, "
          f"{state['sends']} sends")
    if state["stopped_at"]:
        print(f"  stopped at {state['stopped_at']}:")
        print("  " + (state["error"] or "").replace("\n", "\n  "))
    elif state["loaded"]:
        print(f"  last loaded: {state['loaded'][-1]}")
    return 0


def send(args) -> int:
    form = args.form if args.form != "-" else sys.stdin.read()
    answer = ask(args.name, {"op": "send", "form": form, "limit": args.limit})
    output = answer.get("output", "")
    print(output if args.full else brief(output))
    if "elapsed" in answer:
        print(f"[{answer['elapsed']} s{', timed out' if answer.get('timed_out') else ''}]")
    return 1 if answer.get("error") else 0


def stop(args) -> int:
    try:
        answer = ask(args.name, {"op": "stop"}, timeout=30)
        if not answer.get("stopped"):
            print(f"proof-repl: session {args.name!r} did not confirm cleanup")
            return 1
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            fd = open_session_lock(args.name)
            if fd is not None:
                os.close(fd)
                print(f"proof-repl: stopped {args.name}")
                return 0
            time.sleep(0.05)
    except (SystemExit, OSError, ValueError) as error:
        print(error)
        return 1
    print(f"proof-repl: session {args.name!r} has not released its owned process group")
    return 1


def list_sessions(args) -> int:
    if not SESSIONS.exists():
        print("proof-repl: no sessions")
        return 0
    for directory in sorted(SESSIONS.iterdir()):
        state_path = directory / "state.json"
        if state_path.exists():
            state = json.loads(state_path.read_text())
            live = (directory / "sock").exists()
            print(f"{directory.name:16} {'live' if live else 'dead':5} {state['book']}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("start", help="load a book's certified closure and its forms")
    p.add_argument("name")
    p.add_argument("book", help="books/NAME or tests/acl2/NAME, no .lisp")
    p.add_argument("--upto", default=None, help="stop before this event")
    p.add_argument("--through", default=None, help="stop after this event")
    p.add_argument("--limit", type=float, default=60.0,
                   help="prover time limit per sent event, seconds")
    p.add_argument("--load-timeout", type=float, default=600.0,
                   help="hard limit per form while loading the book")
    p.set_defaults(run=start)
    p = sub.add_parser("serve")
    p.add_argument("name")
    p.add_argument("book")
    p.add_argument("--upto", default=None)
    p.add_argument("--through", default=None)
    p.add_argument("--limit", type=float, default=60.0)
    p.add_argument("--load-timeout", type=float, default=600.0)
    p.add_argument("--lock-fd", type=int, required=True)
    p.set_defaults(run=lambda a: serve(a.name, a.book, a.upto, a.through, a.limit,
                                       a.load_timeout, a.lock_fd))
    p = sub.add_parser("send", help="one form; `-` reads it from stdin")
    p.add_argument("name")
    p.add_argument("form")
    p.add_argument("--limit", type=float, default=None)
    p.add_argument("--full", action="store_true", help="everything ACL2 printed")
    p.set_defaults(run=send)
    p = sub.add_parser("status")
    p.add_argument("name")
    p.set_defaults(run=status)
    p = sub.add_parser("stop")
    p.add_argument("name")
    p.set_defaults(run=stop)
    p = sub.add_parser("list")
    p.set_defaults(run=list_sessions)
    args = parser.parse_args(argv)
    return args.run(args)


if __name__ == "__main__":
    raise SystemExit(main())

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

Measuring and probing (2026-09-27, the lanes' recurring obstructions):

    proof_repl.py send NAME '(defthm a ...) (defthm b ...)'   # several forms
    proof_repl.py send-range NAME BOOK --from EVENT --until EVENT [--keep-going]
    proof_repl.py forms BOOK                                  # #N and name of each form
    proof_repl.py probe NAME EVENT [--hints '((...))'] [--form F] [--stop]

Every answer carries ACL2's own `Time:` (run time) and "Prover steps
counted" from the form's last summary (an encapsulate's counts its inner
events), since elapsed seconds vary 2-5x with the box's load and steps do
not vary at all; a multi-form send and `send-range` print one line per
form, the totals and the forms with the most steps, and stop at the first
refusal unless `--keep-going`.  `--from/--until/--through` take an event
name or `#N`, as does `start --upto/--through`.  A trimmed answer keeps its
head (where show-accumulated-persistence and pso put what matters) and its
checkpoints and summary, and says how many lines it cut and where the whole
answer is (build/proof-repl/NAME/last-output.txt); the diagnostic forms
(pso, pe, pbt, pcb, pr, show-accumulated-persistence, ...) are never
trimmed.  `probe` proves a renamed copy of EVENT in a second session
NAME.probe loaded up to just before it (reused while the book's bytes before
EVENT and its closure are unchanged) and undoes the attempt afterwards, so
neither session moves; `status` reports the load's time and steps and its
costliest forms.

A dependency the cache has no certificate for at this tree's bytes: `start`
first publishes any pair this tree's own manifests vouch for (a lane's own
`certify_books.py` run), then refuses naming each book whose own bytes are
uncertified, the books that miss only because they include one, and the
fixes: `--certify-missing` certifies them (certify_books.py --incremental,
under swarm-build where it exists) and starts; `--source-deps` (or
`--ld-missing`) loads them from source in the session; `--ld BOOK` /
`--source-deps A,B` loads named ones.  A from-source book's proofs run in the
session and `status` marks it "from source (not certified)"; the books of the
closure that include it are loaded from source too, since their
certificates name its other bytes.

A session holds one slot of the machine's ACL2 pool for its whole life, so
it belongs to its lane and ends with it (PKT-346: fifteen finished lanes'
sessions once held fifteen of persvati's sixteen slots).  `start` records
the lane (`--lane`, else $FN_LANE, else the worktree's name under
build/lanes/, or persvati's ~/fn-gates/NAME-repl) and an idle deadline
(`--idle-seconds`, default 7200: longer than a farm wait of 3400 s or an
hbox_native run of 5400 s between two sends, short enough that an abandoned session frees its slot within two
hours); a session with no `send` for that long stops itself.  `list` prints
each session's lane, age, idle time and deadline; `reap` stops the sessions
this tool started that are dead, past their own deadline, idle longer than
`--older-than S`, or tagged `--lane NAME` (the coordinator runs
`reap --lane NAME` when it merges that lane).  It signals only the PIDs a
session's state names, after checking each is still that session's process.
"""
from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
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
# A session with no `send` for this long stops itself (see the header).
DEFAULT_IDLE_SECONDS = 7200.0
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


INCLUDE = re.compile(r'^\(\s*(?:local\s+\(\s*)?include-book\s+"([^"]+)"([^)]*)',
                     re.IGNORECASE)


def include_target(form: str, directory: Path) -> str | None:
    """The repository book a local `(include-book "x")` form names, or None.

    A `:dir`-qualified include is a system book and names nothing here.
    """
    match = INCLUDE.match(form.strip())
    if not match or ":dir" in match.group(2).lower():
        return None
    target = (directory / match.group(1)).with_suffix(".lisp").resolve()
    try:
        return target.relative_to(ROOT.resolve()).with_suffix("").as_posix()
    except ValueError:
        return str(target.with_suffix(""))


def form_label(index: int, form: str) -> str:
    head, event = head_and_name(form)
    return f"#{index} {head}" + (f" {event}" if event else "")


def locate(all_forms: list[str], spec: str) -> int:
    """The zero-based index an event name or `#N` (one-based) names."""
    if spec.startswith("#"):
        try:
            number = int(spec[1:])
        except ValueError:
            raise SystemExit(f"proof-repl: {spec!r}: #N wants a form number") from None
        if not 1 <= number <= len(all_forms):
            raise SystemExit(f"proof-repl: {spec}: the book has {len(all_forms)} forms")
        return number - 1
    wanted = spec.lower()
    for index, form in enumerate(all_forms):
        if head_and_name(form)[1] == wanted:
            return index
    raise SystemExit(f"proof-repl: no event named {spec!r} "
                     "(`proof_repl.py forms BOOK` lists them; #N names a form by number)")


def select_range(all_forms: list[str], start: str | None = None,
                 until: str | None = None, through: str | None = None) -> range:
    """--from (inclusive), --until (exclusive) or --through (inclusive)."""
    begin = locate(all_forms, start) if start else 0
    if until and through:
        raise SystemExit("proof-repl: --until and --through: choose one")
    end = (locate(all_forms, until) if until else
           locate(all_forms, through) + 1 if through else len(all_forms))
    if end < begin:
        raise SystemExit(f"proof-repl: the range ends (form {end}) before it begins "
                         f"(form {begin + 1})")
    return range(begin, end)


def book_path(book: str) -> Path:
    """books/NAME, books/NAME.lisp, or any file of forms (a scratch file)."""
    for candidate in (Path(book), ROOT / book, ROOT / f"{book}.lisp"):
        if candidate.is_file():
            return candidate.resolve()
    raise SystemExit(f"proof-repl: no book or file {book!r}")


# --- a book's local include graph ------------------------------------------------

def include_graph(root: Path, book: str) -> dict[str, list[str]]:
    """Each book of BOOK's local closure -> the books it includes directly."""
    graph: dict[str, list[str]] = {}
    pending = [book]
    base = root.resolve()
    while pending:
        name = pending.pop()
        if name in graph:
            continue
        source = base / f"{name}.lisp"
        if not source.is_file():
            raise certs.UnreadableBook(f"{name}.lisp: missing")
        digest, references = certs.book_facts(source)
        graph[name] = certs._include_targets(base, name, source, digest, references)
        pending.extend(graph[name])
    return graph


def dependents_of(graph: dict[str, list[str]], seeds) -> set[str]:
    """The seeds and every book of the graph that transitively includes one."""
    seeds = set(seeds)
    memo: dict[str, bool] = {}

    def reaches(name: str) -> bool:
        if name not in memo:
            memo[name] = False  # the include graph is acyclic; this guards a bad one
            memo[name] = name in seeds or any(reaches(child) for child in graph.get(name, ()))
        return memo[name]

    return {name for name in graph if reaches(name)}


def dependency_order(graph: dict[str, list[str]], subset) -> list[str]:
    """SUBSET, each book after every book of SUBSET it includes."""
    subset = set(subset)
    order: list[str] = []
    seen: set[str] = set()

    def visit(name: str) -> None:
        if name in seen:
            return
        seen.add(name)
        for child in sorted(graph.get(name, ())):
            visit(child)
        if name in subset:
            order.append(name)

    for name in sorted(subset):
        visit(name)
    return order


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


# --- what ACL2 says a form cost ------------------------------------------------

# A summary's `Time:` is ACL2's run time (get-internal-time is run time unless
# get-internal-time-as-realtime is set), and the prover step count does not
# depend on the machine at all: under hbox load 15-21 the elapsed seconds of
# one form varied 2-5x while both of these stayed put.
SUMMARY_TIME = re.compile(r"^\s*Time:\s+([0-9.]+) seconds", re.MULTILINE)
SUMMARY_STEPS = re.compile(r"^\s*Prover steps counted:\s+(More than\s+)?([0-9,]+)",
                           re.MULTILINE)


def measure(output: str) -> dict:
    """ACL2's own account of one form: its last summary's Time and prover steps.

    An enclosing event (encapsulate, make-event, must-fail, progn) prints its
    summary after its inner events' and counts them, so the last summary is
    the form's; summing them would count the inner events twice.  None when
    the form printed no summary (a query, a suppressed include-book).
    """
    times = SUMMARY_TIME.findall(output)
    steps = SUMMARY_STEPS.findall(output)
    return {"time": float(times[-1]) if times else None,
            "steps": int(steps[-1][1].replace(",", "")) if steps else None,
            "steps_capped": bool(steps and steps[-1][0]),
            "summaries": len(times)}


def cost_words(cost: dict, elapsed: float | None = None) -> str:
    time_word = f"{cost['time']:.2f} s" if cost.get("time") is not None else "-"
    if cost.get("steps") is None:
        steps_word = "-"
    else:
        steps_word = (">" if cost.get("steps_capped") else "") + f"{cost['steps']:,}"
    words = f"ACL2 time {time_word}; prover steps {steps_word}"
    return words + (f"; elapsed {elapsed:.1f} s" if elapsed is not None else "")


class Totals:
    """The costs of a multi-form send, summed over the forms that printed one."""

    def __init__(self):
        self.forms = 0
        self.refused = 0
        self.time = 0.0
        self.steps = 0
        self.elapsed = 0.0
        self.costs: list[tuple[str, dict]] = []

    def add(self, label: str, cost: dict, elapsed: float | None, refused: bool) -> None:
        self.forms += 1
        self.refused += int(refused)
        self.time += cost.get("time") or 0.0
        self.steps += cost.get("steps") or 0
        self.elapsed += elapsed or 0.0
        self.costs.append((label, cost))

    def line(self) -> str:
        return (f"[total: {self.forms} forms, {self.refused} refused; "
                f"ACL2 time {self.time:.2f} s; prover steps {self.steps:,}; "
                f"elapsed {self.elapsed:.1f} s]")

    def slowest(self, count: int = 5) -> list[str]:
        ranked = sorted((item for item in self.costs if item[1].get("steps")),
                        key=lambda item: item[1]["steps"], reverse=True)[:count]
        return [f"  {cost_words(cost)}  {label}" for label, cost in ranked]


# --- trimming what ACL2 printed ------------------------------------------------

HEAD_LINES = 25   # accumulated-persistence and pso put the most important first
TAIL_LINES = 120  # the key checkpoints and the summary
ANCHOR_MARKS = ("ACL2 Error", "HARD ACL2 ERROR")
# Forms whose whole output is the answer: trimming them misleads (a trimmed
# show-accumulated-persistence once showed only the least-used rules).
DIAGNOSTIC_HEADS = frozenset((
    "show-accumulated-persistence", "pso", "pso!", "psof", "pe", "pe!", "pbt",
    "pcb", "pcb!", "pc", "pcs", "pr", "pr!", "pl", "pl2", "pf", "props",
    "show-bodies", "pgs", "print-gv", "puff*"))


def form_head(form: str) -> str:
    """`pso` for `:pso`, `(pso)` or `(pso!)` -> `pso!`; the operator of a form."""
    text = form.strip().lstrip("('").lstrip()
    word = re.split(r"[\s()]", text, maxsplit=1)[0] if text else ""
    return word.lstrip(":").lower()


def wants_full(form: str) -> bool:
    return form_head(form) in DIAGNOSTIC_HEADS


def output_lines(output: str) -> list[str]:
    return [line for line in output.splitlines() if line.strip() not in ("ACL2 !>", "")]


def _anchored(line: str) -> bool:
    return (line.startswith("*** Key checkpoint") or line.startswith("Summary")
            or any(mark in line for mark in ANCHOR_MARKS))


def kept_lines(lines: list[str], keep: int = 60, head: int = HEAD_LINES,
               tail: int = TAIL_LINES) -> list[int]:
    """Which lines a trimmed answer shows: the head, then checkpoints and summary."""
    count = len(lines)
    if count <= keep:
        return list(range(count))
    kept = set(range(min(head, count)))
    anchors = [i for i in range(head, count) if _anchored(lines[i])]
    if not anchors:
        kept.update(range(max(head, count - keep), count))
        return sorted(kept)
    first = anchors[0]
    if count - first <= tail:
        kept.update(range(first, count))
        return sorted(kept)
    # A long anchored stretch: its start (the first checkpoints) and its end
    # (the last summary onward, which carries the verdict and the cost).
    summaries = [i for i in anchors if lines[i].startswith("Summary")]
    end_start = max(summaries[-1] if summaries else count - tail // 2, count - tail // 2)
    kept.update(range(first, first + tail - (count - end_start)))
    kept.update(range(end_start, count))
    return sorted(kept)


def cut_note(first: int, last: int, where: str | None) -> str:
    """Zero-based inclusive [first, last] of the lines not shown."""
    number = last - first + 1
    note = (f"[... {number} line{'s' if number != 1 else ''} cut "
            f"(lines {first + 1}-{last + 1} of this answer); --full prints everything")
    if where:
        note += f"; or: sed -n '{first + 1},{last + 1}p' {where}"
    return note + " ...]"


def brief(output: str, keep: int = 60, where: str | None = None) -> str:
    """The head, the checkpoints and the summary, saying what was cut and where it is."""
    lines = output_lines(output)
    rendered: list[str] = []
    previous = -1
    for index in kept_lines(lines, keep):
        if index != previous + 1:
            rendered.append(cut_note(previous + 1, index - 1, where))
        rendered.append(lines[index])
        previous = index
    if previous != len(lines) - 1:
        rendered.append(cut_note(previous + 1, len(lines) - 1, where))
    return "\n".join(rendered)


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


def default_lane(root: Path | None = None) -> str | None:
    """$FN_LANE, else the lane the tree's path names.

    build/lanes/NAME on the laptop; on persvati a lane's REPL tree is
    ~/fn-gates/NAME-repl (or NAME-rN, NAME-devrepl), so the suffix goes.
    """
    configured = os.environ.get("FN_LANE")
    if configured:
        return configured
    root = root or ROOT
    if root.parent.name == "lanes":
        return root.name
    if root.parent.name == "fn-gates":
        return re.sub(r"-(repl|devrepl|dev|r[0-9]+)$", "", root.name) or None
    return None


class _Terminated(Exception):
    pass


def _on_term(_number, _frame) -> None:
    raise _Terminated()


def load_book(acl2: Acl2, book: str, state: dict, load_timeout: float,
              skip: set[str], stop_before: str = "", stop_after: str = "",
              record: bool = True) -> bool:
    """Send one book's forms after setting the connected book directory to it.

    Local includes of SKIP (books this session loads from source) are not
    sent: their events are already here, and including the uncertified file
    would process it again.  Answers False at the first refused form, having
    recorded where in STATE.
    """
    source = ROOT / f"{book}.lisp"
    text = source.read_text(encoding="utf-8")
    where = "" if record else f"{book}: "
    output, timed_out = acl2.send(f'(set-cbd "{source.parent}/")', load_timeout)
    if timed_out or errored(output):
        state["stopped_at"] = where + "set-cbd"
        state["error"] = "load timed out" if timed_out else brief(output)
        return False
    for number, form in enumerate(forms(text), 1):
        head, event = head_and_name(form)
        if stop_before and (event == stop_before or stop_before == f"#{number}"):
            break
        if include_target(form, source.parent) in skip:
            continue
        output, timed_out = acl2.send(form, load_timeout)
        if timed_out or errored(output):
            state["stopped_at"] = where + (event or head)
            state["error"] = ("load timed out" if timed_out else brief(output))
            state["load_timed_out"] = timed_out
            return False
        cost = measure(output)
        load = state.setdefault("load_cost", {"time": 0.0, "steps": 0, "slowest": []})
        load["time"] = round(load["time"] + (cost["time"] or 0.0), 2)
        load["steps"] += cost["steps"] or 0
        if cost["steps"]:
            load["slowest"] = sorted(load["slowest"] + [[where + (event or head), cost["time"],
                                                         cost["steps"]]],
                                     key=lambda item: item[2], reverse=True)[:5]
        if record:
            state["loaded"].append(event or head)
        else:
            state["ld_loaded"][book] = state["ld_loaded"].get(book, 0) + 1
        if stop_after and (event == stop_after or stop_after == f"#{number}"):
            break
    return True


def serve(name: str, book: str, upto: str | None, through: str | None,
          limit: float, load_timeout: float, lock_fd: int,
          lane: str | None = None, idle_seconds: float = DEFAULT_IDLE_SECONDS,
          ld: list[str] | None = None) -> int:
    directory = session_dir(name)
    directory.mkdir(parents=True, exist_ok=True)
    state_path = directory / "state.json"
    sock_path = directory / "sock"
    now = time.time()
    ld = list(ld or [])
    state = {"name": name, "book": book, "pid": os.getpid(), "loaded": [],
             "stopped_at": None, "error": None, "ready": False, "sends": 0,
             "lane": lane, "idle_seconds": idle_seconds, "started_at": now,
             "last_active": now, "acl2_pgid": None, "ended": None,
             "upto": upto, "through": through, "ld": ld, "ld_loaded": {}}
    # SIGTERM (reap's fallback) unwinds through the finally below, which
    # kills the owned ACL2 group; without this it would outlive the server.
    signal.signal(signal.SIGTERM, _on_term)

    def save() -> None:
        staged = directory / f".state-{os.getpid()}.tmp"
        staged.write_text(json.dumps(state, indent=1))
        os.replace(staged, state_path)

    acl2 = None
    server = None
    bound = False
    try:
        save()
        acl2 = Acl2(f"proof-repl {name}" + (f" lane {lane}" if lane else ""),
                    directory / "log")
        state["acl2_pgid"] = acl2.pgid
        skip = set(ld)
        loaded = all(load_book(acl2, one, state, load_timeout, skip, record=False)
                     for one in ld)
        if loaded:
            load_book(acl2, book, state, load_timeout, skip,
                      stop_before=(upto or "").lower(), stop_after=(through or "").lower())
        if state.get("load_timed_out"):
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
        if idle_seconds > 0:
            server.settimeout(min(30.0, max(0.05, idle_seconds / 4)))
        while acl2.alive():
            try:
                connection, _ = server.accept()
            except socket.timeout:
                idle = time.time() - state["last_active"]
                if idle >= idle_seconds:
                    state["ended"] = f"idle {int(idle)} s (deadline {idle_seconds:g} s)"
                    break
                continue
            with connection:
                connection.settimeout(None)
                request = json.loads(read_all(connection))
                if request.get("op", "send") == "send":
                    state["last_active"] = time.time()
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
    except _Terminated:
        state["ended"] = "terminated (SIGTERM)"
    finally:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
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

def ask(name: str, request: dict, timeout: float = 3600,
        sock_path: Path | None = None) -> dict:
    sock_path = sock_path or session_dir(name) / "sock"
    if not sock_path.exists():
        raise SystemExit(f"proof-repl: no live session {name!r} (start it first)")
    client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    client.settimeout(timeout)
    client.connect(str(sock_path))
    client.sendall(json.dumps(request).encode("utf-8"))
    client.shutdown(socket.SHUT_WR)
    return json.loads(read_all(client))


def normalize_book(name: str) -> str:
    name = name[:-len(".lisp")] if name.endswith(".lisp") else name
    path = Path(name)
    if path.is_absolute():
        with contextlib.suppress(ValueError):
            name = path.resolve().relative_to(ROOT.resolve()).as_posix()
    return name


def unusable_reason(entries: Path, toolchain: str | None) -> str:
    """Why the cache's entries for one closure key did not install here."""
    metas = [certs.read_meta(directory) for directory in sorted(entries.iterdir())
             if directory.is_dir()]
    identities = sorted({str(meta.get("toolchain_identity") or "none") for meta in metas})
    if toolchain and toolchain not in identities:
        return (f"the cache holds these bytes only for ACL2 toolchain(s) "
                f"{', '.join(one[:8] for one in identities)}, and this ACL2 is "
                f"{toolchain[:8]} (another box's build: certify here, or run where "
                "that toolchain is)")
    return ("the cache holds certificates for these bytes, but none usable here "
            "(their ACL2 certificate alists disagree with the other books' chosen "
            "certificates, or a live worktree's pair)")


def diagnose(graph: dict[str, list[str]], missing: list[str], cache: Path,
             toolchain: str | None = None) -> list[str]:
    """Why the cache has no set: the books whose own bytes are uncertified, and what follows.

    A missing book none of whose missing-set dependencies is missing is a
    root cause: every book it includes is cached, so the key it lacks is its
    own bytes.  The rest are missing only because they include a root cause
    (a closure key hashes every included book's bytes).
    """
    lost = set(missing)
    roots = [name for name in sorted(lost) if not set(graph.get(name, ())) & lost]
    follow = sorted(lost - set(roots))
    lines = [f"proof-repl: no cached certificate for {len(lost)} of this book's "
             f"dependencies at this tree's bytes (cache {cache}):"]
    default = Path(certs.DEFAULT_CACHE).expanduser()
    for name in roots:
        source = ROOT / f"{name}.lisp"
        try:
            digest = certs.book_facts(source)[0]
            key = certs.closure_key(ROOT, name)[0]
        except (OSError, ValueError) as error:
            lines.append(f"  {name}: unreadable: {error}")
            continue
        if (cache / key).is_dir():
            why = unusable_reason(cache / key, toolchain)
        else:
            why = "no certificate for these bytes was ever published to this cache"
        lines.append(f"  {name}.lisp sha256 {digest[:16]}: {why}")
        if source.with_suffix(".cert").is_file():
            lines.append(f"    a local {name}.cert exists, but no passing manifest under "
                         f"{certs.MANIFEST_GLOB} vouches for it at these bytes")
        if default.resolve() != cache.resolve() and (default / key).is_dir():
            lines.append(f"    {default} holds this key: the certificate went to the "
                         f"default cache (FN_CERT_CACHE={default} would find it)")
    if follow:
        lines.append(f"  missing because they include one of the above ({len(follow)}): "
                     + ", ".join(follow))
    return lines


def certify_command(books: list[str], jobs: int) -> list[str]:
    command = [sys.executable, str(ROOT / "tools" / "certify_books.py"), "--incremental",
               "--jobs", str(jobs), *books]
    wrapper = shutil.which("swarm-build")
    return ([wrapper] + command) if wrapper else command


def fixes(missing: list[str], jobs: int) -> list[str]:
    roots = " ".join(missing)
    return [
        "fix, one of:",
        "  start ... --certify-missing   certify them here first (publishes to the cache):",
        "      " + " ".join(certify_command(missing, jobs)).replace(
            str(ROOT) + "/", "").replace(sys.executable, "python3").replace(
            str(shutil.which("swarm-build")), "swarm-build"),
        "  start ... --source-deps       load them from source in the session (their proofs",
        "                                run in it; that is not a certificate)",
        f"  start ... --ld BOOK           load one named dependency from source (the books of "
        f"the closure that include it follow); missing: {roots}",
    ]


def install_closure(book: str, ld=(), auto: str | None = None, jobs: int = 4,
                    log: Path | None = None) -> tuple[bool, str, list[str]]:
    """Acquire the dependencies under the same ACL2 used by the REPL child.

    Answers (acquired, what to print, the books to load from source in
    dependency order).  LD names dependencies to load from source instead of
    from certificates; every book of the closure that includes one of them
    is loaded from source too, since its certificate names the other bytes.
    On a miss, pairs a passing manifest in this tree vouches for are published
    first (so a lane's own `certify_books.py` run counts); then AUTO says what
    to do with what is still missing: "ld" loads it from source, "certify"
    certifies it with `certify_books.py --incremental` and tries again, and
    None refuses with the diagnosis.
    """
    try:
        graph = include_graph(ROOT, book)
    except (OSError, certs.UnreadableBook, ValueError) as error:
        return False, f"proof-repl: cannot read {book}'s closure: {error}", []
    wanted = [normalize_book(name) for name in ld]
    outside = [name for name in wanted if name not in graph or name == book]
    if outside:
        return False, ("proof-repl: --ld names books outside this book's dependencies: "
                       + ", ".join(outside)), []
    printed: list[str] = []
    configured = os.environ.get("FN_ACL2", "acl2")
    found = (configured if "/" in configured else shutil.which(configured))
    if not found:
        return False, f"proof-repl: no ACL2 executable at {configured!r}", []
    acl2 = Path(found).expanduser().resolve()
    fingerprint = None
    cache = certs.cache_directory()

    def attempt(from_source: set[str], purge: bool):
        nonlocal fingerprint
        required = set(graph) - from_source - {book}
        if not required:
            return None, required
        if fingerprint is None:
            fingerprint = acl2_toolchain.fingerprint(acl2)
        if not fingerprint.qualified or fingerprint.identity is None:
            raise ValueError("unqualified ACL2 launcher/core/runtime: " + fingerprint.reason)
        # The alist probe starts ACL2 directly. Hold the same machine-wide
        # slot that the subsequent interactive wrapper will take.
        with acl2_slots.slot(f"proof-repl cache {book}"):
            if from_source:
                # What stays is closed under includes: a book that includes a
                # from-source book is itself from source.
                return certs.install_artifact_set(
                    ROOT, cache, sorted(required), toolchain_identity=fingerprint.identity,
                    purge_on_miss=purge, acl2=acl2), required
            return certs.install_artifact_set(
                ROOT, cache, [book], toolchain_identity=fingerprint.identity,
                dependencies_only=True, purge_on_miss=purge, acl2=acl2), required

    from_source = dependents_of(graph, wanted) - {book}
    try:
        report, required = attempt(from_source, purge=False)
        if report is not None and report.artifact_set is None:
            published = certs.publish(ROOT, cache, names=sorted(report.uncached))
            if published.published:
                printed.append(f"proof-repl: published {published.published} certificate(s) "
                               "this tree's own manifests vouch for; trying again")
                report, required = attempt(from_source, purge=False)
        if report is not None and report.artifact_set is None and auto == "certify":
            missing = sorted(report.uncached)
            command = certify_command(missing, jobs)
            printed.append("proof-repl: certifying the missing dependencies: "
                           + " ".join(missing))
            with open(log or os.devnull, "a", encoding="utf-8") as sink:
                done = subprocess.run(command, cwd=ROOT, stdout=sink, stderr=subprocess.STDOUT)
            printed.append(f"  certify_books.py exit {done.returncode}"
                           + (f"; log {log}" if log else ""))
            report, required = attempt(from_source, purge=False)
        if report is not None and report.artifact_set is None and auto == "ld":
            from_source |= dependents_of(graph, report.uncached) - {book}
            printed.append("proof-repl: loading from source (proofs run in the session): "
                           + ", ".join(dependency_order(graph, from_source)))
            report, required = attempt(from_source, purge=False)
        if report is not None and report.artifact_set is None:
            missing = sorted(report.uncached)
            # The refusal keeps the old contract: no local pair of the closure
            # survives a miss to stand in for a certificate later.
            attempt(from_source, purge=True)
            return False, "\n".join(printed + diagnose(
                graph, missing, cache, fingerprint.identity if fingerprint else None)
                + fixes(missing, jobs)), []
    except ValueError as error:
        if "unqualified" in str(error):
            return False, "proof-repl: " + str(error), []
        return False, f"proof-repl: certificate acquisition failed: {error}", []
    except (OSError, subprocess.TimeoutExpired) as error:
        return False, f"proof-repl: certificate acquisition failed: {error}", []
    order = dependency_order(graph, from_source)
    if report is None:
        printed.append("no dependencies to install")
    else:
        printed.extend(report.lines())
    if order:
        printed.append("from source, in this order: " + ", ".join(order))
    return True, "\n".join(printed), order


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
        named = list(getattr(args, "ld", None) or ())
        source_deps = getattr(args, "source_deps", None)
        if source_deps and source_deps != "*":
            named += [one.strip() for one in source_deps.split(",") if one.strip()]
        auto = ("certify" if getattr(args, "certify_missing", False) else
                "ld" if getattr(args, "ld_missing", False) or source_deps == "*" else None)
        SESSIONS.mkdir(parents=True, exist_ok=True)
        acquired, detail, from_source = install_closure(
            args.book, named, auto,
            getattr(args, "certify_jobs", 4), SESSIONS / f"{args.name}.certify.log")
        print(detail)
        if not acquired:
            return 1
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "state.json").unlink(missing_ok=True)
        with open(directory / "server.log", "a", encoding="utf-8") as log:
            command = [sys.executable, __file__, "serve", args.name, args.book,
                       "--limit", str(args.limit), "--load-timeout", str(args.load_timeout),
                       "--lock-fd", str(lock_fd),
                       "--idle-seconds", str(getattr(args, "idle_seconds", DEFAULT_IDLE_SECONDS))]
            lane = getattr(args, "lane", None) or default_lane()
            if lane:
                command += ["--lane", lane]
            if args.upto:
                command += ["--upto", args.upto]
            if args.through:
                command += ["--through", args.through]
            for one in from_source:
                command += ["--ld", one]
            subprocess.Popen(command, stdout=log, stderr=log, cwd=ROOT,
                             start_new_session=True, pass_fds=(lock_fd,))
        deadline = time.monotonic() + args.load_timeout * (3 + 2 * len(from_source)) + 60
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
    for book, count in (state.get("ld_loaded") or {}).items():
        print(f"  from source (not certified): {book}, {count} forms")
    if state["stopped_at"]:
        print(f"  stopped at {state['stopped_at']}:")
        print("  " + (state["error"] or "").replace("\n", "\n  "))
    elif state["loaded"]:
        print(f"  last loaded: {state['loaded'][-1]}")
    load = state.get("load_cost")
    if load:
        print(f"  loading cost ACL2 time {load['time']:.2f} s, prover steps {load['steps']:,}"
              + ("; most steps: " + ", ".join(f"{label} ({steps:,})"
                                               for label, _, steps in load["slowest"])
                 if load.get("slowest") else ""))
    return 0


def save_output(name: str, output: str, tag: str = "") -> str:
    """Keep the whole answer next to the session, so a cut note can name its lines."""
    path = session_dir(name) / f"last-output{tag}.txt"
    try:
        path.write_text("\n".join(output_lines(output)) + "\n", encoding="utf-8")
    except OSError:
        return str(session_dir(name) / "log")
    with contextlib.suppress(ValueError):
        return str(path.relative_to(Path.cwd()))
    return str(path)


def send_one(name: str, form: str, limit: float | None, full: bool) -> int:
    answer = ask(name, {"op": "send", "form": form, "limit": limit})
    output = answer.get("output", "")
    if full or wants_full(form):
        print(output)
    else:
        print(brief(output, where=save_output(name, output)))
    cost = measure(output)
    if cost["summaries"]:
        print(f"[{cost_words(cost)}]")
    if "elapsed" in answer:
        print(f"[{answer['elapsed']} s{', timed out' if answer.get('timed_out') else ''}]")
    return 1 if answer.get("error") else 0


def send_many(name: str, items: list[tuple[str, str]], limit: float | None,
              full: bool = False, keep_going: bool = False) -> int:
    """Each (label, form) in order: one line of cost per form, the output of a refusal.

    Stops at the first refusal unless KEEP_GOING; a form that outlives the
    hard limit kills the session, so nothing after it can be sent.
    """
    totals = Totals()
    for position, (label, form) in enumerate(items, 1):
        answer = ask(name, {"op": "send", "form": form, "limit": limit})
        output = answer.get("output", "")
        refused = bool(answer.get("error"))
        cost = measure(output)
        elapsed = answer.get("elapsed")
        totals.add(label, cost, elapsed, refused)
        print(f"{'REFUSED' if refused else 'ok':8}{label}: {cost_words(cost, elapsed)}",
              flush=True)
        if full or wants_full(form):
            print(output)
        elif refused:
            print(brief(output, where=save_output(name, output, f"-{position}")))
        if answer.get("timed_out"):
            print(f"[{label}: no answer within the hard limit; the session was killed]")
            break
        if refused and not keep_going:
            print(f"[stopped at {label}; after fixing it, resume with --from "
                  f"{label.split()[0]}]")
            break
    print(totals.line())
    slowest = totals.slowest()
    if len(totals.costs) > 1 and slowest:
        print("most prover steps:")
        print("\n".join(slowest))
    return 1 if totals.refused else 0


def send(args) -> int:
    form = args.form if args.form != "-" else sys.stdin.read()
    try:
        several = forms(form)
    except ValueError:
        several = [form]  # the session answers with the parse error
    if len(several) <= 1:
        return send_one(args.name, form, args.limit, args.full)
    items = [(form_label(index, one), one) for index, one in enumerate(several, 1)]
    return send_many(args.name, items, args.limit, args.full,
                     getattr(args, "keep_going", False))


def read_state(name: str) -> dict | None:
    path = session_dir(name) / "state.json"
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return None


def send_range(args) -> int:
    """A book's forms from --from to --until/--through into a live session."""
    path = book_path(args.book)
    all_forms = forms(path.read_text(encoding="utf-8"))
    chosen = select_range(all_forms, args.start, args.until, args.through)
    state = read_state(args.name) or {}
    from_source = set(state.get("ld") or [])
    items, skipped = [], 0
    for index in chosen:
        form = all_forms[index]
        target = include_target(form, path.parent)
        if target is not None and (args.skip_includes or target in from_source):
            skipped += 1
            continue
        items.append((form_label(index + 1, form), form))
    first, last = chosen.start + 1, chosen.stop
    print(f"send-range {args.name}: forms #{first}-#{last} of {args.book} "
          f"({len(items)} to send" + (f", {skipped} local includes skipped" if skipped else "")
          + ")")
    if not items:
        return 0
    return send_many(args.name, items, args.limit, args.full, args.keep_going)


def list_forms(args) -> int:
    path = book_path(args.book)
    for index, form in enumerate(forms(path.read_text(encoding="utf-8")), 1):
        print(form_label(index, form))
    return 0


# --- probing one event beside the session -----------------------------------------

THEOREM_HEADS = ("defthm", "defthmd", "defrule", "defruled")
PROBE_MARK = "fn-probe-mark"


def set_keyword(form: str, keyword: str, value: str) -> str:
    """FORM with the event's KEYWORD argument set to VALUE (replaced or added)."""
    target = 2 if re.match(r"\(\s*local\s*\(", form.strip(), re.IGNORECASE) else 1
    tokens = [token for token in theory_check.TOKEN.finditer(form)
              if token.lastgroup not in ("comment", "block")]
    depth = 0
    for index, token in enumerate(tokens):
        kind = token.lastgroup
        if kind == "open":
            depth += 1
        elif kind == "close":
            if depth == target:
                return form[:token.start()] + f" {keyword} {value}" + form[token.start():]
            depth -= 1
        elif (kind == "atom" and depth == target
              and token.group().lower() == keyword.lower()):
            rest = tokens[index + 1:]
            while rest and rest[0].lastgroup == "quote":
                rest = rest[1:]
            if not rest or rest[0].lastgroup == "close":
                raise ValueError(f"{keyword} has no value")
            start = tokens[index + 1].start()
            if rest[0].lastgroup != "open":
                return form[:start] + value + form[rest[0].end():]
            level = 0
            for inner in rest:
                if inner.lastgroup == "open":
                    level += 1
                elif inner.lastgroup == "close":
                    level -= 1
                    if level == 0:
                        return form[:start] + value + form[inner.end():]
    raise ValueError("not one event form")


def probe_form(form: str, hints: str | None) -> str:
    """The event renamed (a theorem) and with replacement hints."""
    head, event = head_and_name(form)
    if head in THEOREM_HEADS and event:
        match = HEAD.match(form.strip())
        form = form.strip()
        form = form[:match.start(2)] + f"{match.group(2)}-probe" + form[match.end(2):]
    if hints is not None:
        form = set_keyword(form, ":hints", hints)
    return form


def probe_identity(book: str, source_text: str, start: int, from_source: list[str]) -> str:
    """What the probe session was loaded from: the book before EVENT and its closure."""
    closure = certs.closure(ROOT, book)
    closure.pop(book, None)
    material = json.dumps({"prefix": source_text[:start], "closure": sorted(closure.items()),
                           "ld": list(from_source)}, sort_keys=True)
    return hashlib.sha256(material.encode("utf-8")).hexdigest()


def probe(args) -> int:
    """Prove a copy of EVENT in a second session loaded up to just before it."""
    main_state = read_state(args.name) or {}
    book = args.book or main_state.get("book")
    if not book:
        raise SystemExit(f"proof-repl: no session {args.name!r} to take the book from; "
                         "pass --book")
    book = normalize_book(book)
    source = ROOT / f"{book}.lisp"
    text = source.read_text(encoding="utf-8")
    places = spans(text)
    index = locate([text[a:b] for a, b in places], args.event)
    event_form = text[places[index][0]:places[index][1]]
    from_source = list(main_state.get("ld") or []) if not args.book else []
    for extra in args.ld or []:
        if normalize_book(extra) not in from_source:
            from_source.append(normalize_book(extra))
    name = f"{args.name}.probe"
    identity = probe_identity(book, text, places[index][0], from_source)
    marker = session_dir(name) / "probe.json"
    try:
        previous = json.loads(marker.read_text())
    except (OSError, json.JSONDecodeError):
        previous = {}
    probe_state = read_state(name) or {}
    reusable = (previous.get("identity") == identity
                and (session_dir(name) / "sock").exists()
                and probe_state.get("ready") and not probe_state.get("stopped_at"))
    if not reusable:
        if (session_dir(name) / "sock").exists():
            stop(argparse.Namespace(name=name))
        print(f"proof-repl probe: loading {book} up to #{index + 1} "
              f"({form_label(index + 1, event_form)}) in session {name}")
        started = start(argparse.Namespace(
            name=name, book=book, upto=f"#{index + 1}", through=None,
            limit=args.limit or 60.0, load_timeout=args.load_timeout,
            lane=main_state.get("lane") or getattr(args, "lane", None),
            idle_seconds=args.idle_seconds, ld=from_source, ld_missing=False,
            certify_missing=False, certify_jobs=4))
        probe_state = read_state(name) or {}
        if started != 0 or probe_state.get("stopped_at"):
            print(f"proof-repl probe: the session could not load {book} up to the event")
            return 1
        marker.write_text(json.dumps({"identity": identity, "book": book,
                                      "event": args.event}) + "\n")
    else:
        print(f"proof-repl probe: reusing {name} (loaded up to #{index + 1} of {book})")
    replacement = args.form
    if replacement == "-":
        replacement = sys.stdin.read()
    try:
        attempt = probe_form(replacement or event_form, args.hints)
    except ValueError as error:
        raise SystemExit(f"proof-repl probe: cannot set :hints: {error}") from None
    # Everything the probe adds goes with the mark, so the session stays at
    # the event for the next probe, whatever this one did.
    ask(name, {"op": "send", "form": f"(ubt! '{PROBE_MARK})"})
    ask(name, {"op": "send", "form": f"(deflabel {PROBE_MARK})"})
    answer = ask(name, {"op": "send", "form": attempt, "limit": args.limit})
    output = answer.get("output", "")
    print(output if args.full else brief(output, where=save_output(name, output)))
    cost = measure(output)
    refused = bool(answer.get("error"))
    print(f"[probe {form_label(index + 1, event_form)} of {book}: "
          f"{'REFUSED' if refused else 'admitted'}; {cost_words(cost, answer.get('elapsed'))}]")
    if answer.get("timed_out"):
        print(f"[the probe outlived the hard limit; session {name} was killed]")
        return 1
    ask(name, {"op": "send", "form": f"(ubt! '{PROBE_MARK})"})
    if args.stop:
        stop(argparse.Namespace(name=name))
    else:
        print(f"[session {name} stays at the event for the next probe; it stops itself "
              f"after {args.idle_seconds:g} s idle, or: proof_repl.py stop {name}]")
    return 1 if refused else 0


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


def _command_of(pid: int) -> str:
    """The command line of PID, or '' when there is no such process."""
    try:
        answer = subprocess.run(["ps", "-o", "command=", "-p", str(pid)],
                                capture_output=True, text=True, timeout=10)
    except (OSError, subprocess.TimeoutExpired):
        return ""
    return answer.stdout.strip() if answer.returncode == 0 else ""


def _is_server(pid, name: str) -> bool:
    """PID is still this session's `proof_repl.py serve NAME` (not a reused PID)."""
    if not isinstance(pid, int) or pid <= 1:
        return False
    words = _command_of(pid).split()
    return ("serve" in words and name in words
            and any(word.endswith("proof_repl.py") for word in words))


def _is_acl2_group(pgid) -> bool:
    """PGID is still a pooled ACL2 wrapper (tools/acl2) this tool started."""
    if not isinstance(pgid, int) or pgid <= 1:
        return False
    return any(word.endswith("tools/acl2") for word in _command_of(pgid).split())


def session_rows(roots: list[str] | None = None) -> list[dict]:
    """Every session directory's state, with its liveness, age and idle time.

    ``roots`` are other trees (each ROOT/build/proof-repl) to read instead of
    this one's: persvati keeps one tree per lane under ~/fn-gates.
    """
    rows = []
    bases = [Path(root) / "build" / "proof-repl" for root in roots] if roots else [SESSIONS]
    now = time.time()
    directories = [d for base in bases if base.is_dir() for d in sorted(base.iterdir())]
    for directory in directories:
        state_path = directory / "state.json"
        if not state_path.is_file():
            continue
        try:
            state = json.loads(state_path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        saved = state_path.stat().st_mtime
        # Sessions of the older tool carry no clock: their state file is
        # rewritten on every request, so its mtime is the last activity.
        last = state.get("last_active") or saved
        started = state.get("started_at")
        if not started:
            # The older tool: the session's first write was its server.log.
            first = directory / "server.log"
            started = first.stat().st_mtime if first.exists() else saved
        server = _is_server(state.get("pid"), directory.name)
        socket_file = (directory / "sock").exists()
        rows.append({"name": directory.name, "state": state, "directory": directory,
                     "server": server, "socket": socket_file,
                     "live": server and socket_file,
                     "age": now - started,
                     "idle": now - last,
                     "deadline": state.get("idle_seconds")})
    return rows


def _duration(seconds: float) -> str:
    seconds = int(max(0, seconds))
    if seconds >= 86400:
        return f"{seconds // 86400}d{seconds % 86400 // 3600}h"
    if seconds >= 3600:
        return f"{seconds // 3600}h{seconds % 3600 // 60:02d}m"
    return f"{seconds // 60}m{seconds % 60:02d}s"


def list_sessions(args) -> int:
    rows = session_rows(getattr(args, "root", None))
    if not rows:
        print("proof-repl: no sessions")
        return 0
    print(f"{'name':24} {'status':6} {'lane':24} {'age':>7} {'idle':>7} {'deadline':>8} book")
    for row in rows:
        state = row["state"]
        status_word = ("live" if row["live"] else
                       "stale" if row["socket"] else
                       "ended" if state.get("ended") else "dead")
        deadline = row["deadline"]
        print(f"{row['name']:24} {status_word:6} {(state.get('lane') or '-'):24} "
              f"{_duration(row['age']):>7} {_duration(row['idle']):>7} "
              f"{(_duration(deadline) if deadline else 'none'):>8} {state.get('book')}"
              + (f"  [{row['directory'].parent.parent.parent}]" if getattr(args, "root", None) else ""))
    return 0


def reap_reason(row: dict, lane: str | None, older_than: float | None) -> str | None:
    """Why `reap` stops this session, or None to leave it."""
    state = row["state"]
    if lane is not None:
        return f"lane {lane}" if state.get("lane") == lane else None
    if not row["server"]:
        # Nothing to stop but an orphan ACL2 group or a stale socket file.
        if row["socket"] or _is_acl2_group(state.get("acl2_pgid")):
            return "dead server"
        return None
    if older_than is not None and row["idle"] >= older_than:
        return f"idle {_duration(row['idle'])} >= {older_than:g} s"
    deadline = row["deadline"]
    if deadline and row["idle"] >= deadline + 120:
        return f"past its own idle deadline ({_duration(deadline)})"
    return None


def reap_one(row: dict) -> str:
    """Stop one session: its own `stop` first, then only the PIDs its state names."""
    name, state = row["name"], row["state"]
    if row["server"] and row["socket"]:
        try:
            if ask(name, {"op": "stop"}, timeout=30,
                   sock_path=row["directory"] / "sock").get("stopped"):
                return "stopped through its socket"
        except (SystemExit, OSError, ValueError):
            pass
    signalled = []
    if row["server"] and _is_server(state.get("pid"), name):
        with contextlib.suppress(ProcessLookupError, PermissionError):
            os.kill(state["pid"], signal.SIGTERM)
            signalled.append(f"server {state['pid']}")
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline and _is_server(state.get("pid"), name):
            time.sleep(0.1)
    pgid = state.get("acl2_pgid")
    if _is_acl2_group(pgid):
        with contextlib.suppress(ProcessLookupError, PermissionError):
            os.killpg(pgid, signal.SIGTERM)
            signalled.append(f"ACL2 group {pgid}")
    if not _is_server(state.get("pid"), name):
        (row["directory"] / "sock").unlink(missing_ok=True)
    return ("signalled " + ", ".join(signalled)) if signalled else "removed a stale socket"


def reap(args) -> int:
    rows = session_rows(args.root)
    chosen = [(row, reason) for row in rows
              for reason in [reap_reason(row, args.lane, args.older_than)] if reason]
    if not chosen:
        print("proof-repl: nothing to reap")
        return 0
    for row, reason in chosen:
        lane = row["state"].get("lane") or "-"
        if args.dry_run:
            print(f"would reap {row['name']} (lane {lane}): {reason}")
            continue
        print(f"reaped {row['name']} (lane {lane}): {reason}; {reap_one(row)}")
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
    p.add_argument("--lane", default=None,
                   help="the owning lane (default $FN_LANE, else build/lanes/NAME)")
    p.add_argument("--idle-seconds", type=float, default=DEFAULT_IDLE_SECONDS,
                   help="stop the session after this long with no send "
                        f"(default {DEFAULT_IDLE_SECONDS:g}; 0: never)")
    p.add_argument("--ld", action="append", default=[], metavar="BOOK",
                   help="load this dependency from source, not from a certificate "
                        "(repeatable); the closure's books that include it follow")
    p.add_argument("--ld-missing", action="store_true",
                   help="load every dependency the cache lacks from source")
    p.add_argument("--source-deps", nargs="?", const="*", default=None, metavar="A,B",
                   help="load these dependencies (comma-separated) from source; bare: "
                        "every one the cache lacks (the same as --ld-missing)")
    p.add_argument("--certify-missing", action="store_true",
                   help="certify every dependency the cache lacks here first "
                        "(certify_books.py --incremental, under swarm-build when present)")
    p.add_argument("--certify-jobs", type=int, default=4,
                   help="--jobs for --certify-missing (default 4)")
    p.set_defaults(run=start)
    p = sub.add_parser("serve")
    p.add_argument("name")
    p.add_argument("book")
    p.add_argument("--upto", default=None)
    p.add_argument("--through", default=None)
    p.add_argument("--limit", type=float, default=60.0)
    p.add_argument("--load-timeout", type=float, default=600.0)
    p.add_argument("--lock-fd", type=int, required=True)
    p.add_argument("--lane", default=None)
    p.add_argument("--idle-seconds", type=float, default=DEFAULT_IDLE_SECONDS)
    p.add_argument("--ld", action="append", default=[])
    p.set_defaults(run=lambda a: serve(a.name, a.book, a.upto, a.through, a.limit,
                                       a.load_timeout, a.lock_fd, a.lane, a.idle_seconds,
                                       a.ld))
    p = sub.add_parser("send", help="forms (one or several); `-` reads them from stdin")
    p.add_argument("name")
    p.add_argument("form")
    p.add_argument("--limit", type=float, default=None)
    p.add_argument("--full", action="store_true", help="everything ACL2 printed")
    p.add_argument("--keep-going", action="store_true",
                   help="several forms: send the rest after a refusal")
    p.set_defaults(run=send)
    p = sub.add_parser("send-range", help="a book's forms from one event to another, "
                                          "with ACL2 time and prover steps per form")
    p.add_argument("name")
    p.add_argument("book", help="books/NAME (.lisp optional) or any file of forms")
    p.add_argument("--from", dest="start", default=None, metavar="EVENT",
                   help="first form: an event name or #N (default: the first)")
    p.add_argument("--until", default=None, metavar="EVENT",
                   help="stop before this event (or #N)")
    p.add_argument("--through", default=None, metavar="EVENT",
                   help="stop after this event (or #N)")
    p.add_argument("--limit", type=float, default=None)
    p.add_argument("--full", action="store_true", help="every form's whole output")
    p.add_argument("--keep-going", action="store_true",
                   help="report every refusal instead of stopping at the first")
    p.add_argument("--skip-includes", action="store_true",
                   help="skip every local include-book form (the session's own "
                        "from-source books are always skipped)")
    p.set_defaults(run=send_range)
    p = sub.add_parser("forms", help="number and name a book's top-level forms (#N)")
    p.add_argument("book")
    p.set_defaults(run=list_forms)
    p = sub.add_parser("probe", help="prove a copy of EVENT in a second session loaded up "
                                     "to just before it; the session NAME is untouched")
    p.add_argument("name")
    p.add_argument("event", help="an event name or #N of the book")
    p.add_argument("--book", default=None, help="default: session NAME's book")
    p.add_argument("--hints", default=None,
                   help="replacement :hints value, e.g. '((\"Goal\" :in-theory (enable f)))'")
    p.add_argument("--form", default=None,
                   help="prove this form (or `-`: stdin) at the event's place instead")
    p.add_argument("--ld", action="append", default=[], metavar="BOOK",
                   help="also load this dependency from source")
    p.add_argument("--limit", type=float, default=None)
    p.add_argument("--load-timeout", type=float, default=600.0)
    p.add_argument("--idle-seconds", type=float, default=1800.0,
                   help="the probe session stops itself after this long idle (default 1800)")
    p.add_argument("--full", action="store_true")
    p.add_argument("--stop", action="store_true", help="stop the probe session afterwards")
    p.set_defaults(run=probe)
    p = sub.add_parser("status")
    p.add_argument("name")
    p.set_defaults(run=status)
    p = sub.add_parser("stop")
    p.add_argument("name")
    p.set_defaults(run=stop)
    p = sub.add_parser("list", help="each session's lane, age, idle time and deadline")
    p.add_argument("--root", action="append", default=None, metavar="TREE",
                   help="read TREE/build/proof-repl instead of this tree's (repeatable)")
    p.set_defaults(run=list_sessions)
    p = sub.add_parser("reap", help="stop dead, overdue or a lane's sessions")
    p.add_argument("--lane", default=None, help="every session tagged with this lane")
    p.add_argument("--older-than", type=float, default=None, metavar="S",
                   help="live sessions idle at least S seconds")
    p.add_argument("--dry-run", action="store_true", help="say what would be reaped")
    p.add_argument("--root", action="append", default=None, metavar="TREE",
                   help="reap in TREE/build/proof-repl instead of this tree's (repeatable)")
    p.set_defaults(run=reap)
    args = parser.parse_args(argv)
    return args.run(args)


if __name__ == "__main__":
    raise SystemExit(main())

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
                                          # --until EXCLUDES its event; --through sends it
    proof_repl.py send-file NAME tests/acl2/X-tests.lisp [--keep-going]
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
neither session moves.  The probe loads the book FILE: an event sent to NAME
by hand is not in it (it names them; `--with-sent` sends them first); `status` reports the load's time and steps and its
costliest forms.

A dependency the cache has no certificate for at this tree's bytes: `start`
first publishes any pair this tree's own manifests vouch for (a lane's own
`certify_books.py` run), then refuses naming each book whose own bytes are
uncertified, the books that miss only because they include one, and the
fixes: `--certify-missing` certifies them (certify_books.py --incremental,
under swarm-build where it exists) and starts; `--source-deps` (or
`--ld-missing`) loads them from source in the session; `--ld DEPENDENCY`
(a book the session's book includes, never the book itself) / `--source-deps
A,B` loads named ones.  A from-source book's proofs run in the
session and `status` marks it "from source (not certified)"; the books of the
closure that include it are loaded from source too, since their
certificates name its other bytes.

Source loading never implicitly launches certification. If a dependency
fails from source, fix the source/world or explicitly choose
`start --certify-missing`. Sent includes may acquire matching cached
certificates, but a cache miss is refused; certification is a separate
explicit operation.

Round 2 (2026-09-27): a keyword command (`:ubt! foo`) is one command with
the rest of its line, and when a keyword command or a raw-Lisp abort
swallows the sentinel it is sent again after 3 s of quiet, so neither hangs
the session.  `probe` checks its session's checkpoint (label fn-probe-base
and the world's command number) before and after each attempt, undoes what
is above it with `ubu!`, and reloads when it cannot; `--form` takes several
forms.  `stop NAME` also ends a start still loading with no socket (the
lock file names its holder).  `start` loads from-source books (`--ld`,
`--source-deps`, `--ld-missing`) inside one encapsulate so their local
events stay local -- the default since obstructions-5 item 32
(store-log-extend's local lemmas turned global form by form); `--ld-leak`
loads form by form, which names the refused event.  `--host BOX`
(hbox, persvati) runs a command in the lane's tree on that box with the
box's own ACL2 and cache after syncing tools/ and the book's closure; on a
box itself FN_ACL2 and FN_CERT_CACHE default to that box's.  Before that
sync a `start` names the closure's books this branch changed (against the
merge base with origin/dev) and loads them from source as `--ld` (item 82);
a second live session of the lane on the box gets its own tree
<lane>-repl-<NAME> (item 79); a bare book name (`--ld store-log`) resolves
under books/ (item 78).  A `send` that loads a host file (`(ld "host/x.lisp")`)
syncs it to the box first, and a second host load in one session is refused
by name, since such a session died in a fasl load (item 84).

Round 3 (lane tooling-leftovers, 2026-09-27): `start` sends each of the
book's events under `with-prover-time-limit` too (`--load-limit S`, default
`--limit`, 0 = none), so a runaway lemma is refused with its checkpoints in
`status` (and the whole answer in build/proof-repl/NAME/load-refusal.txt)
instead of holding the session for ten minutes; the session stays live just
before it for `probe`/`send`.  `--ld-local` sends a from-source book's
non-local `include-book` and `defpkg` forms before its encapsulate, since
ACL2 refuses both inside one; local includes stay inside.  A pair installed
from the cache is dated no earlier than its source (tools/certs.py
`date_after_source`), so `certify_books.py --pcert` completes over a closure
`--certify-missing` or an install put in place.

Round 4 (lane-tools-1, 2026-09-28, the lanes' LANEDUMP asks): `--acl2 PATH`
(else FN_ACL2) picks the ACL2, also on a --host box (hbox's
acl2-literal-4g-tls64k when an image world exhausts thread-local storage);
`send-range --no-sync` refuses when the box's copy is not this tree's;
send-range names every form it skips and counts the `(local ...)` forms it
sends at the top level (whose events stay in the session), and its
`--ld-local` sends the range inside one encapsulate; `resync NAME BOOK --from
EVENT` undoes the session through what it holds from EVENT on and resends from
EVENT, or from the first earlier event its world lacks; a refusal is judged by
the form's own result (a must-fail that caught an `er hard` is not refused);
a form that took long for few prover steps says so; `status` warns that a
book loaded form by form from source leaks its local theory; the reader
knows character literals (#\\( #\\") and |bar symbols|.

Round 5 (lane laptop-acl2, 2026-09-28): the laptop is a REPL target.  Its
Homebrew `saved_acl2` splices `${SBCL_USER_ARGS}` (unqualified, and
--tls-limit 16384); the machine file ~/.config/fn/acl2 names a literal
launcher with the boxes' flags over an ACL2 8.7 built from the boxes'
tarball, and a session run here without --host uses it
(`acl2_slots.configured_acl2`).  `--host laptop` runs here; `--host auto`
starts here when that launcher qualifies, one of this machine's pool slots
is free, and this machine's load per core is below the chosen box's
(FN_REPL_LAPTOP=0 never picks it).  Only REPL sessions: the farm,
remote_check and `boxes.sh --pick` never pick the laptop, and a laptop
`start --certify-missing` certifies the closure into this machine's cache
under its own toolchain identity (box certificates are keyed by theirs).

Round 6 (lane tooling-obstructions, 2026-09-28): `start --host BOX` on a box
another lane reserved names the holder and expiry at once and waits only
for a lease ending within `--lease-wait` minutes (default 2), else refuses;
`--host auto` passes over the laptop when its cache lacks any of the book's
dependencies; a remote start records its box before it runs
(build/proof-repl/NAME/remote.json), and send/send-range/resync/status/
stop/probe without --host go there (`--host laptop` runs here), into the
lane tree the record names -- no FN_LANE needed after `start`.

A session holds one slot of the machine's ACL2 pool for its whole life, so
it belongs to its lane and ends with it (PKT-346: fifteen finished lanes'
sessions once held fifteen of persvati's sixteen slots).  `start` records
the lane (`--lane`, else $FN_LANE, else the worktree's name under
build/lanes/, or persvati's ~/fn-gates/NAME-repl) and an idle deadline.

Idle timeout (post-alloc-3, 2026-09-27: hbox's 22 slots were held mostly by
other lanes' idle sessions under the old 2-hour default):

    proof_repl.py start NAME BOOK --idle-timeout 90    # minutes; 0 = never
    FN_REPL_IDLE_MIN=90 proof_repl.py start NAME BOOK  # the same, as a default
    proof_repl.py reap --idle 60 [--dry-run] [--host hbox]
    proof_repl.py gc [--each-box] [--dry-run]           # reap --idle 30 in every tree;
                                                         # the batch runner runs it each cycle
    proof_repl.py diff NAME BOOK [--all]   # events whose session form is not the book's
    proof_repl.py send NAME '(a) (b)' --keep-going   # send the rest after a refusal

A session with no form sent for 20 minutes (the default) stops itself: ACL2
exits (its pool slot with it), the socket goes, and the session directory
keeps `stopped.json`, so a later `send` answers "session NAME stopped after
N min idle; start it again" instead of "no live session".  Every command
that runs forms resets the clock (send, send-range, a probe -- which also
touches the session it probes beside); `status`, `list` and `reap` do not.
Before a long wait between sends (a farm run, an hbox_native run), start
with a longer `--idle-timeout` or 0.  (`--idle-seconds S` overrides in
seconds; the tests use it.)  `status` prints the time since the last send
and when the session stops; `list` prints each session's lane, age, idle
time, deadline and time left.

`reap` stops the sessions this tool started that are dead, past their own
deadline, idle longer than `--idle MIN` (or `--older-than S`), or tagged
`--lane NAME` (the coordinator runs `reap --lane NAME` when it merges that
lane).  `--idle` and `--all` read every session tree on the machine: this
tree, the main checkout's build/lanes/*, and /tank/fn/gates/*,
/tank/fn/scratch/* and ~/fn-gates/* (each TREE/build/proof-repl/NAME),
and, where /proc exists, the working tree of every running server (a
deeper scratch tree, or a lane that exported its path as FN_LANE -- now
read as its basename); `--root TREE` names trees instead.  It signals only the PIDs a session's
state names, after checking each is still that session's `proof_repl.py
serve NAME` (and, where /proc exists, that its working directory is that
session's tree); never by pattern.  A reaped session keeps a
`stopped.json` naming why.
"""
from __future__ import annotations

import argparse
import contextlib
import fcntl
import fractions
import hashlib
import json
import os
from pathlib import Path
import queue
import re
import shutil
import shlex
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
# A session with no `send` for this long stops itself (see the header);
# FN_REPL_IDLE_MIN (minutes, 0 = never) changes the default.
DEFAULT_IDLE_MINUTES = 20.0
STOP_NOTE = "stopped.json"
# Where session trees live on a machine, besides this tree and the main
# checkout's build/lanes/* (reap --idle / --all).
BOX_TREE_BASES = ("/tank/fn/gates", "/tank/fn/scratch", "~/fn-gates")


def default_idle_seconds(environ=os.environ) -> float:
    """The idle deadline a session gets unless told otherwise, in seconds."""
    configured = environ.get("FN_REPL_IDLE_MIN", "").strip()
    if configured:
        try:
            minutes = float(configured)
        except ValueError:
            raise SystemExit(f"proof-repl: FN_REPL_IDLE_MIN={configured!r} is not a "
                             "number of minutes") from None
        return max(0.0, minutes) * 60
    return DEFAULT_IDLE_MINUTES * 60


def idle_from_args(args, fallback: float | None = None) -> float:
    """--idle-timeout MIN wins, then --idle-seconds S, then the default."""
    minutes = getattr(args, "idle_timeout", None)
    if minutes is not None:
        return max(0.0, minutes) * 60
    seconds = getattr(args, "idle_seconds", None)
    if seconds is not None:
        return max(0.0, seconds)
    return default_idle_seconds() if fallback is None else fallback


def write_stop_note(directory: Path, reason: str, idle: float | None,
                    deadline: float | None, by: str) -> None:
    """Leave why the session ended, for the next `send` and `status`."""
    note = {"reason": reason, "idle": idle, "deadline": deadline, "by": by,
            "at": time.time()}
    with contextlib.suppress(OSError):
        staged = directory / f".{STOP_NOTE}-{os.getpid()}.tmp"
        staged.write_text(json.dumps(note) + "\n")
        os.replace(staged, directory / STOP_NOTE)


def read_stop_note(directory: Path) -> dict | None:
    try:
        return json.loads((directory / STOP_NOTE).read_text())
    except (OSError, json.JSONDecodeError):
        return None


def stop_note_words(name: str, note: dict) -> str:
    idle = note.get("idle")
    when = time.strftime("%Y-%m-%d %H:%M:%S %Z", time.localtime(note.get("at") or 0))
    if note.get("reason") == "idle" and idle is not None:
        head = f"session {name} stopped after {idle / 60:.0f} min idle"
    else:
        head = f"session {name} stopped ({note.get('reason')})"
    return (f"{head} at {when} (by {note.get('by')}); start it again: "
            f"proof_repl.py start {name} BOOK [--idle-timeout MIN]")
SENTINEL = "FN-REPL-DONE"
EVENT_HEADS = ("defthm", "defthmd", "defun", "defund", "defrule", "defruled",
               "encapsulate", "verify-guards", "thm", "defthm-flag", "mutual-recursion",
               "defconst", "define", "defines", "make-event")
ERROR_MARKS = ("ACL2 Error", "HARD ACL2 ERROR", "ACL2 Halted")
# What ACL2 (SBCL) prints when a form fails below the ACL2 loop.  After
# "ABORTING from raw Lisp" ACL2 has discarded the input still pending, the
# sentinel with it (measured on persvati, w25: a control-stack exhaustion).
CRASH_MARKS = ("ABORTING from raw Lisp", "Unhandled memory fault", "Memory fault",
               "debugger invoked on", "Heap exhausted", "Raw Lisp Break")
RESEND_QUIET_SECONDS = 3.0
STALE_SENTINEL = re.compile(re.escape(SENTINEL) + r" [0-9]+")
RAW_DEBUGGER_PROMPT = re.compile(r"^\s*[0-9]+\](?:\s|$)", re.MULTILINE)
ACL2_PROMPT = re.compile(r"^\s*ACL2\s+[!ps]*>", re.MULTILINE)
PROTOCOL_ERROR = "ACL2 Error [Protocol]: "
RECOVERED_NOTE = ("[raw-Lisp abort: ACL2 discarded the pending input and is back at "
                  "its prompt; the session is live (:pbt :max shows where the world is)]")


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


def is_keyword_command(form: str) -> bool:
    """`:ubt! foo`, `:pe f`: ACL2 reads the arguments after the keyword itself."""
    return form.lstrip().startswith(":")


def commands(text: str) -> list[str]:
    """The top-level commands of TEXT, as ACL2's loop reads them from a terminal.

    A keyword command (`:ubt! foo`, `:pe f`, `:u`) takes its arguments from
    the forms after it, so it and the rest of its line are one command; sent
    apart, `:ubt!` would read the next form (the sentinel) as its argument
    and the session would wait out the hard limit (proof-cost-steps).
    """
    found = spans(text)
    grouped: list[tuple[int, int]] = []
    index = 0
    while index < len(found):
        begin, end = found[index]
        index += 1
        if text[begin] == ":":
            while index < len(found) and "\n" not in text[end:found[index][0]]:
                end = found[index][1]
                index += 1
        grouped.append((begin, end))
    return [text[a:b] for a, b in grouped]


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
    if end == begin:
        # closure-theorems-2: `--from X --until X` sent nothing and said
        # nothing; --until is exclusive, --through inclusive.
        raise SystemExit(f"proof-repl: the range is empty (form {begin + 1} up to but "
                         f"not including form {end + 1}): --until stops BEFORE its "
                         "event; --through includes it")
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
        self.protocol_error: str | None = None
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

    def invalidate(self, collected: list[str], reason: str) -> tuple[str, bool]:
        """A raw debugger can evaluate the sentinel without admitting ACL2 events."""
        self.protocol_error = PROTOCOL_ERROR + reason + "; session invalidated; start fresh"
        self.log.write(self.protocol_error + "\n")
        self.log.flush()
        collected.append(self.protocol_error + "\n")
        self.kill()
        return "".join(collected), False

    def send(self, form: str, timeout: float, quiet: float = RESEND_QUIET_SECONDS
             ) -> tuple[str, bool]:
        """Deliver one form; answer (what ACL2 printed, timed out?).

        The sentinel is a second form after FORM.  Two things can swallow it:
        a raw-Lisp abort (ACL2 discards the pending input when it prints
        "ABORTING from raw Lisp"), and a keyword command that reads more
        arguments than its line carries (`:ubt!` alone reads the sentinel as
        its argument).  After either, once ACL2 has been quiet for QUIET
        seconds, the sentinel is sent once more; a sentinel that was not
        swallowed after all shows up later as a stale marker and is dropped.
        """
        if self.protocol_error:
            return self.protocol_error + "\n", False
        assert self.process.stdin is not None
        self.counter += 1
        marker = f"{SENTINEL} {self.counter}"
        sentinel = f'(cw "~%{marker}~%")\n'
        self.log.write(">>> " + form.rstrip() + "\n")
        self.process.stdin.write(form.rstrip() + "\n")
        self.process.stdin.write(sentinel)
        self.process.stdin.flush()
        collected: list[str] = []
        deadline = time.monotonic() + timeout
        suspect = is_keyword_command(form)
        resent = False
        recovery_prompt = False
        last_line = time.monotonic()
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return "".join(collected), True
            try:
                line = self.lines.get(timeout=min(remaining, 0.5))
            except queue.Empty:
                if not self.alive():
                    return self.invalidate(collected, "ACL2 exited before the completion marker")
                if (suspect and not resent and time.monotonic() - last_line >= quiet):
                    resent = True
                    self.log.write(">>> (sentinel again: the first was swallowed)\n")
                    with contextlib.suppress(BrokenPipeError, OSError):
                        self.process.stdin.write(sentinel)
                        self.process.stdin.flush()
                continue
            if line is None:
                return self.invalidate(collected, "ACL2 exited before the completion marker")
            last_line = time.monotonic()
            text = line.strip()
            if "debugger invoked on" in line or RAW_DEBUGGER_PROMPT.search(line):
                collected.append(line)
                return self.invalidate(collected, "raw Lisp debugger is not the ACL2 event loop")
            if text == marker:
                if crashed("".join(collected)) and not recovery_prompt:
                    return self.invalidate(collected, "raw Lisp abort did not return to an ACL2 prompt")
                if resent and recovery_prompt and crashed("".join(collected)):
                    collected.append(RECOVERED_NOTE + "\n")
                return "".join(collected), False
            if STALE_SENTINEL.fullmatch(text):
                continue  # a resent sentinel ACL2 did not swallow after all
            if any(mark in line for mark in CRASH_MARKS):
                suspect = True
                recovery_prompt = False
            elif suspect and ACL2_PROMPT.search(line):
                recovery_prompt = True
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


FAILED_BANNER = "******** FAILED ********"
SUMMARY_LINE = re.compile(r"^Summary\s*$", re.MULTILINE)


def errored(output: str) -> bool:
    """Did ACL2 refuse the form -- judged by the form's own result, not by
    error text anywhere in its output.

    An event that expects an error and catches it (`must-fail` over an `er
    hard`) prints "HARD ACL2 ERROR" and then succeeds: its summary comes
    after the error and no FAILED banner follows (defkeystone, 2026-09-27:
    such a must-fail returned T and was marked refused).  So error text that
    lies wholly before the form's final Summary, with no FAILED banner, is a
    caught error.  A crash, ACL2 Halted, a FAILED banner, or error text with
    no summary after it (a query, a translation error) is a refusal.
    """
    if (any(mark in output for mark in CRASH_MARKS) or "ACL2 Halted" in output
            or RAW_DEBUGGER_PROMPT.search(output) or PROTOCOL_ERROR in output):
        return True
    if FAILED_BANNER in output:
        return True
    last_error = max((output.rfind(mark) for mark in ERROR_MARKS), default=-1)
    if last_error < 0:
        return False
    summaries = [match.start() for match in SUMMARY_LINE.finditer(output)]
    return not summaries or last_error > summaries[-1]


def crashed(output: str) -> bool:
    return any(mark in output for mark in CRASH_MARKS)


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


# "Long time, few steps": a form whose time is not in the prover's counted
# steps.  blake3-digest, 2026-09-27: fn-b3x-chunk-is-chunk took 126-180 s at
# 228 steps -- the time went into preprocessing/clausifying a large mv-let
# term, which steps do not count, so the failure read as cheap.
SLOW_SECONDS = 20.0
SLOW_STEPS_PER_SECOND = 1000


def slow_note(cost: dict, elapsed: float | None = None) -> str:
    """A diagnosis line when a form took long for the steps it counted, else ''."""
    seconds = max(cost.get("time") or 0.0, elapsed or 0.0)
    steps = cost.get("steps") or 0
    if seconds < SLOW_SECONDS or cost.get("steps_capped") or steps > seconds * SLOW_STEPS_PER_SECOND:
        return ""
    return (f"[long time, few steps: {seconds:.0f} s for {steps:,} prover steps. The time "
            "is outside what steps count: preprocessing/clausifying a large term (a big "
            "mv-let, let* or case split before the first simplification), expansion "
            "the hints ask for, a slow executable counterpart, or a loaded box when ACL2's "
            "own time is small. Steps do not show it; split the term into named helpers or "
            "look at :pso's first goals, and do not read the failure as cheap]")


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


# Commands that take events back out of the session.  chunked-body-2 sent
# `(u)` twice meaning to print and silently lost its last event; `send`
# refuses them unless --allow-undo (resync is the command that undoes).
UNDO_HEADS = frozenset(("u", "ubt", "ubt!", "ubu", "ubu!", "ubt?", "ubu?",
                        "ubt-prehistory", "reset-prehistory"))


def undoes(form: str) -> bool:
    return form_head(form) in UNDO_HEADS


# Forms that leave the ACL2 loop (item 49): `(value :q)` sent to a session
# returned :q to LP, which exits to raw Lisp; the session kept answering, in
# raw Lisp, with no ACL2 world semantics and no error.  `stop NAME` ends a
# session; raw Lisp inside one form is `(progn! (set-raw-mode t) ...)`.
LEAVE_HEADS = {"q": "`:q` leaves the ACL2 loop for raw Lisp",
               "good-bye": "`good-bye` ends the ACL2 process",
               "exit": "`exit` ends the ACL2 process",
               "quit": "`quit` ends the ACL2 process",
               "sb-ext:exit": "`sb-ext:exit` ends the Lisp process",
               "sb-ext:quit": "`sb-ext:quit` ends the Lisp process",
               "set-raw-mode-on!": "`set-raw-mode-on!` leaves the session in raw mode"}
LEAVE_VALUE = re.compile(r"\(\s*(?:value|mv\s+nil)\s+:q\b", re.IGNORECASE)
RAW_MODE_ON = re.compile(r"^\s*\(\s*set-raw-mode\s+(?:t|:on)\b", re.IGNORECASE)


def leaves_loop(form: str) -> str | None:
    """Why FORM would take the session out of the ACL2 loop, or None."""
    head = form_head(form)
    if head in LEAVE_HEADS:
        return LEAVE_HEADS[head]
    if LEAVE_VALUE.search(form):
        return "a form returning :q (`(value :q)`) exits LP into raw Lisp"
    if RAW_MODE_ON.match(form):
        return ("top-level `(set-raw-mode t)` leaves the session in raw mode "
                "(use `(progn! (set-raw-mode t) ...)` for one form)")
    return None


def value_lines(form: str, output: str, keep: int = 20) -> list[str]:
    """What a non-event form printed, for the one-line-per-form answers.

    `send` of several forms printed only `ok` per form, so a diagnostic
    value such as `(disabledp 'zp)` was dropped (d27-representation-2).  An
    event's output is its proof, summarised by the cost line; any other
    form's output is its answer, kept up to KEEP lines.
    """
    if is_event(form) or is_keyword_command(form) and form_head(form) in UNDO_HEADS:
        return []
    lines = output_lines(output)
    if len(lines) > keep:
        lines = lines[:keep] + [f"[... {len(lines) - keep} more lines; --full shows them]"]
    return lines


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


# Events ACL2 does not take inside `with-prover-time-limit` in a book's
# scope, and that prove nothing anyway.
UNLIMITED_HEADS = ("defpkg", "defttag")


def wrap_limit(form: str, limit: float | None) -> str:
    if limit and is_event(form) and head_and_name(form)[0] not in UNLIMITED_HEADS:
        if float(limit).is_integer():
            return f"(with-prover-time-limit {int(limit)} {form})"
        # ACL2 takes a rational number of seconds.
        fraction = fractions.Fraction(str(limit)).limit_denominator(1000)
        return f"(with-prover-time-limit {fraction.numerator}/{fraction.denominator} {form})"
    return form


# --- the session server ------------------------------------------------------

def session_dir(name: str) -> Path:
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", name):
        raise SystemExit(f"proof-repl: session name {name!r}: letters, digits, . _ - only")
    return SESSIONS / name


def session_lock_path(name: str) -> Path:
    session_dir(name)  # validate the name before constructing a lock path
    return SESSIONS / ".locks" / name


def open_session_lock(name: str, role: str | None = None) -> int | None:
    """Claim one name before cache acquisition, passing this lock to serve."""
    path = session_lock_path(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_CREAT | os.O_RDWR, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        os.close(fd)
        return None
    if role:
        note_lock_holder(fd, role)
    return fd


def note_lock_holder(fd: int, role: str) -> None:
    """Write who holds a session's name lock into the lock file itself.

    A `start` whose ssh was killed keeps the lock while it waits for the
    load (friend-blockers-2 spent four minutes finding its own PIDs); the
    refusal and `stop` read this record to name and end that holder.
    """
    entry = {"pid": os.getpid(), "role": role, "since": time.time(),
             "host": socket.gethostname()}
    if role == "serve":
        # The start that passed the lock down keeps its copy until the load
        # is done; both hold it, so both are named.
        with contextlib.suppress(OSError, json.JSONDecodeError, ValueError):
            previous = json.loads(os.pread(fd, 4096, 0).decode("utf-8") or "{}")
            if previous.get("role") == "start":
                entry["starter"] = previous.get("pid")
    record = json.dumps(entry).encode("utf-8")
    with contextlib.suppress(OSError):
        os.ftruncate(fd, 0)
        os.pwrite(fd, record, 0)


def lock_holder(name: str) -> dict:
    try:
        return json.loads(session_lock_path(name).read_text() or "{}")
    except (OSError, json.JSONDecodeError):
        return {}


def _is_holder(pid, name: str) -> bool:
    """PID is still a proof_repl.py start/serve/probe of session NAME."""
    if not isinstance(pid, int) or pid <= 1 or pid == os.getpid():
        return False
    words = _command_of(pid).split()
    base = name[:-len(".probe")] if name.endswith(".probe") else name
    return (any(word.endswith("proof_repl.py") for word in words)
            and any(verb in words for verb in ("start", "serve", "probe"))
            and (name in words or base in words))


def holder_words(name: str) -> str:
    holder = lock_holder(name)
    if not holder.get("pid"):
        return "the holder left no record (an older tool)"
    age = _duration(time.time() - float(holder.get("since") or time.time()))
    alive = _is_holder(holder["pid"], name)
    return (f"held by pid {holder['pid']} ({holder.get('role')}, {age} ago, "
            f"{'still running' if alive else 'not a proof_repl process now'})")


def default_lane(root: Path | None = None) -> str | None:
    """$FN_LANE, else the lane the tree's path names.

    build/lanes/NAME on the laptop; on persvati a lane's REPL tree is
    ~/fn-gates/NAME-repl (or NAME-rN, NAME-devrepl), so the suffix goes.
    """
    configured = os.environ.get("FN_LANE")
    if configured:
        # A lane that exported its worktree's path (batch-aw on hbox, whose
        # tree became /tank/fn/gates/Users/ember/...-repl) means its name.
        return configured.rstrip("/").rsplit("/", 1)[-1] or None
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


LOCAL_FORM = re.compile(r"^\(\s*local\b", re.IGNORECASE)
# What ACL2 refuses in the scope of an encapsulate: a non-local include-book
# ("does not permit non-local include-book forms in the scope of an
# encapsulate") and defpkg ("not an embedded event form" there).
HOISTED_HEADS = ("include-book", "defpkg")


def encapsulated(text: str, directory: Path, skip: set[str],
                 limit: float | None = None) -> tuple[list[str], str]:
    """A book's forms as one `(encapsulate () ...)`, so its local events stay local.

    Loaded form by form, a from-source book's `local` lemmas stay in the
    session as rules its dependents then use, which a certified include
    would not give them (octets-bulk: a dependent admitted in the REPL
    failed certification).  Inside an encapsulate they are dropped at its
    end, as an include drops them.  `in-package` is not an event and goes.

    Answers (hoisted, encapsulate): the book's non-local `include-book` and
    `defpkg` forms, in order, to send first -- ACL2 refuses both inside an
    encapsulate, which made `--ld-local` fail on every book that includes
    another (seven lanes, 2026-09-27) -- and the encapsulate of the rest.  A
    non-local include is what an include of the book brings along, so it
    belongs in the session anyway; a local one stays inside, local.  With
    LIMIT, each event inside is wrapped in `with-prover-time-limit`, as a
    `send` is, so one runaway lemma costs LIMIT seconds, not the session.
    The encapsulate is empty text when no embedded events remain; an
    include-only umbrella still exports its successfully loaded dependencies.
    """
    hoisted: list[str] = []
    kept: list[str] = []
    for form in forms(text):
        head, _ = head_and_name(form)
        if head == "in-package" or include_target(form, directory) in skip:
            continue
        if head in HOISTED_HEADS and not LOCAL_FORM.match(form):
            hoisted.append(form)
        else:
            kept.append(wrap_limit(form, limit))
    # Include-only umbrellas have no embedded events after hoisting/skips.
    # ACL2 rejects an empty encapsulate; the includes already export the world.
    return hoisted, ("(encapsulate ()\n" + "\n".join(kept) + "\n)" if kept else "")


TIME_LIMIT_MARK = "[Time-limit]"


def load_refusal(output: str, limit: float | None, where: str | None) -> str:
    """What `status` prints for the form a load stopped at: the prover's own
    checkpoints and summary, trimmed as a `send` answer is, and, when the
    per-form limit is what stopped it, that sentence first."""
    words = brief(output, where=where)
    if TIME_LIMIT_MARK in output and limit:
        return (f"over the per-form prover limit ({limit:g} s; start --load-limit S "
                "raises it, 0 = none); its checkpoints:\n" + words)
    return words


def load_output_path(state: dict) -> Path | None:
    """Where a load's refused form's whole answer is kept (beside the session)."""
    name = state.get("name")
    return (SESSIONS / name / "load-refusal.txt") if name else None


def note_refusal(state: dict, output: str, limit: float | None) -> None:
    path = load_output_path(state)
    where = None
    if path is not None:
        with contextlib.suppress(OSError):
            path.write_text("\n".join(output_lines(output)) + "\n", encoding="utf-8")
            where = str(path)
    state["error"] = load_refusal(output, limit, where)
    note = slow_note(measure(output), limit if TIME_LIMIT_MARK in output else None)
    if note:
        state["error"] = state["error"] + "\n" + note
    state["load_time_limited"] = TIME_LIMIT_MARK in output


def load_book(acl2: Acl2, book: str, state: dict, load_timeout: float,
              skip: set[str], stop_before: str = "", stop_after: str = "",
              record: bool = True, encapsulate: bool = False,
              limit: float | None = None) -> bool:
    """Send one book's forms after setting the connected book directory to it.

    Local includes of SKIP (books this session loads from source) are not
    sent: their events are already here, and including the uncertified file
    would process it again.  Each event is wrapped in `with-prover-time-limit
    LIMIT` (start --load-limit, default --limit), the same guard `send`
    puts on a form: before 2026-09-27 a book's forms ran with no limit and
    two runaway lemmas held their sessions over ten minutes.  A form over
    the limit is refused like any other, with its checkpoints kept.  Answers
    False at the first refused form, having recorded where in STATE.
    """
    source = ROOT / f"{book}.lisp"
    text = source.read_text(encoding="utf-8")
    where = "" if record else f"{book}: "
    hard = max(load_timeout, (limit or 0) * 1.5 + 30)
    output, timed_out = acl2.send(f'(set-cbd "{source.parent}/")', load_timeout)
    if timed_out or errored(output):
        state["stopped_at"] = where + "set-cbd"
        state["error"] = "load timed out" if timed_out else brief(output)
        return False
    if encapsulate:
        hoisted, body = encapsulated(text, source.parent, skip, limit)
        for form in hoisted:
            output, timed_out = acl2.send(form, hard)
            if timed_out or errored(output):
                state["stopped_at"] = where + form_label(0, form).split(" ", 1)[1]
                if timed_out:
                    state["error"] = "load timed out"
                else:
                    note_refusal(state, output, limit)
                state["load_timed_out"] = timed_out
                return False
        if not body:
            state["ld_loaded"][book] = "encapsulated"
            return True
        output, timed_out = acl2.send(body, hard * 4)
        if timed_out or errored(output):
            state["stopped_at"] = (where + "(encapsulate of the book; start with --ld-leak "
                                   "to stop at the refused event itself)")
            if timed_out:
                state["error"] = "load timed out"
            else:
                note_refusal(state, output, limit)
            state["load_timed_out"] = timed_out
            return False
        cost = measure(output)
        load = state.setdefault("load_cost", {"time": 0.0, "steps": 0, "slowest": []})
        load["time"] = round(load["time"] + (cost["time"] or 0.0), 2)
        load["steps"] += cost["steps"] or 0
        state["ld_loaded"][book] = "encapsulated"
        return True
    for number, form in enumerate(forms(text), 1):
        head, event = head_and_name(form)
        if stop_before and (event == stop_before or stop_before == f"#{number}"):
            break
        if include_target(form, source.parent) in skip:
            continue
        output, timed_out = acl2.send(wrap_limit(form, limit), hard)
        if timed_out or errored(output):
            state["stopped_at"] = where + (event or head)
            if timed_out:
                state["error"] = "load timed out"
            else:
                note_refusal(state, output, limit)
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
          lane: str | None = None, idle_seconds: float | None = None,
          ld: list[str] | None = None, ld_local: bool = False,
          load_limit: float | None = None) -> int:
    if idle_seconds is None:
        idle_seconds = default_idle_seconds()
    directory = session_dir(name)
    directory.mkdir(parents=True, exist_ok=True)
    (directory / STOP_NOTE).unlink(missing_ok=True)
    state_path = directory / "state.json"
    sock_path = directory / "sock"
    now = time.time()
    ld = list(ld or [])
    state = {"name": name, "book": book, "pid": os.getpid(), "loaded": [],
             "stopped_at": None, "error": None, "ready": False, "sends": 0,
             "lane": lane, "idle_seconds": idle_seconds, "started_at": now,
             "last_active": now, "acl2_pgid": None, "ended": None,
             "upto": upto, "through": through, "ld": ld, "ld_loaded": {},
             "ld_local": ld_local,
             "load_limit": limit if load_limit is None else load_limit}
    # SIGTERM (reap's fallback) unwinds through the finally below, which
    # kills the owned ACL2 group; without this it would outlive the server.
    signal.signal(signal.SIGTERM, _on_term)
    note_lock_holder(lock_fd, "serve")

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
        per_form = state["load_limit"] or None
        loaded = True
        for one in ld:
            if not load_book(acl2, one, state, load_timeout, skip, record=False,
                             encapsulate=ld_local, limit=per_form):
                # The session record names the dependency and its first error
                # line (obstructions-7 item 57: depth-debt-5 saw "live, 0
                # forms loaded" three times and never the dependency's error).
                loaded = False
                state["failed_dependency"] = one
                state["dependency_error"] = next(
                    (line.strip() for line in str(state.get("error") or "").splitlines()
                     if line.strip()), "no error text (see the session log)")
                break
        if loaded:
            load_book(acl2, book, state, load_timeout, skip,
                      stop_before=(upto or "").lower(), stop_after=(through or "").lower(),
                      limit=per_form)
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
                    write_stop_note(directory, "idle", idle, idle_seconds, "its own idle timeout")
                    break
                continue
            with connection:
                connection.settimeout(None)
                request = json.loads(read_all(connection))
                # Forms (and a probe's touch) reset the idle clock; status and
                # stop do not.  The clock restarts when the answer is ready,
                # so a long proof is not counted as idleness.
                active = request.get("op", "send") in ("send", "touch")
                if active:
                    state["last_active"] = time.time()
                answer = handle(request, acl2, state, limit)
                if acl2.protocol_error:
                    state["ready"] = False
                    state["error"] = acl2.protocol_error
                    state["ended"] = "invalidated ACL2 protocol"
                if active:
                    state["last_active"] = time.time()
                if request.get("op") == "stop" and request.get("reason"):
                    state["ended"] = request["reason"]
                    write_stop_note(directory, request["reason"],
                                    time.time() - state["last_active"], idle_seconds,
                                    request.get("by") or "stop")
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
            if acl2.protocol_error:
                state["error"] = acl2.protocol_error
                state["ended"] = "invalidated ACL2 protocol"
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
    if op == "touch":
        return {"touched": True}
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
        count = len(commands(form))
    except ValueError as error:
        return {"error": True, "output": f"not one complete form: {error} (a form with "
                "quotes, strings or character literals is safest in a file: "
                "`proof_repl.py send-range NAME FILE`, or `send NAME -` from stdin)"}
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
        note = read_stop_note(sock_path.parent)
        if note:
            raise SystemExit("proof-repl: " + stop_note_words(name, note))
        raise SystemExit(f"proof-repl: no live session {name!r} (start it first)")
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
        client.settimeout(timeout)
        client.connect(str(sock_path))
        client.sendall(json.dumps(request).encode("utf-8"))
        client.shutdown(socket.SHUT_WR)
        return json.loads(read_all(client))


def normalize_book(name: str) -> str:
    """A book's tree-relative name without .lisp.  A bare name (`store-log`,
    no directory) that is not a file at the root resolves under books/, or to
    the one book of that name below books/ (obstructions-9 item 78: three
    sessions were lost to `--source-deps store-log`)."""
    name = name[:-len(".lisp")] if name.endswith(".lisp") else name
    path = Path(name)
    if path.is_absolute():
        with contextlib.suppress(ValueError):
            name = path.resolve().relative_to(ROOT.resolve()).as_posix()
    elif "/" not in name and name and not (ROOT / f"{name}.lisp").is_file():
        if (ROOT / "books" / f"{name}.lisp").is_file():
            return f"books/{name}"
        found = sorted((ROOT / "books").rglob(f"{name}.lisp")) if (ROOT / "books").is_dir() else []
        if len(found) == 1:
            return found[0].relative_to(ROOT).with_suffix("").as_posix()
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
    mine = [meta for meta in metas
            if not toolchain or meta.get("toolchain_identity") == toolchain]
    if mine and not any(meta.get("fasl_sha256") for meta in mine):
        return ("the cache holds these bytes only without their compiled file (.fasl); "
                "installed bare the book would load uncompiled, so no set takes it "
                "(--certify-missing certifies and compiles it)")
    return ("the cache holds certificates for these bytes, but none usable here "
            "(their ACL2 certificate alists disagree with the other books' chosen "
            "certificates, or a live worktree's pair)")


def root_causes(graph: dict[str, list[str]], missing) -> list[str]:
    """The missing books none of whose dependencies is missing (their own bytes)."""
    lost = set(missing)
    return [name for name in sorted(lost) if not set(graph.get(name, ())) & lost]


def refusal_headline(graph: dict[str, list[str]], missing) -> str:
    """The refusal's first line: the command that gets past it.

    A lane that edited books/X and started a session on a test book that
    includes it read a page of diagnosis before finding `--ld books/X` in the
    last line (assurance-hygiene, 2026-09-29).
    """
    roots = root_causes(graph, missing)
    ld = " ".join(f"--ld {name}" for name in roots)
    follow = len(set(missing)) - len(roots)
    return (f"proof-repl: REFUSED -- no certificate at these bytes for "
            f"{', '.join(name + '.lisp' for name in roots)}"
            + (f" (and {follow} book(s) that include it)" if follow else "")
            + f"; start again with `{ld}` (load from source in the session) "
            "or --certify-missing (certify, then include)")


def diagnose(graph: dict[str, list[str]], missing: list[str], cache: Path,
             toolchain: str | None = None) -> list[str]:
    """Why the cache has no set: the books whose own bytes are uncertified, and what follows.

    A missing book none of whose missing-set dependencies is missing is a
    root cause: every book it includes is cached, so the key it lacks is its
    own bytes.  The rest are missing only because they include a root cause
    (a closure key hashes every included book's bytes).
    """
    lost = set(missing)
    roots = root_causes(graph, lost)
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
        f"  start ... --ld DEPENDENCY     load one book it includes from source (the books of "
        f"the closure that include it follow); missing: {roots}",
    ]


def runner_closure(book: str, graph: dict[str, list[str]], include_self: bool,
                   cache: Path, identity: str, acl2: Path):
    """The certify runner's own install of BOOK's dependencies, or None if short.

    `start --certify-missing` ran `certify_books.py --incremental`, whose
    install-partial chooses per book; it said "nothing left" while install-set
    (one compatible set) still found none and `start` refused "no cached
    certificate" (bp-remainder, persvati, twice).  The closure the runner
    installed is the one it certifies against, so when install-partial covers
    every dependency, compiled, the session takes it.
    """
    roots = [book] if include_self else sorted(graph.get(book, ()))
    if not roots:
        return None
    with acl2_slots.slot(f"proof-repl cache {book}"):
        report = certs.install_partial(ROOT, cache, roots, identity, acl2=acl2)
    return None if report.uncached or report.uncompiled else report


def install_closure(book: str, ld=(), auto: str | None = None, jobs: int = 4,
                    log: Path | None = None,
                    include_self: bool = False) -> tuple[bool, str, list[str]]:
    """Acquire the dependencies under the same ACL2 used by the REPL child.

    Answers (acquired, what to print, the books to load from source in
    dependency order).  LD names dependencies to load from source instead of
    from certificates; every book of the closure that includes one of them
    is loaded from source too, since its certificate names the other bytes.
    On a miss, pairs a passing manifest in this tree vouches for are published
    first (so a lane's own `certify_books.py` run counts); then AUTO says what
    to do with what is still missing: "ld" loads it from source, "certify"
    certifies it with `certify_books.py --incremental` and tries again, and
    None refuses with the diagnosis.  INCLUDE_SELF acquires BOOK's own
    certificate too (a book a live session is about to include).
    """
    try:
        graph = include_graph(ROOT, book)
    except (OSError, certs.UnreadableBook, ValueError) as error:
        return False, f"proof-repl: cannot read {book}'s closure: {error}", []
    wanted = [normalize_book(name) for name in ld]
    if book in wanted:
        # bp-remainder-2 read the old "outside this book's dependencies" as
        # "--ld takes the test book" (obstructions-5 item 42).
        return False, (f"proof-repl: --ld takes a DEPENDENCY of the session's book, not the book "
                       f"itself: {book} already loads form by form from source; name the book "
                       f"it includes that you changed (`start NAME {book} --ld books/X`)"), []
    outside = [name for name in wanted if name not in graph]
    if outside:
        return False, (f"proof-repl: --ld takes a DEPENDENCY of {book} (a book it includes, "
                       f"directly or not) to load from source; {book} does not include "
                       + ", ".join(outside)
                       + f" (start the session on a book that does, or drop the --ld)"), []
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
        required = set(graph) - from_source - (set() if include_self else {book})
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
                dependencies_only=not include_self, purge_on_miss=purge,
                acl2=acl2), required

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
            if (report is not None and report.artifact_set is None
                    and done.returncode == 0 and not from_source):
                per_book = runner_closure(book, graph, include_self, cache,
                                          fingerprint.identity, acl2)
                if per_book is not None:
                    printed.append(
                        "proof-repl: install-set found no one compatible set after the "
                        f"certify run (missing {', '.join(report.uncached)}); the runner's "
                        "own per-book install (install-partial) covers the closure -- "
                        "taking that")
                    report = per_book
        if (report is not None and report.artifact_set is None
                and report.action != "install-partial" and auto == "ld"):
            from_source |= dependents_of(graph, report.uncached) - {book}
            printed.append("proof-repl: loading from source (proofs run in the session): "
                           + ", ".join(dependency_order(graph, from_source)))
            report, required = attempt(from_source, purge=False)
        if (report is not None and report.artifact_set is None
                and report.action != "install-partial"):
            missing = sorted(report.uncached)
            # The refusal keeps the old contract: no local pair of the closure
            # survives a miss to stand in for a certificate later.
            attempt(from_source, purge=True)
            return False, "\n".join([refusal_headline(graph, missing)] + printed + diagnose(
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


# `_start`'s answer when a dependency loaded from source failed. `start`
# stops the failed session; only an explicit certification request may retry.
SOURCE_DEPS_FAILED = 75


def start(args) -> int:
    """Start a session without turning a source refusal into an implicit build."""
    code = _start(args)
    if code != SOURCE_DEPS_FAILED:
        return code
    with contextlib.suppress(SystemExit):
        stop(args)
    if not getattr(args, "certify_missing", False):
        print("proof-repl: dependency failed from source; no certification launched. "
              "Fix the source/world or explicitly restart with --certify-missing.")
        return code
    args.certify_missing = True
    args.source_deps = None
    args.ld_missing = False
    args.ld = []
    print("proof-repl: retrying with --certify-missing: the dependencies are "
          "certified (on this machine, into its cache) and included, as a "
          "certification would include them")
    return _start(args)


def _start(args) -> int:
    directory = session_dir(args.name)
    lock_fd = open_session_lock(args.name, "start")
    if lock_fd is None:
        print(f"proof-repl: session {args.name!r} is starting or live; stop it first "
              f"({holder_words(args.name)}; `proof_repl.py stop {args.name}` ends a stuck "
              "start as well as a live session)")
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
        (directory / STOP_NOTE).unlink(missing_ok=True)
        with open(directory / "server.log", "a", encoding="utf-8") as log:
            command = [sys.executable, __file__, "serve", args.name, args.book,
                       "--limit", str(args.limit), "--load-timeout", str(args.load_timeout),
                       "--load-limit", str(args.limit if getattr(args, "load_limit", None)
                                           is None else args.load_limit),
                       "--lock-fd", str(lock_fd),
                       "--idle-seconds", str(idle_from_args(args))]
            lane = getattr(args, "lane", None) or default_lane()
            if lane:
                command += ["--lane", lane]
            if args.upto:
                command += ["--upto", args.upto]
            if args.through:
                command += ["--through", args.through]
            for one in from_source:
                command += ["--ld", one]
            if getattr(args, "ld_local", False):
                command += ["--ld-local"]
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
                    failed_in = [one for one in from_source
                                 if str(state.get("stopped_at") or "").startswith(one + ":")]
                    if failed_in and not getattr(args, "certify_missing", False):
                        print(f"proof-repl: the failure is in {failed_in[0]}, loaded "
                              f"from source ({state.get('stopped_at')}); a from-source "
                              "load is not a certification and can fail where one "
                              "passes")
                        return SOURCE_DEPS_FAILED
                    return 1
            time.sleep(0.5)
        else:
            print("proof-repl: the session did not become ready; see", directory / "log")
            return 1
        code = status(args)
        final = read_state(args.name) or {}
        line, partial = load_verdict(final)
        print(line)
        if final.get("failed_dependency"):
            return SOURCE_DEPS_FAILED
        return PARTIAL_LOAD if partial else code
    finally:
        os.close(lock_fd)


# `start`'s answer when the book's load stopped at a refused form: the session
# may be live, just before it, but it is not the book (join-f2-5 lost a farm
# round to a start whose output looked like a full load).
PARTIAL_LOAD = 3


def load_verdict(state: dict) -> tuple[str, bool]:
    """`start`'s last line: where the load stopped, or that it is complete.

    Answers (the line, whether the load is partial).  A stop the caller
    asked for (--upto/--through) is a complete load of what was asked.
    """
    name, book = state.get("name", "?"), state.get("book", "?")
    loaded = len(state.get("loaded") or [])
    stopped = state.get("stopped_at")
    if state.get("failed_dependency"):
        return (f"proof-repl {name}: NOT LIVE -- the dependency {state['failed_dependency']} "
                f"failed to load from source at {stopped or '?'}: "
                f"{state.get('dependency_error')}; none of {book}'s forms were sent. "
                f"`proof_repl stop {name}`, then fix it or start with --certify-missing; "
                f"exit {SOURCE_DEPS_FAILED}", True)
    if not stopped:
        asked = state.get("upto") or state.get("through")
        return (f"proof-repl {name}: LOADED {book}: {loaded} forms"
                + (f" (as asked, {'up to' if state.get('upto') else 'through'} {asked})"
                   if asked else ""), False)
    within, _, event = stopped.rpartition(": ")
    try:
        total = len(forms((ROOT / f"{book}.lisp").read_text(encoding="utf-8")))
    except OSError:
        total = None
    return (f"proof-repl {name}: PARTIAL LOAD -- stopped at {event} in "
            f"{within or book} (a from-source dependency) " if within else
            f"proof-repl {name}: PARTIAL LOAD -- stopped at {event} in {book} "
            ) + (f"after {loaded}" + (f" of {total}" if total else "") + " forms; "
                 ) + ("the session is live just before it (fix it, then `send` or "
                      "`send-range --from`); exit 3" if state.get("ready") else
                      "the session is not live; exit 3"), True


REFUSAL_MARKS = ("******** FAILED ********", "ACL2 Error")


def last_checkpoints(log_text: str, lines: int = 16) -> tuple[str | None, list[list[str]]]:
    """(the refused form's first line, its key checkpoints) from a session log.

    A multi-form `send` prints one line per form, and the checkpoints stayed
    in the session log; decision-keystones grepped it over ssh three times.
    The log holds `>>> FORM` before each form's output; the last form whose
    output has a refusal mark is the one answered.
    """
    blocks: list[tuple[str, list[str]]] = []
    for line in log_text.splitlines():
        if line.startswith(">>> "):
            blocks.append((line[4:], []))
        elif blocks:
            blocks[-1][1].append(line)
    for form, output in reversed(blocks):
        if not any(mark in line for line in output for mark in REFUSAL_MARKS):
            continue
        found: list[list[str]] = []
        for index, line in enumerate(output):
            if line.startswith("*** Key checkpoint"):
                block = [line]
                for follow in output[index + 1:]:
                    if follow.startswith(("*** Key checkpoint", "Summary", "ACL2 Error",
                                          "******** FAILED")):
                        break
                    block.append(follow)
                while block and not block[-1].strip():
                    block.pop()
                found.append(block[:lines] + (["[...]"] if len(block) > lines else []))
        return form, found
    return None, []


def checkpoints(args) -> int:
    try:
        text = (session_dir(args.name) / "log").read_text(encoding="utf-8", errors="replace")
    except OSError:
        print(f"proof-repl: no log for session {args.name!r}")
        return 1
    form, found = last_checkpoints(text, args.lines)
    if form is None:
        print(f"proof-repl {args.name}: no refused form in the session log")
        return 0
    print(f"proof-repl {args.name}: last refused form: {form[:120]}")
    if not found:
        print("  (no key checkpoint printed: the refusal is not a failed proof -- "
              "`send ... --full` shows it)")
    for block in found:
        print("\n".join(block))
    return 0


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
        print(f"  from source (not certified): {book}, "
              + ("in one encapsulate (its local events stay local)" if count == "encapsulated"
                 else f"{count} forms (its local events are in the session)"))
    leaking = [book for book, count in (state.get("ld_loaded") or {}).items()
               if count != "encapsulated"]
    if leaking:
        print(f"  WARNING: {len(leaking)} from-source book(s) loaded form by form, so their "
              "LOCAL lemmas and theory are rules in this session that a certified include "
              "would not give: a proof here may pass, fail or cost differently than under "
              "certification (feed-queue, 2026-09-27: 6.9M steps here, 1.76M over the "
              "certified dependency). This session was started with --ld-leak; without it "
              "each loads inside one encapsulate (its non-local include-book and defpkg "
              "forms first), or --certify-missing includes certificates.")
    if state["stopped_at"]:
        print(f"  stopped at {state['stopped_at']}:")
        print("  " + (state["error"] or "").replace("\n", "\n  "))
        if state.get("load_time_limited") and live:
            print(f"  the session is live just before it: `proof_repl.py probe {state['name']} "
                  f"{state['stopped_at'].split(': ')[-1]} --hints '((...))'` tries hints "
                  "beside it, `send` takes a fixed form")
    elif state["loaded"]:
        print(f"  last loaded: {state['loaded'][-1]}")
    last = state.get("last_active")
    deadline = state.get("idle_seconds")
    if live and last:
        idle = time.time() - last
        print(f"  last send {_duration(idle)} ago; idle deadline "
              + (f"{_duration(deadline)}, stops in {_duration(deadline - idle)} "
                 "without a send (status does not count)" if deadline else "none (never stops)"))
    note = read_stop_note(session_dir(args.name))
    if not live and note:
        print("  " + stop_note_words(args.name, note))
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
    note = slow_note(cost, answer.get("elapsed"))
    if note:
        print(note)
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
        note = slow_note(cost, elapsed)
        if note:
            print("        " + note, flush=True)
        if full or wants_full(form):
            print(output)
        elif refused:
            print(brief(output, where=save_output(name, output, f"-{position}")))
        else:
            for line in value_lines(form, output):
                print("        " + line)
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


# --- :expand (:free ...) over a controller (obstructions-7/8 item 65) -----
#
# `:expand ((:free (n) (f x n)))' expands EVERY instance of (f x _), the
# recursive call its expansion introduces included: when N sits where F's
# recursion is controlled (a formal of its measure, else an argument its
# recursive call changes), each expansion makes a new match and the prover
# re-expands until the step limit.  A warning at send, never a refusal.

def _theory_check():
    import theory_check  # noqa: PLC0415
    return theory_check


def expand_terms(form: str) -> list:
    """Every term an `:expand' hint of FORM names, as nested lists."""
    try:
        read = _theory_check().forms(form)
    except ValueError:
        return []
    found: list = []

    def walk(node) -> None:
        if not isinstance(node, list):
            return
        for position, item in enumerate(node):
            if item == ":expand" and position + 1 < len(node):
                value = node[position + 1]
                if isinstance(value, list) and value:
                    if isinstance(value[0], list):
                        found.extend(term for term in value if isinstance(term, list))
                    else:
                        found.append(value)
            walk(item)

    walk(read)
    return found


def _symbols(term) -> set[str]:
    if isinstance(term, list):
        return set().union(*(_symbols(item) for item in term)) if term else set()
    return {term} if isinstance(term, str) and not term.startswith('"') else set()


def _self_calls(term, name: str) -> list[list]:
    if not isinstance(term, list) or not term:
        return []
    if term[0] == "quote":
        return []
    calls = [term] if term[0] == name else []
    for item in term[1:]:
        calls.extend(_self_calls(item, name))
    return calls


def controller_positions(definition: list) -> list[int]:
    """The argument positions controlling DEFINITION's recursion: the formals
    its :measure mentions, else those its recursive calls change; [] for a
    function that does not call itself."""
    if len(definition) < 4 or not isinstance(definition[2], list):
        return []
    name, formals = definition[1], [f for f in definition[2] if isinstance(f, str)]
    body = definition[-1]
    calls = _self_calls(body, name)
    if not calls:
        return []
    for item in definition[3:-1]:
        if isinstance(item, list) and item and item[0] == "declare":
            for decl in item[1:]:
                if isinstance(decl, list) and decl and decl[0] == "xargs":
                    rest = decl[1:]
                    for key, value in zip(rest[::2], rest[1::2]):
                        if key == ":measure":
                            used = _symbols(value)
                            return [i for i, f in enumerate(formals) if f in used]
    return sorted({i for call in calls for i, f in enumerate(formals)
                   if i + 1 < len(call) and call[i + 1] != f})


DEFUN_HEADS = ("defun", "defund", "defun-inline", "defund-inline")


def find_definition(name: str, texts: list[str]) -> list | None:
    """NAME's defun: first in TEXTS (the forms being sent, the session's
    book), else the tree's books/ and tests/acl2/ (git grep, then that file)."""
    def search(text: str) -> list | None:
        try:
            read = _theory_check().forms(text)
        except ValueError:
            return None
        stack = list(read)
        while stack:
            form = stack.pop(0)
            if not isinstance(form, list) or not form:
                continue
            if form[0] in DEFUN_HEADS and len(form) > 1 and form[1] == name:
                return form
            if form[0] in ("mutual-recursion", "local", "encapsulate", "progn"):
                stack[:0] = form[1:]
        return None

    for text in texts:
        if name in text.lower():
            found = search(text)
            if found:
                return found
    pattern = r"\(def(un|und)(-inline)?[[:space:]]+" + re.escape(name) + r"([[:space:])]|$)"
    listed = subprocess.run(["git", "-C", str(ROOT), "grep", "-l", "-i", "-E", pattern,
                             "--", "books", "tests/acl2"],
                            capture_output=True, text=True, check=False).stdout.split()
    for relative in listed[:3]:
        found = search((ROOT / relative).read_text(encoding="utf-8", errors="replace"))
        if found:
            return found
    return None


def _spell(term) -> str:
    if isinstance(term, list):
        return "(" + " ".join(_spell(item) for item in term) + ")"
    return str(term)


def free_expand_warnings(form: str, texts: list[str] = ()) -> list[str]:
    """One line per `:expand (:free VARS (F ...))' of FORM that frees an
    argument at a controller position of F's recursion."""
    lines = []
    for term in expand_terms(form):
        if len(term) < 3 or term[0] != ":free" or not isinstance(term[1], list):
            continue
        free, target = set(term[1]), term[2]
        if not isinstance(target, list) or not target or not isinstance(target[0], str):
            continue
        definition = find_definition(target[0], [form, *texts])
        if definition is None:
            continue
        for position in controller_positions(definition):
            if position + 1 < len(target) and _symbols(target[position + 1]) & free:
                formal = definition[2][position]
                lines.append(
                    f"proof-repl: warning: :expand {_spell(term)} frees "
                    f"{_spell(target[position + 1])}, in {target[0]}'s controlling argument "
                    f"{formal}: each expansion's recursive call matches again and is "
                    f"expanded in turn (a loop, or a blow-up to the step limit); name the "
                    f"instances to expand, or keep {formal}'s argument bound")
                break
    return lines


def warn_free_expands(items: list[str], texts: list[str] = ()) -> None:
    for form in items:
        for line in free_expand_warnings(form, list(texts)):
            print(line, file=sys.stderr, flush=True)


# --- what `send` added to a session, for its probe (item 72) -------------
#
# A probe session is loaded from the BOOK FILE up to the event: a lemma sent
# by hand to session NAME is in NAME's world and not in NAME.probe's, so the
# probe "did not see" it (online-reclaim, 2026-09-29).  `send` records each
# event form a session accepted, tagged with the session's start; `probe`
# names them, and `probe --with-sent` sends them (above its checkpoint, so
# they are undone with the attempt).

SENT_EVENTS = "sent-events.jsonl"


def record_sent(name: str, forms: list[str]) -> None:
    started = (read_state(name) or {}).get("started_at")
    events = [form for form in forms if is_event(form)]
    if not events or started is None:
        return
    with contextlib.suppress(OSError):
        with open(session_dir(name) / SENT_EVENTS, "a", encoding="utf-8") as handle:
            for form in events:
                handle.write(json.dumps({"started_at": started, "form": form}) + "\n")


def sent_events(name: str) -> list[str]:
    """The event forms `send` added to session NAME since it started."""
    started = (read_state(name) or {}).get("started_at")
    try:
        lines = (session_dir(name) / SENT_EVENTS).read_text(encoding="utf-8").splitlines()
    except OSError:
        return []
    out = []
    for line in lines:
        with contextlib.suppress(json.JSONDecodeError):
            row = json.loads(line)
            if row.get("started_at") == started and started is not None:
                out.append(row["form"])
    return out


HOST_LOAD = re.compile(r'^\(\s*(ld|load)\s+"([^"]+)"', re.IGNORECASE)
HOST_LOADS = "host-loads.jsonl"


def host_load_target(form: str, directory: Path | None) -> str | None:
    """The repository host file (root-relative) an `(ld "X")` / `(load "X")`
    form names, resolved from DIRECTORY (the session's connected book
    directory) or else from the root; None for anything else."""
    match = HOST_LOAD.match(form.strip())
    if not match:
        return None
    written = match.group(2)
    for base in ([directory] if directory else []) + [ROOT]:
        target = (base / written).resolve()
        if target.is_file():
            with contextlib.suppress(ValueError):
                relative = target.relative_to(ROOT.resolve()).as_posix()
                if relative.startswith("host/"):
                    return relative
    return None


def session_host_loads(name: str) -> list[str]:
    """The host files `send` loaded into session NAME since it started."""
    started = (read_state(name) or {}).get("started_at")
    try:
        lines = (session_dir(name) / HOST_LOADS).read_text(encoding="utf-8").splitlines()
    except OSError:
        return []
    out = []
    for line in lines:
        with contextlib.suppress(json.JSONDecodeError):
            row = json.loads(line)
            if started is not None and row.get("started_at") == started:
                out.append(row["file"])
    return out


def second_host_load(name: str, several: list[str]) -> str | None:
    """Why sending SEVERAL would be a second host load in session NAME
    (obstructions-9 item 84: a session with several host loads behind it
    died in a fasl load), or None."""
    directory = session_directory(name)
    loaded = session_host_loads(name)
    for one in several:
        target = host_load_target(one, directory)
        if target is None:
            continue
        if loaded:
            return (f"session {name!r} already loaded host file {loaded[0]}; a second host "
                    f"load ({target}) in one session dies in a fasl load.  Start another "
                    f"session for it (`proof_repl.py start NAME2 ...`), or stop {name} and "
                    "start it again")
        loaded = [target]
    return None


def record_host_loads(name: str, several: list[str]) -> None:
    started = (read_state(name) or {}).get("started_at")
    directory = session_directory(name)
    if started is None:
        return
    with contextlib.suppress(OSError):
        with open(session_dir(name) / HOST_LOADS, "a", encoding="utf-8") as handle:
            for one in several:
                target = host_load_target(one, directory)
                if target:
                    handle.write(json.dumps({"started_at": started, "file": target}) + "\n")


def send(args) -> int:
    form = args.form if args.form != "-" else sys.stdin.read()
    try:
        several = commands(form)
    except ValueError:
        several = [form]  # the session answers with the parse error
    for one in several:
        why = leaves_loop(one)
        if why:
            print(f"proof-repl: refusing {one.strip()[:40]!r}: {why}; the session would "
                  "keep answering outside the ACL2 loop.  End a session with "
                  f"`proof_repl.py stop {args.name}`.", file=sys.stderr)
            return 2
    undoing = [one for one in several if undoes(one)]
    if undoing and not getattr(args, "allow_undo", False):
        print(f"proof-repl: refusing {undoing[0].strip()[:40]!r}: it takes events back "
              "out of the session (`(u)` is not a print).  Pass --allow-undo if that "
              "is meant, or `resync NAME BOOK --from EVENT` to undo and resend a book.",
              file=sys.stderr)
        return 2
    why = second_host_load(args.name, several)
    if why:
        print(f"proof-repl: refusing: {why}", file=sys.stderr)
        return 2
    several, ready = prepare_includes(args.name, several)
    if not ready:
        return 1
    book = (read_state(args.name) or {}).get("book")
    warn_free_expands(several, [(ROOT / f"{book}.lisp").read_text(encoding="utf-8")]
                      if book and (ROOT / f"{book}.lisp").exists() else [])
    if len(several) <= 1:
        code = send_one(args.name, several[0] if several else form, args.limit, args.full)
    else:
        items = [(form_label(index, one), one) for index, one in enumerate(several, 1)]
        code = send_many(args.name, items, args.limit, args.full,
                         getattr(args, "keep_going", False))
    # A host load is recorded whatever it answered: its fasl is in the session.
    record_host_loads(args.name, several or [form])
    if code == 0:
        record_sent(args.name, several or [form])
    return code


def session_directory(name: str) -> Path | None:
    """The connected book directory of session NAME: its book's directory."""
    book = (read_state(name) or {}).get("book")
    return (ROOT / f"{book}.lisp").parent if book else None


def rooted_include(form: str, directory: Path) -> tuple[str, str | None]:
    """FORM with a repository-root-relative include path made relative to
    DIRECTORY (the session's connected book directory), and the book it names.

    A session on books/X has books/ as its directory, so `(include-book
    "tests/acl2/y-tests")` named books/tests/acl2/y-tests and failed
    (paged-history, 2026-09-29).  A path that names a book from DIRECTORY
    is left alone; one that names a book only from the root is rewritten.
    """
    match = INCLUDE.match(form.strip())
    if not match or ":dir" in match.group(2).lower():
        return form, None
    written = match.group(1)
    if (directory / f"{written}.lisp").is_file() or not (ROOT / f"{written}.lisp").is_file():
        return form, include_target(form, directory)
    relative = os.path.relpath(ROOT / written, directory)
    rewritten = form.replace(f'"{written}"', f'"{relative}"', 1)
    return rewritten, include_target(rewritten, directory)


def prepare_includes(name: str, several: list[str], acquire=None) -> tuple[list[str], bool]:
    """The forms to send, each repository include made relative to the
    session's directory, and whether every included book is certified.

    A sent include of a book with no certificate here (a tests/acl2 book is
    rarely in a books/ session's closure) is acquired from matching cached
    evidence first. A miss is refused, never implicitly certified; choose
    certification explicitly or send the intended source forms instead.
    """
    directory = session_directory(name)
    if directory is None:
        return several, True
    acquire = acquire or (lambda book: install_closure(
        book, (), None, 4, SESSIONS / f"{name}.include.log", include_self=True))
    prepared = []
    for one in several:
        rewritten, target = rooted_include(one, directory)
        if rewritten != one:
            print(f"proof-repl: include path made relative to the session's directory "
                  f"{directory.relative_to(ROOT).as_posix() if directory.is_relative_to(ROOT) else directory}/: "
                  f"{rewritten.strip()}")
        if (target is not None and (ROOT / f"{target}.lisp").is_file()
                and not certs.valid_looking(ROOT / f"{target}.cert")):
            acquired, detail, _ = acquire(target)
            print(detail)
            if not acquired:
                print(f"proof-repl: not sending the include of {target}: no certificate "
                      "could be acquired for it")
                return several, False
        prepared.append(rewritten)
    return prepared, True


def read_state(name: str) -> dict | None:
    path = session_dir(name) / "state.json"
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return None


def range_items(path: Path, all_forms: list[str], chosen: range, from_source: set[str],
                skip_includes: bool = False) -> tuple[list[tuple[str, str]], list[str], int]:
    """(label, form) to send for CHOSEN, the labels of the includes skipped, and
    how many of the sent forms are top-level `(local ...)`."""
    items, skipped, local = [], [], 0
    for index in chosen:
        form = all_forms[index]
        target = include_target(form, path.parent)
        if target is not None and (skip_includes or target in from_source):
            skipped.append(form_label(index + 1, form)
                           + (" (loaded from source already)" if target in from_source
                              else " (--skip-includes)"))
            continue
        local += bool(LOCAL_FORM.match(form))
        items.append((form_label(index + 1, form), form))
    return items, skipped, local


def range_words(name: str, book: str, chosen: range, items: list, skipped: list[str],
                local: int, ld_local: bool, until: str | None = None) -> str:
    """The head line of a send-range: what it sends, what it skips and why.

    web-native, 2026-09-27: a local include a later termination proof needed
    was absent from the session and nothing said so; every skipped form is
    now named, and the local forms sent are counted, since at the top level
    their events stay in the session (a certified include drops them).
    """
    words = (f"send-range {name}: forms #{chosen.start + 1}-#{chosen.stop} of {book} "
             f"({len(items)} to send")
    if local:
        words += (f", {local} of them (local ...): " +
                  ("inside one encapsulate, so they are dropped at its end as an include "
                   "drops them" if ld_local else
                   "sent at the top level, so their events STAY in this session "
                   "(--ld-local drops them at the range's end)"))
    words += ")"
    if skipped:
        words += f"\nskipped {len(skipped)} form(s): " + "; ".join(skipped)
    if until:
        # reclaim-equivalence read --until as inclusive and waited on a
        # theorem that was never sent (obstructions-6 item 53).
        words += (f"\n--until {until} is EXCLUSIVE: {until} itself is NOT sent "
                  f"(--through {until} sends it)")
    return words


def file_includes_rooted(form: str, file_dir: Path) -> str:
    """FORM with an include path written relative to FILE_DIR (the sent
    file's directory) rewritten root-relative, for prepare_includes to make
    relative to the session's directory."""
    match = INCLUDE.match(form.strip())
    if not match or ":dir" in match.group(2).lower():
        return form
    target = include_target(form, file_dir)
    if target is None or target.startswith("/") or not (ROOT / f"{target}.lisp").is_file():
        return form
    return form.replace(f'"{match.group(1)}"', f'"{target}"', 1)


def send_file(args) -> int:
    """Every form of a file, in order, into a live session (item 75).

    For a test file (tests/acl2/X-tests.lisp) beside a book session: its
    includes are written relative to ITS directory, so each is rewritten for
    the session's (and a book with no certificate is acquired first, as
    `send` does); then the forms go one at a time with a line each, stopping
    at the first refusal unless --keep-going.  send-range sends a range of a
    book with the book's own paths; this sends a whole file with its paths
    made the session's."""
    path = book_path(args.file)
    text = path.read_text(encoding="utf-8")
    all_forms = forms(text)
    if not all_forms:
        print(f"proof-repl send-file: {args.file} has no forms")
        return 2
    for one in all_forms:
        why = leaves_loop(one)
        if why:
            print(f"proof-repl: refusing {args.file}: {one.strip()[:40]!r}: {why}",
                  file=sys.stderr)
            return 2
        if undoes(one) and not getattr(args, "allow_undo", False):
            print(f"proof-repl: refusing {args.file}: {one.strip()[:40]!r} takes events "
                  "back out of the session; pass --allow-undo if that is meant",
                  file=sys.stderr)
            return 2
    labels = [form_label(index, one) for index, one in enumerate(all_forms, 1)]
    rooted = [file_includes_rooted(one, path.parent) for one in all_forms]
    prepared, ready = prepare_includes(args.name, rooted)
    if not ready:
        return 1
    relative = path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else str(path)
    print(f"proof-repl send-file: {len(prepared)} form(s) of {relative} into {args.name}, "
          "in order" + (" (every refusal reported)" if args.keep_going else
                        " (stopping at the first refusal)"))
    warn_free_expands(prepared, [text])
    code = send_many(args.name, list(zip(labels, prepared)), args.limit, args.full,
                     args.keep_going)
    if code == 0:
        record_sent(args.name, prepared)
    return code


def guard_notes(text: str, chosen: range) -> list[str]:
    """For each guard verification among the CHOSEN forms (0-based), the
    same-book callees and the form each is verified at (obstructions-7 item
    56): a callee verified LATER passes in a session whose world already has
    it and fails at certify."""
    lines = []
    for index, name, callees in _theory_check().guard_events(text):
        if index - 1 not in chosen or not callees:
            continue
        later = [f"{callee} #{at}" for callee, at in callees if at > index]
        words = ", ".join(f"{callee} #{at}" for callee, at in callees)
        lines.append(f"note: form #{index} verifies {name}'s guards; its callees here are "
                     f"verified at {words}"
                     + (f" -- LATER: {', '.join(later)} (certify fails at #{index}; a "
                        f"session that already has them passes)" if later else ""))
    return lines


def send_range(args) -> int:
    """A book's forms from --from to --until/--through into a live session."""
    path = book_path(args.book)
    all_forms = forms(path.read_text(encoding="utf-8"))
    chosen = select_range(all_forms, args.start, args.until, args.through)
    state = read_state(args.name) or {}
    from_source = set(state.get("ld") or [])
    items, skipped, local = range_items(path, all_forms, chosen, from_source,
                                        args.skip_includes)
    ld_local = getattr(args, "ld_local", False)
    print(range_words(args.name, args.book, chosen, items, skipped, local, ld_local,
                      args.until))
    if not items:
        return 0
    text = path.read_text(encoding="utf-8")
    for line in guard_notes(text, chosen):
        print(line, flush=True)
    warn_free_expands([form for _, form in items], [text])
    if ld_local:
        hoisted, body = encapsulated("\n".join(form for _, form in items), path.parent,
                                     set(), None)
        items = ([(form_label(0, form).split(" ", 1)[1], form) for form in hoisted]
                 + ([(f"#{chosen.start + 1}-#{chosen.stop} (encapsulate)", body)] if body else []))
    return send_many(args.name, items, args.limit, args.full, args.keep_going)


# Heads whose name argument is an existing name, not one the form introduces.
NAMELESS_HEADS = ("verify-guards", "defattach", "in-theory", "local")


def introduced_name(form: str) -> str | None:
    head, name = head_and_name(form)
    return None if head in NAMELESS_HEADS else name


def first_index(name: str, names: list[str], want_present: bool,
                asker=None) -> int | None:
    """Ask session NAME which of NAMES is (want_present) or is not a logical
    name in its world; answers the first such position, or None."""
    if not names:
        return None
    asker = asker or ask
    probes = " ".join(f"(if (logical-namep '{one} (w state)) t nil)" for one in names)
    form = f"(position {'t' if want_present else 'nil'} (list {probes}))"
    output = asker(name, {"op": "send", "form": form, "limit": None}).get("output", "")
    found = re.findall(r"(?:^|>)\s*([0-9]+|NIL)\s*$", output, re.MULTILINE)
    if not found:
        raise SystemExit(f"proof-repl: resync could not read the world of {name!r}:\n"
                         + brief(output))
    return None if found[-1] == "NIL" else int(found[-1])


def resync(args, asker=None) -> int:
    """Undo the session back to EVENT and resend the book from there, in one command.

    web-native, 2026-09-27: `:ubt! X` then `send-range --from X` sometimes
    left earlier definitions missing (the undo reached an event the book
    defines before X, or an earlier form had never been sent), and the
    redefinition refusals that followed only a fresh `start` cleared.  This
    asks the session's world which of the book's names it has: it undoes
    (`:ubt!`) through the first name from EVENT onward that is present,
    until none is, then resends from the first name before EVENT that is
    missing, or from EVENT.
    """
    asker = asker or ask
    path = book_path(args.book)
    all_forms = forms(path.read_text(encoding="utf-8"))
    begin = locate(all_forms, args.start)
    tail = [(index, introduced_name(all_forms[index])) for index in
            select_range(all_forms, args.start, args.until, args.through)]
    tail = [(index, one) for index, one in tail if one]
    undone: list[str] = []
    for _ in range(len(tail) + 1):
        present = first_index(args.name, [one for _, one in tail], True, asker)
        if present is None:
            break
        target = tail[present][1]
        answer = asker(args.name, {"op": "send", "form": f":ubt! {target}", "limit": None})
        undone.append(target)
        if answer.get("error"):
            print(f"resync {args.name}: :ubt! {target} was refused:\n"
                  + brief(answer.get("output", "")))
            return 1
    else:
        print(f"resync {args.name}: the world still holds names from #{begin + 1} on "
              f"after {len(undone)} undo(s); start the session again")
        return 1
    before = [(index, introduced_name(all_forms[index])) for index in range(begin)]
    before = [(index, one) for index, one in before if one]
    missing = first_index(args.name, [one for _, one in before], False, asker)
    start = before[missing][0] if missing is not None else begin
    print(f"resync {args.name}: "
          + (f"undid through {', '.join(undone)}" if undone else "nothing from "
             f"#{begin + 1} on was in the world")
          + (f"; #{start + 1} {before[missing][1]} (before {args.start}) was missing, so "
             f"resending from there" if missing is not None else "")
          + ".", flush=True)
    chosen = range(start, select_range(all_forms, args.start, args.until,
                                       args.through).stop)
    state = read_state(args.name) or {}
    items, skipped, local = range_items(path, all_forms, chosen, set(state.get("ld") or []))
    print(range_words(args.name, args.book, chosen, items, skipped, local, False,
                      getattr(args, "until", None)))
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
PROBE_BASE = "fn-probe-base"


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


def probe_attempts(text: str, event: str | None, hints: str | None) -> list[str]:
    """The forms one probe proves: one form (renamed, hints set), or several.

    Several forms (helper lemmas and the target) are sent in order; a form
    named like EVENT is renamed, and --hints go to the last form.
    """
    several = commands(text)
    if len(several) <= 1:
        return [probe_form(text, hints)]
    attempts = []
    for position, form in enumerate(several, 1):
        mine = head_and_name(form)[1] == event and head_and_name(form)[0] in THEOREM_HEADS
        last = position == len(several)
        if mine:
            form = probe_form(form, None)
        if last and hints is not None:
            form = set_keyword(form, ":hints", hints)
        attempts.append(form)
    return attempts


PROBE_AT = "FN-PROBE-AT"
PROBE_AT_LINE = re.compile(re.escape(PROBE_AT) + r" ([0-9]+)")
WORLD_QUERY = f'(cw "~%{PROBE_AT} ~x0~%" (max-absolute-command-number (w state)))'


def world_command(name: str) -> int | None:
    """The probe session's current absolute command number, or None if it cannot say."""
    answer = ask(name, {"op": "send", "form": WORLD_QUERY})
    found = PROBE_AT_LINE.findall(answer.get("output", ""))
    return int(found[-1]) if found and not answer.get("error") else None


def undo_to_base(name: str, base: int) -> tuple[bool, str]:
    """Put the probe session back at its checkpoint; (clean?, what was done)."""
    now = world_command(name)
    if now == base:
        return True, "clean"
    if now is None or now < base:
        return False, f"cannot read the world (command {now}, checkpoint {base})"
    answer = ask(name, {"op": "send", "form": f"(ubu! '{PROBE_BASE})"})
    after = world_command(name)
    if after == base and not answer.get("error"):
        return True, f"undid {now - base} command(s) above the checkpoint"
    return False, (f"undo to {PROBE_BASE} left the world at command {after}, "
                   f"checkpoint {base}")


def probe(args) -> int:
    """Prove a copy of EVENT in a second session loaded up to just before it.

    The probe session carries a checkpoint: the label fn-probe-base and the
    absolute command number the world had right after it.  Every probe first
    checks the world is at the checkpoint (undoing with `ubu!` whatever an
    earlier probe or a hand `send` left above it), sends its forms, then
    undoes them and checks again.  A probe that cannot restore the
    checkpoint reloads the session (a fresh world) and says so: a trial
    theorem left behind as a rewrite rule would make every later step count
    wrong (proof-cost-steps, 2026-09-27).
    """
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
    event_name = head_and_name(event_form)[1]
    from_source = list(main_state.get("ld") or []) if not args.book else []
    for extra in args.ld or []:
        if normalize_book(extra) not in from_source:
            from_source.append(normalize_book(extra))
    name = f"{args.name}.probe"
    idle_seconds = idle_from_args(args)
    if (session_dir(args.name) / "sock").exists():
        # A probe is work on the session it probes beside: keep that one alive too.
        with contextlib.suppress(SystemExit, OSError, ValueError):
            ask(args.name, {"op": "touch"}, timeout=30)
    identity = probe_identity(book, text, places[index][0], from_source)
    marker = session_dir(name) / "probe.json"
    replacement = args.form
    if replacement == "-":
        replacement = sys.stdin.read()
    try:
        attempts = probe_attempts(replacement or event_form, event_name, args.hints)
    except ValueError as error:
        raise SystemExit(f"proof-repl probe: cannot read the probe's forms or set "
                         f":hints: {error}") from None

    def load() -> int | None:
        if (session_dir(name) / "sock").exists():
            stop(argparse.Namespace(name=name))
        print(f"proof-repl probe: loading {book} up to #{index + 1} "
              f"({form_label(index + 1, event_form)}) in session {name}")
        started = start(argparse.Namespace(
            name=name, book=book, upto=f"#{index + 1}", through=None,
            limit=args.limit or 60.0, load_timeout=args.load_timeout,
            lane=main_state.get("lane") or getattr(args, "lane", None),
            idle_seconds=idle_seconds, ld=from_source, ld_missing=False,
            certify_missing=False, certify_jobs=4,
            load_limit=main_state.get("load_limit"),
            ld_local=bool(main_state.get("ld_local")) and not args.book))
        state = read_state(name) or {}
        if started != 0 or state.get("stopped_at"):
            print(f"proof-repl probe: the session could not load {book} up to the event")
            return None
        ask(name, {"op": "send", "form": f"(deflabel {PROBE_BASE})"})
        base = world_command(name)
        if base is None:
            print("proof-repl probe: the session cannot report its world's command number")
            return None
        marker.write_text(json.dumps({"identity": identity, "book": book,
                                      "event": args.event, "base": base}) + "\n")
        return base

    try:
        previous = json.loads(marker.read_text())
    except (OSError, json.JSONDecodeError):
        previous = {}
    probe_state = read_state(name) or {}
    reusable = (previous.get("identity") == identity
                and isinstance(previous.get("base"), int)
                and (session_dir(name) / "sock").exists()
                and probe_state.get("ready") and not probe_state.get("stopped_at"))
    base = previous.get("base") if reusable else None
    if reusable:
        clean, how = undo_to_base(name, base)
        if clean:
            print(f"proof-repl probe: reusing {name} (loaded up to #{index + 1} of {book}; "
                  f"world at its checkpoint: {how})")
        else:
            print(f"proof-repl probe: {name} is not at its checkpoint ({how}); reloading")
            base = None
    if base is None:
        base = load()
        if base is None:
            return 1

    extra = sent_events(args.name) if not args.book else []
    if extra and not getattr(args, "with_sent", False):
        print(f"proof-repl probe: {len(extra)} event(s) sent by hand to {args.name} are not "
              f"in the probe (it loads {book} from the file); --with-sent sends them first: "
              + ", ".join(head_and_name(form)[1] or form.strip()[:30] for form in extra[:6])
              + (" ..." if len(extra) > 6 else ""))
    elif extra:
        attempts = extra + attempts
        print(f"proof-repl probe: sending the {len(extra)} event(s) sent by hand to "
              f"{args.name} first (undone with the attempt)")

    totals = Totals()
    refused = timed_out = False
    for position, attempt in enumerate(attempts, 1):
        answer = ask(name, {"op": "send", "form": attempt, "limit": args.limit})
        output = answer.get("output", "")
        cost = measure(output)
        refused = bool(answer.get("error"))
        label = (form_label(index + 1, event_form) if len(attempts) == 1
                 else form_label(position, attempt))
        totals.add(label, cost, answer.get("elapsed"), refused)
        if len(attempts) > 1:
            print(f"{'REFUSED' if refused else 'ok':8}{label}: "
                  f"{cost_words(cost, answer.get('elapsed'))}", flush=True)
        if len(attempts) == 1 or refused or args.full:
            print(output if args.full else brief(output, where=save_output(name, output)))
        timed_out = bool(answer.get("timed_out"))
        if timed_out or refused:
            break
    _, last_cost = totals.costs[-1]
    verdict = "REFUSED" if refused else "admitted"
    if len(attempts) == 1:
        print(f"[probe {form_label(index + 1, event_form)} of {book}: {verdict}; "
              f"{cost_words(last_cost, answer.get('elapsed'))}]")
    else:
        print(f"[probe {form_label(index + 1, event_form)} of {book} ({len(attempts)} forms): "
              f"{verdict}; last form {cost_words(last_cost)}]")
        print(totals.line())
    if timed_out:
        print(f"[the probe outlived the hard limit; session {name} was killed]")
        return 1
    clean, how = undo_to_base(name, base)
    if not clean:
        print(f"[probe: COULD NOT restore the checkpoint ({how}); stopping {name} so the "
              "next probe reloads a fresh world]")
        stop(argparse.Namespace(name=name))
        return 1
    print(f"[probe undone: world back at its checkpoint (command {base})]")
    if args.stop:
        stop(argparse.Namespace(name=name))
    else:
        print(f"[session {name} stays at the event for the next probe; it stops itself "
              f"after {_duration(idle_seconds) if idle_seconds else 'never'} idle, "
              f"or: proof_repl.py stop {name}]")
    return 1 if refused else 0


def stop_holder(name: str) -> int:
    """No socket: end a `start` (or server) still holding NAME's lock, by the PID it recorded."""
    fd = open_session_lock(name)
    if fd is not None:
        os.close(fd)
        print(f"proof-repl: no live session {name!r}")
        return 1
    holder = lock_holder(name)
    pid = holder.get("pid")
    pids = [one for one in (pid, holder.get("starter")) if _is_holder(one, name)]
    if not pids:
        print(f"proof-repl: session {name!r} has no socket and its lock is "
              f"{holder_words(name)}; nothing of this tool's to stop")
        return 1
    for one in pids:
        with contextlib.suppress(ProcessLookupError, PermissionError):
            os.kill(one, signal.SIGTERM)
    deadline = time.monotonic() + 15
    while time.monotonic() < deadline:
        fd = open_session_lock(name)
        if fd is not None:
            os.close(fd)
            print(f"proof-repl: stopped {name} (its {holder.get('role')}, pid "
                  f"{', '.join(map(str, pids))}, held the lock with no socket)")
            return 0
        time.sleep(0.1)
    print(f"proof-repl: pid {pid} of session {name!r} did not release the lock")
    return 1


def stop(args) -> int:
    if not (session_dir(args.name) / "sock").exists():
        return stop_holder(args.name)
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


def _process_cwd(pid: int) -> Path | None:
    """PID's working directory where /proc says (Linux); None elsewhere."""
    try:
        return Path(os.readlink(f"/proc/{pid}/cwd")).resolve()
    except OSError:
        return None


def _is_server(pid, name: str, tree: Path | None = None) -> bool:
    """PID is still this session's `proof_repl.py serve NAME` (not a reused PID).

    With TREE, and where /proc names the process's working directory, it
    must also be TREE: the same session name exists in many lanes' trees.
    """
    if not isinstance(pid, int) or pid <= 1:
        return False
    words = _command_of(pid).split()
    if not ("serve" in words and name in words
            and any(word.endswith("proof_repl.py") for word in words)):
        return False
    if tree is not None:
        cwd = _process_cwd(pid)
        if cwd is not None and cwd != tree.resolve():
            return False
    return True


def _is_acl2_group(pgid) -> bool:
    """PGID is still a pooled ACL2 wrapper (tools/acl2) this tool started."""
    if not isinstance(pgid, int) or pgid <= 1:
        return False
    return any(word.endswith("tools/acl2") for word in _command_of(pgid).split())


def live_server_trees(proc: Path = Path("/proc")) -> list[Path]:
    """The trees of this machine's running `proof_repl.py serve` processes.

    Where /proc exists (the boxes): a server runs with its tree as its
    working directory, which finds trees the bases miss (a scratch tree one
    level deeper, a lane whose remote tree took a path as its name).  Only
    finds where to read state; what is stopped is still decided by each
    session's own state and the checks on its recorded PID.
    """
    found = []
    if not proc.is_dir():
        return found
    for entry in proc.iterdir():
        if not entry.name.isdigit():
            continue
        try:
            words = (entry / "cmdline").read_bytes().split(b"\0")
        except OSError:
            continue
        if not (b"serve" in words and any(word.endswith(b"proof_repl.py") for word in words)):
            continue
        with contextlib.suppress(OSError):
            found.append(Path(os.readlink(entry / "cwd")))
    return sorted(set(found))


def box_trees(environ=os.environ) -> list[str]:
    """Every tree on this machine that holds proof_repl sessions.

    This tree; the main checkout and its build/lanes/* (a lane worktree's
    main checkout is three levels up); and each directory under the boxes'
    gate and scratch bases (/tank/fn/gates, /tank/fn/scratch on hbox,
    ~/fn-gates on persvati).  Only trees with a build/proof-repl count.
    """
    candidates = [ROOT]
    main = ROOT.parents[2] if ROOT.parent.name == "lanes" and ROOT.parent.parent.name == "build" \
        else ROOT
    candidates.append(main)
    lanes = main / "build" / "lanes"
    if lanes.is_dir():
        candidates += sorted(lanes.iterdir())
    for base in BOX_TREE_BASES:
        directory = Path(os.path.expanduser(base))
        if directory.is_dir():
            candidates += sorted(directory.iterdir())
    candidates += live_server_trees()
    found, seen = [], set()
    for tree in candidates:
        with contextlib.suppress(OSError):
            if not (tree / "build" / "proof-repl").is_dir():
                continue
            key = tree.resolve()
            if key not in seen:
                seen.add(key)
                found.append(str(tree))
    return found


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
        tree = directory.parent.parent.parent
        server = _is_server(state.get("pid"), directory.name, tree)
        socket_file = (directory / "sock").exists()
        rows.append({"name": directory.name, "state": state, "directory": directory,
                     "tree": tree,
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
    roots = getattr(args, "root", None) or (box_trees() if getattr(args, "all", False) else None)
    if roots is not None and getattr(args, "all", False):
        args.root = roots
    rows = session_rows(roots)
    if not rows:
        print("proof-repl: no sessions")
        return 0
    print(f"{'name':24} {'status':6} {'lane':24} {'age':>7} {'idle':>7} {'deadline':>8} "
          f"{'left':>7} book")
    for row in rows:
        state = row["state"]
        status_word = ("live" if row["live"] else
                       "stale" if row["socket"] else
                       "ended" if state.get("ended") else "dead")
        deadline = row["deadline"]
        left = (_duration(deadline - row["idle"]) if deadline and row["live"] else "-")
        print(f"{row['name']:24} {status_word:6} {(state.get('lane') or '-'):24} "
              f"{_duration(row['age']):>7} {_duration(row['idle']):>7} "
              f"{(_duration(deadline) if deadline else 'none'):>8} {left:>7} {state.get('book')}"
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


def reap_one(row: dict, reason: str | None = None) -> str:
    """Stop one session: its own `stop` first, then only the PIDs its state names."""
    name, state = row["name"], row["state"]
    tree = row.get("tree")
    kind = "idle" if reason and reason.startswith("idle") else f"reaped: {reason}"
    if row["server"] and row["socket"]:
        try:
            if ask(name, {"op": "stop", "reason": kind, "by": "proof_repl.py reap"},
                   timeout=30, sock_path=row["directory"] / "sock").get("stopped"):
                return "stopped through its socket"
        except (SystemExit, OSError, ValueError):
            pass
    signalled = []
    if row["server"] and _is_server(state.get("pid"), name, tree):
        with contextlib.suppress(ProcessLookupError, PermissionError):
            os.kill(state["pid"], signal.SIGTERM)
            signalled.append(f"server {state['pid']}")
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline and _is_server(state.get("pid"), name, tree):
            time.sleep(0.1)
    pgid = state.get("acl2_pgid")
    if _is_acl2_group(pgid):
        with contextlib.suppress(ProcessLookupError, PermissionError):
            os.killpg(pgid, signal.SIGTERM)
            signalled.append(f"ACL2 group {pgid}")
    if not _is_server(state.get("pid"), name, tree):
        (row["directory"] / "sock").unlink(missing_ok=True)
    if signalled and reason:
        write_stop_note(row["directory"], kind, row["idle"], row["deadline"],
                        "proof_repl.py reap (signal)")
    return ("signalled " + ", ".join(signalled)) if signalled else "removed a stale socket"


def reap(args) -> int:
    older_than = args.older_than
    if getattr(args, "idle", None) is not None:
        older_than = args.idle * 60
    everywhere = getattr(args, "all", False) or getattr(args, "idle", None) is not None
    roots = args.root or (box_trees() if everywhere else None)
    rows = session_rows(roots)
    chosen = [(row, reason) for row in rows
              for reason in [reap_reason(row, args.lane, older_than)] if reason]
    if not chosen:
        print("proof-repl: nothing to reap" + (f" in {len(roots)} trees" if roots else ""))
        return 0
    for row, reason in chosen:
        lane = row["state"].get("lane") or "-"
        where = f" [{row['tree']}]" if roots else ""
        if args.dry_run:
            print(f"would reap {row['name']} (lane {lane}, book {row['state'].get('book')}): "
                  f"{reason}{where}")
            continue
        print(f"reaped {row['name']} (lane {lane}): {reason}; {reap_one(row, reason)}{where}")
    return 0


# --- gc: the reaper the batch runner runs each cycle (Q7g) -------------------------

# cert-images (2026-09-29): idle sessions of finished lanes held all 22 of
# persvati's ACL2 slots.  `gc` stops every session on the machine idle at least
# GC_IDLE_MINUTES (in every session tree, as `reap --idle` does); `--each-box`
# runs it on every farm box in turn.
GC_IDLE_MINUTES = 30.0


def gc(args) -> int:
    if getattr(args, "each_box", False):
        worst = 0
        for host in sorted(REMOTE_TREES):
            print(f"== proof_repl gc on {host}", flush=True)
            argv = ["gc", "--idle", f"{args.idle:g}", "--host", host]
            if args.dry_run:
                argv.append("--dry-run")
            try:
                worst = max(worst, main(argv))
            except SystemExit as stop:  # one unreachable box never hides the other
                print(f"proof_repl gc on {host}: {stop}", flush=True)
                worst = max(worst, 1)
        return worst
    return reap(argparse.Namespace(lane=None, older_than=None, idle=args.idle, all=True,
                                   dry_run=args.dry_run, root=args.root))


# --- diff: the session's events against the book's text (Q7g) ----------------------

# owner-relation (2026-09-28): a theorem admitted in the session as a rewrite
# rule and written to the book as :rule-classes nil gave a false green.  `diff
# NAME BOOK` asks the session, for each named event of BOOK, whether the world's
# event form is EQUAL to the book's form as ACL2 reads it (so whitespace and
# comments never count).  A defund/defthmd is compared as the defun/defthm it
# expands to; an event some other macro generates is reported "macro", not
# compared.
DIFF_ALIASES = {"defund": "defun", "defthmd": "defthm"}
DIFF_VERDICT = re.compile(r"\(\s*([^\s()]+)\s+\.\s+:(SAME|DIFFERS|ABSENT|MACRO)\s*\)", re.IGNORECASE)


def diff_items(text: str) -> list[tuple[str, str]]:
    """(name, form) for each named event of TEXT, `local` unwrapped, aliases applied."""
    items = []
    for form in forms(text):
        body = form.strip()
        inner = re.match(r"^\(\s*local\s+(\(.*\))\s*\)$", body, re.IGNORECASE | re.DOTALL)
        if inner:
            body = inner.group(1)
        head, name = head_and_name(body)
        if not name or head in ("include-book", "in-package", "in-theory"):
            continue
        alias = DIFF_ALIASES.get(head)
        if alias:
            body = re.sub(r"^\(\s*" + re.escape(head), "(" + alias, body, count=1, flags=re.IGNORECASE)
        items.append((name, body))
    return items


def diff_form(items: list[tuple[str, str]]) -> str:
    """One ACL2 form printing (NAME . :SAME|:DIFFERS|:ABSENT|:MACRO) for each item."""
    rows = []
    for name, body in items:
        rows.append(f"(cons '{name} (let ((ev (get-event '{name} (w state))) (bk '{body}))"
                    " (cond ((null ev) :absent) ((equal ev bk) :same)"
                    " ((not (eq (car ev) (car bk))) :macro) (t :differs))))")
    return "(cw \"~x0~%\" (list " + " ".join(rows) + "))"


def diff_verdicts(output: str) -> dict[str, str]:
    return {m.group(1).lower(): m.group(2).lower() for m in DIFF_VERDICT.finditer(output)}


def diff(args) -> int:
    items = diff_items(book_path(args.book).read_text(encoding="utf-8"))
    if not items:
        print(f"proof-repl diff: no named events in {args.book}")
        return 0
    answer = ask(args.name, {"op": "send", "form": diff_form(items), "limit": args.limit})
    if answer.get("error"):
        print(brief(answer.get("output", "")))
        return 2
    verdicts = diff_verdicts(answer.get("output", ""))
    counts: dict[str, int] = {}
    for name, _ in items:
        verdict = verdicts.get(name, "unanswered")
        counts[verdict] = counts.get(verdict, 0) + 1
        if verdict == "differs" or (verdict in ("absent", "macro", "unanswered") and args.all):
            print(f"{verdict.upper():10} {name}")
    print("proof-repl diff: " + ", ".join(f"{n} {v}" for v, n in sorted(counts.items()))
          + f" of {len(items)} named events in {args.book}")
    return 1 if counts.get("differs") else 0


# --- running a session on another box ------------------------------------------

# Where a lane's REPL tree lives on each box (relative paths are under the
# remote home).  The toolchain, the cache and the wrapper come from
# tools/farm.py's HOSTS, the one table of what each box certifies with.
# Both boxes run the same ACL2 build (w28, identity d5f2b9f0), and each
# reads its own cache; tools/cert_cache_sync.py (which farm's fetch runs)
# copies one box's new certificates into the other's.
REMOTE_TREES = {"persvati": "fn-gates", "hbox": "/tank/fn/gates"}
# Subcommands whose remote process may start a session server: on hbox they
# run under swarm-build, whose scope carries the enforced memory cap and
# makes the server killable (an ssh child inherits sshd's OOM immunity).
SERVER_COMMANDS = ("start", "probe")
SYNC_EXCLUDES = ("__pycache__", ".pyc")
SSH_OPTIONS = ("-o", "ControlMaster=auto", "-o", "ControlPersist=600",
               "-o", "ControlPath=~/.ssh/fn-proof-repl-%r@%h:%p",
               "-o", "ServerAliveInterval=30")


def farm_hosts() -> dict:
    return acl2_slots.farm_hosts()


def box_settings(host: str) -> dict:
    hosts = farm_hosts()
    if host not in hosts:
        raise SystemExit(f"proof-repl: --host {host!r}: known boxes are "
                         + ", ".join(sorted(hosts)))
    return dict(hosts[host])


def apply_box_defaults(environ=os.environ, hostname: str | None = None) -> str | None:
    """On a farm box, default FN_ACL2 and FN_CERT_CACHE to that box's own
    (acl2_slots.apply_box_defaults; openbsd-release-fixes)."""
    return acl2_slots.apply_box_defaults(environ, hostname)


# `--host laptop`: this machine, when it is not a farm box.  Only REPL
# sessions run here; the farm and remote_check never name it.
LOCAL_HOST = "laptop"


def apply_local_defaults(environ=os.environ) -> str | None:
    """Off the farm boxes, default FN_ACL2 to this machine's launcher file.

    ~/.config/fn/acl2 (acl2_slots.configured_acl2) names the qualified
    launcher; without it FN_ACL2 stays unset and `acl2` on PATH is used, as
    before.  Only the local path calls this: `--host BOX` forwards this
    shell's FN_ACL2 to the box, and a laptop path there would be wrong.
    """
    if "FN_ACL2" in environ:
        return None
    chosen = acl2_slots.configured_acl2(environ)
    if chosen == "acl2":
        return None
    environ["FN_ACL2"] = chosen
    return chosen


def laptop_offer(environ=os.environ) -> tuple[float, int] | None:
    """(load per core, free pool slots) when this machine may take a session.

    None when it is a farm box, FN_REPL_LAPTOP=0, its configured ACL2 is not
    a qualified launcher (the proof_repl cache refuses one), or every slot
    of its pool is held.
    """
    if environ.get("FN_REPL_LAPTOP", "1").strip() == "0":
        return None
    if socket.gethostname().split(".")[0] in REMOTE_TREES:
        return None
    configured = acl2_slots.configured_acl2(environ)
    found = configured if "/" in configured else shutil.which(configured)
    if not found or not acl2_toolchain.fingerprint(Path(found)).qualified:
        return None
    free = acl2_slots.slot_count() - len(acl2_slots.holders())
    if free <= 0:
        return None
    return os.getloadavg()[0] / (os.cpu_count() or 1), free


def local_cache_gap(book: str, cache: Path | None = None,
                    toolchain: str | None = None) -> tuple[int, int]:
    """(dependencies of BOOK this machine's cache has no certificate for, all of them).

    `--host auto` weighed the laptop on load alone and took it with a cache
    that lacked 76 and 87 books of dev's closure (operations, auth-tls-bugs,
    2026-09-28): the start then refused and the lane forced --host hbox.  A
    dependency counts as held when the cache has an entry for its closure key
    at these bytes (for TOOLCHAIN, when named).  An unreadable closure is
    all gap.
    """
    cache = certs.cache_directory() if cache is None else cache
    try:
        graph = include_graph(ROOT, normalize_book(book))
    except (OSError, certs.UnreadableBook, ValueError):
        return 1, 1
    wanted = [name for name in graph if name != normalize_book(book)]
    lacking = 0
    for name in wanted:
        try:
            entries = certs.book_entries(ROOT, cache, name)
        except (OSError, certs.UnreadableBook):
            entries = []
        if toolchain:
            entries = [one for one in entries
                       if one[1].get("toolchain_identity") in (None, toolchain)]
        if not entries:
            lacking += 1
    return lacking, len(wanted)


def laptop_toolchain(environ=os.environ) -> str | None:
    configured = acl2_slots.configured_acl2(environ)
    found = configured if "/" in configured else shutil.which(configured)
    return acl2_toolchain.fingerprint(Path(found)).identity if found else None


def remote_tree(host: str, lane: str | None, override: str | None = None) -> str:
    if override:
        return override
    if not lane:
        raise SystemExit("proof-repl: --host needs a lane to name the remote tree: run from "
                         "build/lanes/NAME, set FN_LANE, or pass --remote-tree PATH")
    return f"{REMOTE_TREES[host]}/{lane}-repl"


def sync_files(books: list[str], extra: list[str] = ()) -> list[str]:
    """The files a remote session needs: tools/, host/ and the named books' include closures.

    Never planning/ (hundreds of MB): the closure is what `start` reads,
    certifies and loads.  Certificates are not copied; the box installs
    its own from its own cache.
    """
    wanted: set[str] = set(extra)
    for directory, _, names in os.walk(ROOT / "tools"):
        if any(part in directory for part in SYNC_EXCLUDES):
            continue
        for name in names:
            if not name.endswith(SYNC_EXCLUDES):
                wanted.add(str(Path(directory, name).relative_to(ROOT)))
    # The host files too (2.6 MB): a session that `ld`s them (the coverage
    # dump over image-world + tools/extract/world-host.lisp) found none on
    # the box's tree (obstructions-3 item 14).
    for path in sorted((ROOT / "host").rglob("*.lisp")):
        wanted.add(str(path.relative_to(ROOT)))
    for book in books:
        try:
            graph = include_graph(ROOT, normalize_book(book))
        except (OSError, certs.UnreadableBook, ValueError) as error:
            raise SystemExit(f"proof-repl: cannot read {book}'s closure: {error}") from None
        wanted.update(f"{name}.lisp" for name in graph)
    return sorted(wanted)


def ssh_command(host: str, script: str) -> list[str]:
    return ["ssh", *SSH_OPTIONS, host, script]


def sync_to(host: str, tree: str, files: list[str]) -> float:
    """rsync FILES (paths under ROOT) into TREE on HOST; answers the seconds it took."""
    started = time.monotonic()
    listing = "\n".join(files) + "\n"
    command = ["rsync", "-a", "--files-from=-", "-e", "ssh " + " ".join(SSH_OPTIONS),
               f"--rsync-path=mkdir -p {tree} && rsync", f"{ROOT}/", f"{host}:{tree}/"]
    done = subprocess.run(command, input=listing, text=True, capture_output=True)
    if done.returncode:
        raise SystemExit(f"proof-repl: rsync to {host}:{tree} exited {done.returncode}: "
                         + done.stderr.strip()[-400:])
    return time.monotonic() - started


def strip_remote_options(argv: list[str]) -> list[str]:
    """ARGV without --host/--remote-tree/--acl2/--no-sync, which only this side
    reads (--acl2 goes to the box as its FN_ACL2)."""
    kept, skip = [], False
    for word in argv:
        if skip:
            skip = False
            continue
        if word in ("--host", "--remote-tree", "--acl2"):
            skip = True
            continue
        if word.startswith(("--host=", "--remote-tree=", "--acl2=")) or word == "--no-sync":
            continue
        kept.append(word)
    return kept


def remote_acl2(args, environ=os.environ) -> str | None:
    """The ACL2 a --host command runs with, when not the box's default.

    `--acl2 PATH` wins, then FN_ACL2 from this shell; None keeps the box's
    own (tools/farm.py HOSTS).  extract-2, 2026-09-27: an image's world plus
    host files exhausted hbox's default (tls 16384) with "Thread local
    storage exhausted", and --host offered no way to pick
    /tank/fn/toolchains/w28/acl2-literal-4g-tls64k.
    """
    chosen = getattr(args, "acl2", None) or environ.get("FN_ACL2", "").strip()
    return chosen or None


def remote_script(host: str, tree: str, lane: str | None, argv: list[str],
                  acl2: str | None = None) -> str:
    settings = box_settings(host)
    import shlex  # noqa: E402
    exports = [f"FN_ACL2={shlex.quote(acl2) if acl2 else settings['acl2']}",
               f"FN_CERT_CACHE={settings['cache']}"]
    if lane:
        exports.append(f"FN_LANE={shlex.quote(lane)}")
    wrap = settings.get("wrap") or ""
    command = ("python3 tools/proof_repl.py " + " ".join(shlex.quote(word) for word in argv))
    if wrap and argv and argv[0] in SERVER_COMMANDS:
        command = f"{wrap} {command}"
    return f"cd {tree} && export {' '.join(exports)} && {command}"


def remote_digest(host: str, tree: str, relative: str) -> str | None:
    """The SHA-256 of TREE/RELATIVE on HOST, or None when it is not there."""
    import shlex  # noqa: E402
    script = (f"cd {tree} && python3 -c 'import hashlib,sys; "
              "print(hashlib.sha256(open(sys.argv[1],\"rb\").read()).hexdigest())' "
              f"{shlex.quote(relative)}")
    done = subprocess.run(ssh_command(host, script), capture_output=True, text=True,
                          stdin=subprocess.DEVNULL)
    text = done.stdout.strip()
    return text if done.returncode == 0 and re.fullmatch(r"[0-9a-f]{64}", text) else None


def refuse_stale_remote(host: str, tree: str, relative: str,
                        digest_of=remote_digest) -> None:
    """--no-sync runs the box's copy: refuse when it is not this one.

    defprotocol, 2026-09-27: an edit made after the last sync silently did
    not run, and the refusal it caused read like a proof problem.
    """
    local = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
    remote = digest_of(host, tree, relative)
    if remote != local:
        raise SystemExit(
            f"proof-repl: --no-sync would run {host}:{tree}/{relative} "
            f"(sha256 {remote[:16] if remote else 'absent'}), which is not this tree's "
            f"{relative} (sha256 {local[:16]}); drop --no-sync to sync it first")


# The commands about one existing session: without --host they go to the
# machine its start recorded.
SESSION_COMMANDS = ("send", "send-range", "send-file", "resync", "status", "stop", "probe",
                    "diff", "checkpoints")

# Minutes `start --host BOX` waits for another lane's reservation of BOX.
# config-and-legacy and operations (2026-09-28) waited 10 and 13 minutes in
# `boxes.sh wait` with nothing on the screen (its note went to a `| tail`):
# a longer lease is refused at once, naming its holder and expiry.
DEFAULT_LEASE_WAIT = 2.0


def box_lease(host: str, checker=None) -> tuple[str, int] | None:
    """(`boxes.sh`'s line naming the holder and expiry, minutes left) of a
    lease on HOST held by another lane, or None when it is free (or ours)."""
    if checker is None:
        def checker():
            done = subprocess.run(["sh", str(ROOT / "tools" / "boxes.sh"), "check", host],
                                  capture_output=True, text=True, check=False)
            return done.returncode, done.stderr
    code, text = checker()
    if code != 4:
        return None
    line = next((one for one in text.splitlines() if " reserved by " in one), text.strip())
    left = re.search(r"\((\d+) min left\)", line)
    return line.removeprefix("boxes: "), int(left.group(1)) if left else 0


def refuse_or_wait_for_lease(host: str, wait_minutes: float, checker=None,
                             waiter=None) -> None:
    held = box_lease(host, checker)
    if held is None:
        return
    line, left = held
    print(f"proof-repl --host {host}: {line}", file=sys.stderr, flush=True)
    if left > wait_minutes:
        raise SystemExit(
            f"proof-repl: {host} is reserved for {left} more min (over --lease-wait "
            f"{wait_minutes:g}); no session started: use --host auto (the other box), "
            f"--lease-wait {left + 1}, or FN_BOX_RESERVATION=ignore when you are its holder")
    print(f"proof-repl --host {host}: waiting up to {wait_minutes:g} min for the lease",
          file=sys.stderr, flush=True)
    if waiter is None:
        def waiter():
            return subprocess.run(["sh", str(ROOT / "tools" / "boxes.sh"), "wait", host,
                                   "--max", str(max(1, int(wait_minutes + 0.999)))],
                                  check=False).returncode
    if waiter() != 0:
        raise SystemExit(f"proof-repl: {host} is still reserved (tools/boxes.sh); "
                         "no session started")


def remember_host(name: str, host: str | None, tree: str | None = None,
                  book: str | None = None, lane: str | None = None) -> None:
    """Record which machine session NAME runs on (build/proof-repl/NAME/remote.json).

    Written before a remote start runs, so send/send-range/status/stop after
    a failed or interrupted start still go to that box without --host again
    (full-vs-uncertain, 2026-09-28: "no live session" from the local look);
    a local start removes it, so a name reused on another machine follows the
    newest start (time-bars: one name on two hosts confused resync).
    """
    directory = session_dir(name)
    record = directory / "remote.json"
    if host is None:
        record.unlink(missing_ok=True)
        return
    directory.mkdir(parents=True, exist_ok=True)
    record.write_text(json.dumps({"host": host, "tree": tree, "book": book,
                                  "lane": lane}) + "\n")


def recorded_host(name: str | None) -> str | None:
    if not name:
        return None
    with contextlib.suppress(OSError, KeyError, ValueError, TypeError):
        return json.loads((session_dir(name) / "remote.json").read_text())["host"]
    return None


def recorded_session(name: str | None) -> dict:
    """The record `start` wrote for session NAME (host, tree, book, lane), or {}."""
    if not name:
        return {}
    with contextlib.suppress(OSError, ValueError, TypeError):
        record = json.loads((session_dir(name) / "remote.json").read_text())
        if isinstance(record, dict):
            return record
    return {}


def remote_lane_and_tree(args, host: str) -> tuple[str | None, str]:
    """The lane and box tree a --host command runs in.

    `start` takes them from --lane/--remote-tree, else $FN_LANE or the
    worktree's name.  Every later command about that session (send,
    send-range, resync, status, stop, probe, diff, checkpoints) takes them
    from the record `start` wrote when it is for the same box, so a shell
    without FN_LANE -- the main checkout, a sub-agent's -- reaches the same
    tree (obstructions-5 item 31); an explicit --lane/--remote-tree still wins.
    """
    record = {} if args.command == "start" else recorded_session(getattr(args, "name", None))
    if record.get("host") != host:
        record = {}
    lane = getattr(args, "lane", None) or record.get("lane") or default_lane()
    override = getattr(args, "remote_tree", None) or (
        record.get("tree") if not getattr(args, "lane", None) else None)
    return lane, remote_tree(host, lane, override)


# Run on the box (python3, no tools/ needed): each session of TREE other than
# NAME whose lock record names a live proof_repl.py start/serve/probe of it.
LIVE_SIBLINGS_SCRIPT = r"""
import json, os, sys
tree, name = sys.argv[1], sys.argv[2]
locks = os.path.join(tree, "build", "proof-repl", ".locks")
try:
    entries = sorted(os.listdir(locks))
except OSError:
    entries = []
for other in entries:
    base = other[:-len(".probe")] if other.endswith(".probe") else other
    if base == name:
        continue
    try:
        pid = int(json.load(open(os.path.join(locks, other))).get("pid") or 0)
        words = open("/proc/%d/cmdline" % pid, "rb").read().decode().split("\0")
    except (OSError, ValueError, AttributeError):
        continue
    if any(w.endswith("proof_repl.py") for w in words) and base in words:
        print(base)
"""


def live_siblings(host: str, tree: str, name: str, runner=None) -> list[str] | None:
    """The other live sessions in HOST's TREE (None: the box did not answer)."""
    script = (f"python3 - {shlex.quote(tree)} {shlex.quote(name)} <<'FN_SIBLINGS'\n"
              f"{LIVE_SIBLINGS_SCRIPT}\nFN_SIBLINGS")
    try:
        done = (runner or subprocess.run)(ssh_command(host, script), stdin=subprocess.DEVNULL,
                                          text=True, capture_output=True, timeout=60)
    except subprocess.TimeoutExpired:
        return None
    if done.returncode:
        return None
    return sorted({line.strip() for line in done.stdout.splitlines() if line.strip()})


def own_remote_tree(args, host: str, lane: str | None, tree: str, runner=None) -> str:
    """The tree a remote `start` of args.name uses (obstructions-9 item 79).

    Two sessions of one lane on one box shared <lane>-repl: each start's
    rsync rewrote the books and tools/ under the other's load.  When another
    session is live in the lane's tree, this start takes its own tree
    <lane>-repl-<NAME> and says so; an explicit --remote-tree is refused by
    name instead, since its owner chose that directory.
    """
    others = live_siblings(host, tree, args.name, runner)
    if not others:
        return tree
    if getattr(args, "remote_tree", None):
        raise SystemExit(f"proof-repl: --host {host}: session(s) {', '.join(others)} are live "
                         f"in {tree}; a second session there races their sync and load. "
                         f"Stop them, or pass another --remote-tree")
    own = f"{tree}-{args.name}"
    print(f"proof-repl --host {host}: session(s) {', '.join(others)} of lane {lane} are live "
          f"in {tree}; session {args.name!r} gets its own tree {own} (item 79)", flush=True)
    return own


def changed_dependencies(book: str, named=(), base_ref: str = "origin/dev") -> list[str]:
    """The books of BOOK's closure (not BOOK) whose bytes here differ from
    the merge base with BASE_REF, committed or not, less those NAMED.

    obstructions-9 item 82 (operability-7): a lane that changed a WIDE book
    (books/native-admin) needs it from source in every session on a book
    that includes it, and a --host start learned so from the box's refusal
    only after the sync.  No box cache holds a certificate for bytes only
    this branch has, so `start --host` loads these from source (as --ld)
    and says so before syncing.
    """
    book = normalize_book(book)
    try:
        graph = include_graph(ROOT, book)
    except (OSError, certs.UnreadableBook, ValueError):
        return []

    def out(*words):
        done = subprocess.run(["git", "-C", str(ROOT), *words], capture_output=True, text=True)
        return done.stdout if done.returncode == 0 else None
    base = (out("merge-base", "HEAD", base_ref) or "").strip()
    if not base:
        return []
    changed = set((out("diff", "--name-only", base, "--") or "").split())
    changed |= set((out("ls-files", "--others", "--exclude-standard") or "").split())
    wanted = {normalize_book(one) for one in named}
    return sorted(name for name in graph
                  if name != book and f"{name}.lisp" in changed and name not in wanted)


def run_remote(args, argv: list[str]) -> int:
    """This command, on args.host, in the lane's tree there, after syncing what it reads."""
    host = args.host
    lane, tree = remote_lane_and_tree(args, host)
    forwarded = strip_remote_options(argv)
    books: list[str] = []
    extra: list[str] = []
    early_stdin = None
    command = args.command
    if command == "start":
        # A box reserved for a measurement (tools/boxes.sh reserve): say who
        # holds it and until when at once, and wait only --lease-wait minutes
        # (`--host auto` already skipped it).
        refuse_or_wait_for_lease(host, getattr(args, "lease_wait", DEFAULT_LEASE_WAIT))
        books = [args.book, *(normalize_book(one) for one in getattr(args, "ld", None) or [])]
        source_deps = getattr(args, "source_deps", None)
        if source_deps and source_deps != "*":
            books += [normalize_book(one.strip()) for one in source_deps.split(",") if one.strip()]
        if not (source_deps == "*" or getattr(args, "ld_missing", False)
                or getattr(args, "certify_missing", False)):
            changed = changed_dependencies(args.book, books[1:])
            if changed:
                print(f"proof-repl --host {host}: {len(changed)} dependenc"
                      f"{'y' if len(changed) == 1 else 'ies'} of {normalize_book(args.book)} "
                      f"changed on this branch (no box has their certificates): "
                      f"{', '.join(changed)}; loading them from source (as --ld; the books "
                      "between that include them follow). --certify-missing certifies "
                      "them instead (item 82)", flush=True)
                books += changed
                for one in changed:
                    forwarded += ["--ld", one]
    elif command == "probe":
        record = session_dir(args.name) / "remote.json"
        try:
            books = [args.book or json.loads(record.read_text())["book"]]
        except (OSError, KeyError, json.JSONDecodeError):
            raise SystemExit(f"proof-repl: --host probe: no record of session {args.name!r}'s "
                             "book here (start it with --host from this tree, or pass --book)")
        books += list(args.ld or [])
    elif command == "send":
        # A sent include of a repository book: its closure goes to the box.
        if args.form == "-":
            early_stdin = sys.stdin.read()
        record = session_dir(args.name) / "remote.json"
        with contextlib.suppress(OSError, KeyError, json.JSONDecodeError, ValueError):
            directory = (ROOT / f"{json.loads(record.read_text())['book']}.lisp").parent
            for one in commands(early_stdin if args.form == "-" else args.form):
                _, target = rooted_include(one, directory)
                if target is not None and (ROOT / f"{target}.lisp").is_file():
                    books.append(target)
                # A sent host load: the box's copy is refreshed first (item 84:
                # a stale host file there was re-tested once).
                loaded = host_load_target(one, directory)
                if loaded:
                    extra.append(loaded)
    elif command in ("list", "reap", "gc") and not getattr(args, "no_sync", False):
        extra.append("tools/proof_repl.py")  # sync_files adds the rest of tools/
    elif command in ("send-range", "resync", "diff", "send-file"):
        named = args.file if command == "send-file" else args.book
        path = book_path(named)
        if command == "send-file":
            # its includes' closures go to the box, as a sent include's does
            for one in forms(path.read_text(encoding="utf-8")):
                target = include_target(one, path.parent)
                if target is not None and (ROOT / f"{target}.lisp").is_file():
                    books.append(target)
        try:
            relative = path.relative_to(ROOT.resolve()).as_posix()
        except ValueError:
            # A scratch file outside the tree goes to build/proof-repl-files/.
            relative = None
        if relative is None:
            staged = SESSIONS.parent / "proof-repl-files" / path.name
            staged.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, staged)
            relative = staged.relative_to(ROOT).as_posix()
        extra.append(relative)
        forwarded = [relative if word == named else word for word in forwarded]
        if getattr(args, "no_sync", False):
            refuse_stale_remote(host, tree, relative)
    if command == "start":
        tree = own_remote_tree(args, host, lane, tree)
        remember_host(args.name, host, tree, normalize_book(args.book), lane)
    if (books or extra) and not getattr(args, "no_sync", False):
        files = sync_files(books, extra)
        seconds = sync_to(host, tree, files)
        print(f"proof-repl --host {host}: synced {len(files)} files to {tree} "
              f"({seconds:.1f} s)", flush=True)
    stdin_text = early_stdin
    if stdin_text is None and (command == "probe" and args.form == "-"):
        stdin_text = sys.stdin.read()
    acl2 = remote_acl2(args)
    if acl2 and command in SERVER_COMMANDS:
        print(f"proof-repl --host {host}: ACL2 {acl2} (not the box default "
              f"{box_settings(host)['acl2']}; certificates are keyed by toolchain, so the "
              "cache may miss)", flush=True)
    script = remote_script(host, tree, lane, forwarded, acl2)
    if stdin_text is None:
        done = subprocess.run(ssh_command(host, script), stdin=subprocess.DEVNULL)
    else:
        done = subprocess.run(ssh_command(host, script), input=stdin_text, text=True)
    return done.returncode


def resolve_auto_host(args, picker=None, offer=None, cache_gap=None) -> str:
    """`--host auto`: a session's own machine, else the least loaded one now.

    A command about an existing session (send, send-range, resync, status,
    stop, and probe beside it) goes where that session was started
    (remote.json; a session directory here without one is this machine's);
    `start` and the machine-wide `list`/`reap` pick the box with the lowest
    load per core (tools/boxes.sh --pick prints both).  `start` takes this
    machine instead when `laptop_offer` does and its load per core is below
    the picked box's: at most its pool's slots, sessions only -- and never
    when its certificate cache lacks any of the book's dependencies
    (`local_cache_gap`; a box's cache is the one the farm publishes to).
    """
    name = getattr(args, "name", None)
    if args.command != "start" and name:
        directory = session_dir(name)
        with contextlib.suppress(OSError, KeyError, json.JSONDecodeError):
            host = json.loads((directory / "remote.json").read_text())["host"]
            print(f"proof-repl --host auto: session {name!r} is on {host}", flush=True)
            return host
        if directory.is_dir() and args.command != "probe":
            print(f"proof-repl --host auto: session {name!r} is on this machine", flush=True)
            return LOCAL_HOST
        if args.command != "probe":
            raise SystemExit(f"proof-repl: --host auto: no record here of session {name!r}'s "
                             "box; name it (--host hbox|persvati|laptop)")
    if picker is None:
        def picker():
            done = subprocess.run(["sh", str(ROOT / "tools" / "boxes.sh"), "--pick"],
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  text=True, check=False)
            sys.stderr.write(done.stderr)
            host = done.stdout.strip() if done.returncode == 0 else ""
            load = re.search(rf"^boxes: {re.escape(host)} ([0-9.]+) load per core$",
                             done.stderr, re.MULTILINE) if host else None
            return host, (float(load.group(1)) if load else None)
    picked = picker()
    host, box_load = (picked, None) if isinstance(picked, str) else picked
    if args.command == "start":
        local = (offer or laptop_offer)()
        if local is not None:
            load, free = local
            lacking, wanted = (0, 0)
            if getattr(args, "book", None):
                lacking, wanted = (cache_gap or (lambda book: local_cache_gap(
                    book, toolchain=laptop_toolchain())))(args.book)
            if lacking and host in REMOTE_TREES:
                print(f"proof-repl --host auto: not this machine: its certificate cache "
                      f"lacks {lacking} of {args.book}'s {wanted} dependencies", flush=True)
            elif host not in REMOTE_TREES or box_load is None or load < box_load:
                print(f"proof-repl --host auto: this machine ({load:.2f} load per core, "
                      f"{free} free slot(s)) over {host or 'no box'}"
                      + (f" ({box_load:.2f})" if box_load is not None else ""), flush=True)
                return LOCAL_HOST
    if host not in REMOTE_TREES:
        raise SystemExit("proof-repl: --host auto: no build box answered (tools/boxes.sh)")
    return host


def add_remote_options(parser, sync: bool = False, lease: bool = False) -> None:
    parser.add_argument("--host", default=None, metavar="BOX",
                        help="run this on BOX (hbox, persvati, laptop = this machine, or "
                             "auto: a session's own machine, else the lower load per core, "
                             "the laptop included for start) in the lane's tree there, "
                             "with that box's ACL2 and certificate cache")
    parser.add_argument("--remote-tree", default=None, metavar="PATH",
                        help="with --host: the tree on the box (default: "
                             "<box's gates>/<lane>-repl)")
    parser.add_argument("--acl2", default=None, metavar="PATH",
                        help="the ACL2 executable (default FN_ACL2; with --host, else the "
                             "box's own). On hbox an image world plus host files wants "
                             "/tank/fn/toolchains/w28/acl2-literal-4g-tls64k")
    if sync:
        parser.add_argument("--no-sync", action="store_true",
                            help="with --host: do not rsync tools/ and the closure first")
    if lease:
        parser.add_argument("--lease-wait", type=float, default=DEFAULT_LEASE_WAIT,
                            metavar="MIN",
                            help="with --host BOX: when another lane reserved BOX, wait "
                                 "for a lease that ends within MIN minutes (default "
                                 f"{DEFAULT_LEASE_WAIT:g}); a longer one is refused at "
                                 "once, naming its holder and expiry")


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
    p.add_argument("--load-limit", type=float, default=None, metavar="S",
                   help="prover time limit per event while loading (default --limit; "
                        "0: none); a form over it is refused with its checkpoints")
    p.add_argument("--lane", default=None,
                   help="the owning lane (default $FN_LANE, else build/lanes/NAME)")
    p.add_argument("--idle-timeout", type=float, default=None, metavar="MIN",
                   help="stop the session after MIN minutes with no send (default "
                        f"$FN_REPL_IDLE_MIN, else {DEFAULT_IDLE_MINUTES:g}; 0: never)")
    p.add_argument("--idle-seconds", type=float, default=None, help=argparse.SUPPRESS)
    p.add_argument("--ld", action="append", default=[], metavar="DEPENDENCY",
                   help="a book the session's book INCLUDES (not the book itself): load it "
                        "from source, not from a certificate (repeatable); the closure's "
                        "books that include it follow")
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
    p.add_argument("--ld-local", dest="ld_local", action="store_true", default=True,
                   help="(the default) load each from-source dependency inside one "
                        "(encapsulate () ...), so its local lemmas stay local as a certified "
                        "include keeps them")
    p.add_argument("--ld-leak", dest="ld_local", action="store_false",
                   help="load from-source dependencies form by form instead: their LOCAL "
                        "lemmas become session rules, but a refusal names its event")
    add_remote_options(p, sync=True, lease=True)
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
    p.add_argument("--idle-seconds", type=float, default=None)
    p.add_argument("--ld", action="append", default=[])
    p.add_argument("--ld-local", action="store_true")
    p.add_argument("--load-limit", type=float, default=None)
    p.set_defaults(run=lambda a: serve(a.name, a.book, a.upto, a.through, a.limit,
                                       a.load_timeout, a.lock_fd, a.lane, a.idle_seconds,
                                       a.ld, a.ld_local, a.load_limit))
    p = sub.add_parser("send", help="forms (one or several); `-` reads them from stdin")
    p.add_argument("name")
    p.add_argument("form")
    p.add_argument("--limit", type=float, default=None)
    p.add_argument("--full", action="store_true", help="everything ACL2 printed")
    p.add_argument("--keep-going", action="store_true",
                   help="several forms: send the rest after a refusal")
    p.add_argument("--allow-undo", action="store_true",
                   help="send (u), (ubt ...), :ubt! ... and the like; refused without it")
    add_remote_options(p, sync=True)  # --no-sync accepted: send syncs nothing
    p.set_defaults(run=send)
    p = sub.add_parser("send-range", help="a book's forms from one event to another, "
                                          "with ACL2 time and prover steps per form")
    p.add_argument("name")
    p.add_argument("book", help="books/NAME (.lisp optional) or any file of forms")
    p.add_argument("--from", dest="start", default=None, metavar="EVENT",
                   help="first form: an event name or #N (default: the first)")
    p.add_argument("--until", default=None, metavar="EVENT",
                   help="EXCLUSIVE: stop BEFORE this event (or #N); it is NOT sent "
                        "(--through EVENT sends it)")
    p.add_argument("--through", default=None, metavar="EVENT",
                   help="INCLUSIVE: stop after this event (or #N); it is sent")
    p.add_argument("--limit", type=float, default=None)
    p.add_argument("--full", action="store_true", help="every form's whole output")
    p.add_argument("--keep-going", action="store_true",
                   help="report every refusal instead of stopping at the first")
    p.add_argument("--ld-local", action="store_true",
                   help="send the range inside one encapsulate (non-local include-book "
                        "and defpkg first), so its local events are dropped at the end, "
                        "as a certified include drops them")
    p.add_argument("--skip-includes", action="store_true",
                   help="skip every local include-book form (the session's own "
                        "from-source books are always skipped)")
    add_remote_options(p, sync=True)
    p.set_defaults(run=send_range)
    p = sub.add_parser("send-file", help="every form of a file (a tests/acl2 test file), "
                                         "in order, its include paths made the session's")
    p.add_argument("name")
    p.add_argument("file", help="the file of forms (tests/acl2/X-tests.lisp, .lisp optional)")
    p.add_argument("--limit", type=float, default=None)
    p.add_argument("--full", action="store_true", help="every form's whole output")
    p.add_argument("--keep-going", action="store_true",
                   help="report every refusal instead of stopping at the first")
    p.add_argument("--allow-undo", action="store_true",
                   help="send a form that takes events back out (`:u`, `:ubt`, ...)")
    add_remote_options(p, sync=True)
    p.set_defaults(run=send_file)
    p = sub.add_parser("resync", help="undo the session back to EVENT and resend the "
                                      "book from there (or from the first earlier event "
                                      "the world lacks)")
    p.add_argument("name")
    p.add_argument("book", help="books/NAME (.lisp optional) or any file of forms")
    p.add_argument("--from", dest="start", required=True, metavar="EVENT",
                   help="an event name or #N")
    p.add_argument("--until", default=None, metavar="EVENT",
                   help="EXCLUSIVE: stop before this one, which is NOT sent")
    p.add_argument("--through", default=None, metavar="EVENT",
                   help="INCLUSIVE: stop after this one, which is sent")
    p.add_argument("--limit", type=float, default=None)
    p.add_argument("--full", action="store_true", help="every form's whole output")
    p.add_argument("--keep-going", action="store_true",
                   help="do not stop at the first refused form")
    add_remote_options(p, sync=True)
    p.set_defaults(run=resync)

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
                   help="prove this form, or several (helper lemmas, then the target), "
                        "at the event's place instead; `-` reads them from stdin")
    p.add_argument("--ld", action="append", default=[], metavar="DEPENDENCY",
                   help="also load this dependency (a book the session's book includes) "
                        "from source")
    p.add_argument("--limit", type=float, default=None)
    p.add_argument("--load-timeout", type=float, default=600.0)
    p.add_argument("--idle-timeout", type=float, default=None, metavar="MIN",
                   help="the probe session stops itself after MIN minutes idle "
                        f"(default $FN_REPL_IDLE_MIN, else {DEFAULT_IDLE_MINUTES:g}; 0: never)")
    p.add_argument("--idle-seconds", type=float, default=None, help=argparse.SUPPRESS)
    p.add_argument("--full", action="store_true")
    p.add_argument("--stop", action="store_true", help="stop the probe session afterwards")
    p.add_argument("--with-sent", action="store_true",
                   help="first send the events `send` added to session NAME by hand (the "
                        "probe loads the book file, so it does not have them otherwise)")
    add_remote_options(p, sync=True)
    p.set_defaults(run=probe)
    p = sub.add_parser("status")
    p.add_argument("name")
    add_remote_options(p)
    p.set_defaults(run=status)
    p = sub.add_parser("checkpoints", help="the last refused form's key checkpoints "
                                           "from the session log")
    p.add_argument("name")
    p.add_argument("--lines", type=int, default=16,
                   help="lines kept per checkpoint (default 16)")
    add_remote_options(p)
    p.set_defaults(run=checkpoints)
    p = sub.add_parser("stop")
    p.add_argument("name")
    add_remote_options(p)
    p.set_defaults(run=stop)
    p = sub.add_parser("list", help="each session's lane, age, idle time and deadline")
    p.add_argument("--root", action="append", default=None, metavar="TREE",
                   help="read TREE/build/proof-repl instead of this tree's (repeatable)")
    p.add_argument("--all", action="store_true",
                   help="every session tree on this machine (see the header)")
    add_remote_options(p, sync=True)
    p.set_defaults(run=list_sessions)
    p = sub.add_parser("reap", help="stop dead, overdue or a lane's sessions")
    p.add_argument("--lane", default=None, help="every session tagged with this lane")
    p.add_argument("--older-than", type=float, default=None, metavar="S",
                   help="live sessions idle at least S seconds")
    p.add_argument("--idle", type=float, default=None, metavar="MIN",
                   help="live sessions idle at least MIN minutes, in every session tree "
                        "on this machine (implies --all)")
    p.add_argument("--all", action="store_true",
                   help="every session tree on this machine, not only this tree's")
    p.add_argument("--dry-run", action="store_true", help="say what would be reaped")
    p.add_argument("--root", action="append", default=None, metavar="TREE",
                   help="reap in TREE/build/proof-repl instead of this tree's (repeatable)")
    add_remote_options(p, sync=True)
    p.set_defaults(run=reap)
    p = sub.add_parser("gc", help=f"stop every session idle at least {GC_IDLE_MINUTES:g} min "
                                  "on this machine (--each-box: on every farm box)")
    p.add_argument("--idle", type=float, default=GC_IDLE_MINUTES, metavar="MIN")
    p.add_argument("--each-box", action="store_true", help="run it on hbox and persvati in turn")
    p.add_argument("--dry-run", action="store_true", help="say what would be stopped")
    p.add_argument("--root", action="append", default=None, metavar="TREE", help=argparse.SUPPRESS)
    add_remote_options(p, sync=True)
    p.set_defaults(run=gc)
    p = sub.add_parser("diff", help="the session's events whose form differs from the book's "
                                    "(a lemma edited in the book but not re-sent, or vice versa)")
    p.add_argument("name")
    p.add_argument("book", help="books/NAME (.lisp optional) or any file of forms")
    p.add_argument("--all", action="store_true", help="also list absent, macro and unanswered events")
    p.add_argument("--limit", type=float, default=None)
    add_remote_options(p, sync=True)
    p.set_defaults(run=diff)
    argv = list(sys.argv[1:] if argv is None else argv)
    # The remote options belong to the subcommand, but closeout-common writes
    # `proof_repl.py --host auto start ...` (the farm's and remote_check's
    # order): options before the subcommand move after it (f1-bisect,
    # 2026-09-28: "invalid choice: 'auto'").
    lead = []
    while argv and (argv[0] in ("--host", "--remote-tree", "--acl2") and len(argv) > 1
                    or argv[0] == "--no-sync" or argv[0].startswith(
                        ("--host=", "--remote-tree=", "--acl2="))):
        width = 2 if argv[0] in ("--host", "--remote-tree", "--acl2") else 1
        lead += argv[:width]
        argv = argv[width:]
    if lead and argv:
        argv = argv[:1] + lead + argv[1:]
    elif lead:
        argv = lead
    args = parser.parse_args(argv)
    if args.command in ("start", "probe") and getattr(args, "book", None) \
            and args.book.endswith(".lisp"):
        # `start NAME books/X.lisp` reached the box as books/X.lisp.lisp
        # (small-rows, 2026-09-29): the name is the book without its suffix.
        suffixed = args.book
        args.book = suffixed[:-len(".lisp")]
        argv = [args.book if word == suffixed else word for word in argv]
    if (getattr(args, "host", None) is None and args.command in SESSION_COMMANDS
            and recorded_host(args.name)):
        # The session's machine is recorded here (remember_host): no --host again.
        args.host = recorded_host(args.name)
        print(f"proof-repl: session {args.name!r} is on {args.host} (its record); "
              "--host laptop runs here", file=sys.stderr, flush=True)
        argv = argv + ["--host", args.host]
    if getattr(args, "host", None) == "auto":
        args.host = resolve_auto_host(args)
        argv = [args.host if word == "auto" else word for word in argv]
    if getattr(args, "host", None) == LOCAL_HOST:
        if socket.gethostname().split(".")[0] in REMOTE_TREES:
            raise SystemExit("proof-repl: --host laptop: this is a farm box")
        args.host = None
    if args.command == "start" and not getattr(args, "host", None):
        remember_host(args.name, None)
    if getattr(args, "host", None):
        return run_remote(args, argv)
    if getattr(args, "acl2", None):
        os.environ["FN_ACL2"] = args.acl2
    if apply_box_defaults() is None:
        apply_local_defaults()
    return args.run(args)


if __name__ == "__main__":
    raise SystemExit(main())

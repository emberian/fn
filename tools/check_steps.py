#!/usr/bin/env python3
"""Run every step of `make check`, in parallel, skip what cannot have changed, then say which failed.

`make` stops a recipe at its first failing line, so one sibling's red step
(a stale harness arity, a generated file behind) hid every check after it:
flip-bridge, flip-tests-green and readme each lost a round to that on
2026-09-27.  So every step runs, and the last line prints the table and
exits 1 when any step failed.  And `make check` ran its ~60 steps one after
another, 35-45 minutes of every landing cycle (batch BB, 2026-09-28), while
most of them read disjoint parts of the tree; so the recipe now only PLANS
its steps and this driver runs them:

    python3 tools/check_steps.py begin build/check-steps
    python3 tools/check_steps.py add build/check-steps -- python3 tools/x.py --strict
    ...
    python3 tools/check_steps.py execute build/check-steps [--jobs N] [--no-cache]

`execute`:

- PARALLEL.  The steps fan out over N workers (default: half the cores,
  CHECK_JOBS), longest first by the last recorded time.  A step that writes a
  file another step reads or writes (WRITERS below, plus any writer a traced
  run discovered, kept in the cache directory) runs first, alone, in plan
  order.  Each step's output is printed whole when it finishes (the log
  never interleaves) and kept in DIRECTORY/logs/.
- WARM-UPS.  A step planned with `add --warm` (tools/ledger.py --load-tree)
  fills a content-addressed cache under build/cache/ that several steps
  read; it starts first and is never cached itself, the steps whose last
  traced run read build/cache/ (and any never traced) start after it, and
  every other step runs meanwhile.  Seven checkers used to analyse the same
  tree at once, four minutes each on persvati.
- INPUT-HASHED.  Every step runs under tools/check_trace/sitecustomize.py,
  which records what it actually read: the files it opened (imports
  included), the directories it listed, the paths it stat'ed and the git
  commands it ran.  After a VERDICT (exit 0, a pass; exit 1, a finding),
  the driver keys those inputs (content digests, listings, git outputs, the
  command, the FN_* environment, the Python interpreter and version, and the
  ACL2 and SBCL launchers the environment names) under CACHE.  A step whose
  recorded inputs are all unchanged is not run: its row says "cached (inputs
  unchanged since <sha>)" and its stored output is replayed; a RED is
  replayed red, with the same exit and finding, and its header names the
  run that produced it (sha, box, when, log), so the reader opens the real
  failure.  Paths inside the tree are keyed relative to its root, so one
  store serves every worktree of the same bytes on a box: CACHE is
  build/check-cache (never committed) unless FN_VERDICT_STORE or --cache
  names a shared one.  A step that starts a process the trace cannot see
  into (ACL2, a shell, a Python child without the tracer) or runs a git
  command with side effects or stdin is never cached, and neither is a
  NON-VERDICT: exit 2 (NOT RUN), a signal, 127.  `--no-cache` (`make check
  FORCE=1`) runs every step; the batch runner's one full pass at a pushed
  head uses it, and a cached verdict never satisfies a READY or a batch
  gate (a lane's READY is a live run of the steps its change reaches).

- SCOPED.  `execute --changed-since REV` (make check-lane CHECK_CHANGED_SINCE=REV)
  runs only the steps the diff from REV (committed, uncommitted and untracked
  files) can reach: the steps whose last traced run (build/check-cache/scope/,
  kept for passes AND failures: a NOT RUN or red step has inputs too) read,
  stat'ed or listed a changed path, ran a git command the change can move, or
  cannot be traced at all.  The rest print "skipped".  A docs-only diff runs
  the docs checks, not host_check or reach_check.  A step never traced here
  (a new tree, a new command) runs: scoping is only as good as the last
  full run in this cache.
- BASELINE.  `--write-baseline FILE` keeps the step table (the format of
  build/coordinator/check-baseline-<sha>.txt); `--baseline FILE` reads one, and
  the run prints "NEW reds vs baseline: ..." and exits nonzero only for a red
  step the baseline did not have red.

The summary is today's table in plan order; the verdict is the exit status.
`run` and `summary` remain for a single step outside `execute`.  An
interrupt (Ctrl-C) stops the whole check.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

RESULTS = "results.jsonl"
PLAN = "plan.jsonl"
ROOT = Path(__file__).resolve().parents[1]
TRACER = ROOT / "tools" / "check_trace"
DEFAULT_CACHE = ROOT / "build" / "check-cache"
# A line that names a finding, strongest first: a nonzero finding count, a
# named failure; then anything that reads like trouble.
STRONG = re.compile(r"\b[1-9]\d* (?:findings?|failures?|errors?)\b|\bUNDEFINED\b|\bNEW\b|"
                    r"(?i:\bfail(?:ed|ure|s)?\b|\berror\b|traceback|refused|mismatch|"
                    r"called with)")
FINDING = re.compile(r"(?i)\b(fail\w*|error|refus\w*|stale|missing|mismatch|violat\w*|"
                     r"traceback|not (?:found|generated|current|green))\b")

# Steps (by step_name) that write a file some other step reads or writes: they
# run first, one at a time, in plan order.  A traced run adds any writer it
# finds to CACHE/writers.json (and says so); name it here as well.
WRITERS: frozenset[str] = frozenset()
# Read-only git subcommands a cached step may have run: replayed to key it.
GIT_READS = frozenset({"rev-parse", "ls-files", "log", "show", "status", "diff", "ls-tree",
                       "merge-base", "rev-list", "describe", "cat-file", "check-ignore",
                       "for-each-ref", "grep", "hash-object", "config", "symbolic-ref",
                       "blame", "var"})
GIT_REPLAY_LIMIT = 200
# Content-addressed caches several steps share: an entry's name is the digest
# of the bytes it was computed from, which the step reads (and the trace
# records) to name it, and it is written by an atomic rename.  Neither an
# input nor a hazard (tools/ledger.py's ledger-tree, tools/callgraph.py's).
SHARED_CACHES = (str(ROOT / "build" / "cache") + os.sep,)
# Environment that does not change what a step decides.
ENV_IGNORED = frozenset({"FN_LANE_CHECK_DIR", "FN_CHECK_TRACE"})
# Exit codes that are a verdict on the inputs, and so are cached: a pass and a
# finding.  Exit 2 is NOT RUN (the tree's convention: no ACL2, no certificate),
# 127 is a missing program, a negative code a signal: none judged the inputs.
VERDICT_EXITS = (0, 1)


def step_name(command: list[str]) -> str:
    """`tools/cite_check.py --summary` -> `cite_check`; `-m unittest -q X` -> `X`."""
    words = [word for word in command[1:] if not word.startswith("-")] or command
    if "-m" in command:
        after = command[command.index("-m") + 1:]
        names = [word for word in after if not word.startswith("-")]
        return names[-1] if names else "python -m"
    first = Path(words[0]).name
    return first[:-3] if first.endswith(".py") else first


# A step that exits 2 and says NOT RUN lacks a capability this tree has not
# built (no certified world, no ACL2 launcher): a capability skip that says
# why, never a red (coordinator ruling 2026-10-10, MAKE-CHECK-CERT-WORLD-NOT-RUN).
# The train's box step has the world and runs those steps on every train.
NOT_RUN = re.compile(r"\bNOT RUN\b")


def capability_skip(row: dict) -> bool:
    return row.get("exit") == 2 and bool(NOT_RUN.search(row.get("finding") or ""))


def red(row: dict) -> bool:
    return row["exit"] != 0 and not capability_skip(row)


def first_finding(lines: list[str]) -> str:
    """The NOT RUN line of a capability skip, else the first line that reads
    like a finding, else the last line printed."""
    printed = [line.strip() for line in lines if line.strip()]
    for line in printed:
        if NOT_RUN.search(line):
            return line[:160]
    for pattern in (STRONG, FINDING):
        for line in printed:
            if pattern.search(line):
                return line[:160]
    return printed[-1][:160] if printed else ""


def begin(directory: Path) -> int:
    shutil.rmtree(directory, ignore_errors=True)
    directory.mkdir(parents=True, exist_ok=True)
    return 0


def add(directory: Path, command: list[str], warm: bool = False) -> int:
    directory.mkdir(parents=True, exist_ok=True)
    with open(directory / PLAN, "a", encoding="utf-8") as plan:
        plan.write(json.dumps({"command": command, **({"warm": True} if warm else {})}) + "\n")
    return 0


def run(directory: Path, command: list[str]) -> int:
    """One step, now, its output passing straight through (no trace, no cache)."""
    directory.mkdir(parents=True, exist_ok=True)
    name = step_name(command)
    print(f"== {name}: {shlex.join(command)}", flush=True)
    started = time.monotonic()
    captured: list[str] = []
    try:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, bufsize=1, errors="replace")
    except OSError as error:
        code, captured = 127, [f"cannot run: {error}"]
        print(captured[0])
    else:
        assert process.stdout is not None
        try:
            for line in process.stdout:
                sys.stdout.write(line)
                sys.stdout.flush()
                captured.append(line)
            process.stdout.close()
            code = process.wait()
        except KeyboardInterrupt:
            process.kill()
            process.wait()
            raise
    record = {"step": name, "command": shlex.join(command), "exit": code,
              "seconds": round(time.monotonic() - started, 1),
              "finding": first_finding(captured) if code else ""}
    with open(directory / RESULTS, "a", encoding="utf-8") as results:
        results.write(json.dumps(record) + "\n")
    if code < 0 and -code == 2:  # the step itself was interrupted
        raise KeyboardInterrupt
    return 0


def read_results(directory: Path) -> list[dict]:
    try:
        text = (directory / RESULTS).read_text(encoding="utf-8")
    except OSError:
        return []
    rows = [json.loads(line) for line in text.splitlines() if line.strip()]
    return sorted(rows, key=lambda row: row.get("index", 0))


def table_lines(rows: list[dict], footer: str = "") -> list[str]:
    width = max(len(row["step"]) for row in rows)
    failed = [row for row in rows if red(row)]
    skipped = sum(1 for row in rows if capability_skip(row))
    lines = [f"== check: {len(rows)} steps, {len(failed)} failed"
             f"{f', {skipped} not run (capability)' if skipped else ''}{footer}"]
    for row in rows:
        verdict = ("ok" if row["exit"] == 0 else "not run" if capability_skip(row)
                   else f"exit {row['exit']}")
        line = f"  {row['step']:{width}}  {verdict:8} {row['seconds']:7.1f} s"
        if row["exit"] != 0 and row["finding"]:
            line += f"  {row['finding']}"
        elif row.get("cached") or row.get("skipped"):
            line += f"  {row.get('cached') or row['skipped']}"
        lines.append(line)
    return lines


def summary(directory: Path, footer: str = "", baseline: Path | None = None,
            write_baseline: Path | None = None) -> int:
    rows = read_results(directory)
    if not rows:
        print(f"check: no step recorded under {directory}")
        return 1
    lines = table_lines(rows, footer)
    print("\n" + "\n".join(lines))
    if write_baseline is not None:
        write_baseline.parent.mkdir(parents=True, exist_ok=True)
        write_baseline.write_text("\n".join(lines) + "\n", encoding="utf-8")
        print(f"check: step table written to {write_baseline}")
    failed = [row for row in rows if red(row)]
    if baseline is None:
        return 1 if failed else 0
    return 1 if vs_baseline(rows, baseline) else 0


# ----------------------------------------------------------------- baseline

BASELINE_ROW = re.compile(r"^\s{2}(\S+)\s+(ok|not run|exit -?\d+)\s+\d+(?:\.\d+)? s(?:\s{2}(.*))?$")


def read_baseline(text: str) -> list[dict]:
    """The rows of the LAST step table in `text`: a check-baseline file, or a
    remote_check log that holds one (the runner's noise around it is skipped).
    Step name, whether it was red, and its finding."""
    rows: list[dict] = []
    for line in text.splitlines():
        if line.startswith("== check:"):
            rows = []
            continue
        found = BASELINE_ROW.match(line)
        if found and (rows or "== check:" in text):
            rows.append({"step": found[1], "red": found[2] not in ("ok", "not run"),
                         "finding": (found[3] or "").strip()})
    return rows


def finding_shape(finding: str) -> str:
    """A finding without its numbers: line numbers and counts drift, the step's
    complaint does not."""
    return re.sub(r"\d+", "#", finding)


def new_reds(current: list[dict], baseline: list[dict]) -> list[dict]:
    """The current red rows the baseline did not already have red.

    Per step name, the baseline's red rows are claimed first by an identical
    finding (digits aside), then, for a name that is one step in this run,
    by any leftover red row: a step that was red and is red again on another
    line is the same red.  A name planned several times (host_check) matches
    by finding only, so a different instance going red is new."""
    pool: dict[str, list[str]] = {}
    for row in baseline:
        if row["red"]:
            pool.setdefault(row["step"], []).append(finding_shape(row["finding"]))
    instances: dict[str, int] = {}
    for row in current:
        instances[row["step"]] = instances.get(row["step"], 0) + 1
    fresh = []
    leftovers = []
    for row in current:
        if not red(row):
            continue
        shapes = pool.get(row["step"], [])
        shape = finding_shape(row.get("finding", ""))
        if shape in shapes:
            shapes.remove(shape)
        else:
            leftovers.append(row)
    for row in leftovers:
        shapes = pool.get(row["step"], [])
        if shapes and instances[row["step"]] == 1:
            shapes.pop()
        else:
            fresh.append(row)
    return fresh


def vs_baseline(rows: list[dict], baseline: Path) -> bool:
    """Print the verdict against `baseline`; True when a red is new."""
    try:
        known = read_baseline(baseline.read_text(encoding="utf-8", errors="replace"))
    except OSError as error:
        print(f"check: cannot read the baseline {baseline}: {error}")
        return True
    if not known:
        print(f"check: no step table in the baseline {baseline}")
        return True
    ran = [row for row in rows if not row.get("skipped")]
    fresh = new_reds(ran, known)
    reds = [row for row in ran if red(row)]
    seen = {row["step"] for row in ran if not red(row)}
    fixed = sorted({row["step"] for row in known if row["red"]}
                   & seen - {row["step"] for row in reds})
    print(f"== baseline {baseline}: {sum(1 for r in known if r['red'])} red in it, "
          f"{len(reds)} red now, {len(reds) - len(fresh)} carried over, "
          f"{len(fixed)} fixed" + (f" ({', '.join(fixed)})" if fixed else ""))
    if fresh:
        print(f"NEW reds vs baseline: {', '.join(row['step'] for row in fresh)}")
        for row in fresh:
            print(f"  {row['step']}  exit {row['exit']}  {row.get('finding', '')}")
        return True
    print("no new reds vs baseline")
    return False


# ------------------------------------------------------------ scoped inputs

# Everything that decides what a trace records: a change here reaches every step.
GLOBAL_PATHS = ("tools/check_steps.py", "tools/check_trace/")
# What no untraceable child (ACL2, a shell, a Python child without the tracer)
# reads: prose.  A step whose trace is blind to its children is reached by any
# change but these; it is the one hand-kept list here, and it is short on
# purpose (a diff of only these never runs host_check --load's ACL2).
INERT_FOR_CHILDREN = ("docs/",)
INERT_SUFFIXES = (".md",)
# git reads whose output is a function of the tracked PATH SET only (a file
# added or removed moves it; an edit does not).
LS_FLAGS = frozenset({"-z", "--cached", "-c", "--exclude-standard", "--full-name",
                      "--error-unmatch", "--", "-o", "--others"})
# git reads whose output is none of the tree's business.
GIT_STATIC = frozenset({"config", "var", "check-ignore", "symbolic-ref", "init"})


def rel_path(path: str) -> str | None:
    """`path` relative to the repository root, None when outside it."""
    for form in (os.path.abspath(path), os.path.realpath(path)):
        for root in (str(ROOT), os.path.realpath(ROOT)):
            if form == root:
                return "."
            if form.startswith(root + os.sep):
                return form[len(root) + 1:]
    return None


def portable(path: str) -> str:
    """`path` as the store keys it: tree-relative (`./x`) inside the repository,
    absolute outside it (the interpreter, site-packages), so an entry written
    in one worktree is found from another worktree of the same bytes."""
    rel = rel_path(path)
    if rel is None:
        return path
    return "./" if rel == "." else "./" + rel


def located(key: str) -> str:
    """The path a stored key names in THIS tree."""
    if key == "./":
        return str(ROOT)
    return str(ROOT / key[2:]) if key.startswith("./") else key


def scope_record(command: list[str], trace: dict) -> dict:
    """What a diff must touch to reach this step: its repository inputs (never
    the ones it wrote, never outside the repository), and `x` when the trace is
    blind to something it ran."""
    written = trace["w"]

    def inside(paths) -> list[str]:
        found = {rel_path(p) for p in paths if p not in written}
        return sorted(p for p in found if p is not None)

    return {"command": command, "x": trace["x"][0] if trace["x"] else "",
            "r": inside(trace["r"] | trace["s"]), "l": inside(trace["l"]),
            "g": [[cwd, argv] for cwd, argv in trace["g"]]}


class Changes:
    """What differs from a base: `paths` maps a repository-relative path to A,
    D or M; `listed` is every directory whose listing that moves (the nearest
    directory that exists on both sides of an added or removed path)."""

    def __init__(self, paths: dict[str, str], old_dirs: set[str] | None = None):
        self.paths = dict(paths)
        self.listed: set[str] = set()
        for path, status in self.paths.items():
            if status not in ("A", "D"):
                continue
            where = os.path.dirname(path)
            while where:
                known = where in old_dirs if old_dirs is not None else os.path.isdir(ROOT / where)
                if known and (status == "A" or os.path.isdir(ROOT / where)):
                    break
                where = os.path.dirname(where)
            self.listed.add(where or ".")

    def __bool__(self) -> bool:
        return bool(self.paths)


PINNED = re.compile(r"[0-9a-f]{7,40}|(?:origin|upstream)/\S+|refs/(?:remotes|tags)/\S+")
REV_READS = frozenset({"show", "cat-file", "ls-tree", "rev-parse", "log", "diff", "rev-list",
                       "describe", "blame"})


def spec_match(path: str, specs: list[str]) -> bool:
    return any(path == spec or path.startswith(spec + "/") or fnmatch.fnmatch(path, spec)
               for spec in (s.rstrip("/") for s in specs))


def git_reached(argv: list[str], changed: Changes) -> str:
    """Why a change can move this git read's output, "" when it cannot.

    Static: config and friends; merge-base (a fork point moves with history,
    not with a file diff); anything about revisions that are all pinned (a
    sha, origin/..., a tag), whatever the diff.  By path: ls-files by an added
    or removed path; `REV:PATH`, and log, grep and blame with a pathspec, by a
    changed path under it.  Everything else (rev-parse HEAD, status, diff,
    log with no pathspec) by any change at all."""
    if not changed:
        return ""
    dash = argv.index("--") if "--" in argv else None
    specs = argv[dash + 1:] if dash is not None else []
    head = argv[:dash] if dash is not None else argv
    words = [w for w in head if not w.startswith("-")]
    sub, positional = (words[0], words[1:]) if words else ("", [])
    anything = f"git {' '.join(argv)[:50]}"
    if sub in GIT_STATIC or sub == "merge-base" or (sub == "rev-parse" and not positional):
        return ""
    if sub == "ls-files" and all(a in LS_FLAGS or not a.startswith("-") for a in argv):
        for path, status in changed.paths.items():
            if status in ("A", "D") and (spec_match(path, specs + positional)
                                         if specs or positional else True):
                return f"git ls-files: {path} {status}"
        return ""
    if sub in REV_READS and positional:
        for word in positional:
            rev, _, path = word.partition(":")
            if PINNED.fullmatch(re.split(r"[~^]", rev)[0]):
                continue
            hit = next((p for p in changed.paths if spec_match(p, [path])), "") if path else ""
            if hit or not path:
                return f"git {sub} {word[:40]}: {hit or 'any change'}"
        return ""
    if sub in ("log", "grep", "blame") and specs:
        hit = next((p for p in changed.paths if spec_match(p, specs)), "")
        return f"git {sub}: {hit} changed" if hit else ""
    return anything


def reached_by(record: dict | None, command: list[str], changed: Changes) -> str:
    """Why the change can affect the step, "" when it cannot."""
    if record is None or record.get("command") != command:
        return "never traced here"
    if record["x"]:
        for path in changed.paths:
            if not path.startswith(INERT_FOR_CHILDREN) and not path.endswith(INERT_SUFFIXES):
                return f"untraceable ({record['x'][:50]}) and {path} changed"
    for path in changed.paths:
        if path.startswith(GLOBAL_PATHS):
            return f"{path} changed"
    inputs = set(record["r"])
    for path in changed.paths:
        if path in inputs:
            return f"{path} changed"
    for where in sorted(set(record["l"]) & changed.listed):
        return f"{where}/ listing changed"
    for cwd, argv in record["g"]:
        if rel_path(cwd) is None:  # another repository: a fixture, a scratch clone
            continue
        why = git_reached(argv, changed)
        if why:
            return why
    return ""


def changed_paths(since: str) -> Changes:
    """What differs from `since` in the working tree (committed since,
    uncommitted, and untracked files), repository-relative."""
    def git(*argv: str) -> str:
        done = subprocess.run(["git", *argv], cwd=ROOT, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True)
        if done.returncode:
            raise SystemExit(f"check_steps: git {' '.join(argv)}: {done.stderr.strip()}")
        return done.stdout

    paths: dict[str, str] = {}
    parts = git("diff", "--name-status", "--no-renames", "-z", since).split("\0")
    for status, path in zip(parts[0::2], parts[1::2]):
        paths[path] = status[:1] if status[:1] in ("A", "D") else "M"
    for path in git("ls-files", "--others", "--exclude-standard", "-z").split("\0"):
        if path:
            paths[path] = "A"
    old_dirs = {d for d in git("ls-tree", "-d", "-r", "--name-only", since).splitlines()}
    return Changes(paths, old_dirs)


# ---------------------------------------------------------------- input keys

TEMP_ROOTS = tuple(sorted({os.path.realpath(p) + os.sep for p in
                           (tempfile.gettempdir(), "/tmp", "/var/tmp", "/private/tmp",
                            "/var/folders", "/private/var/folders",
                            os.environ.get("TMPDIR", "/tmp"))}))


def _is_temp(path: str) -> bool:
    return ((os.path.realpath(path) + os.sep).startswith(TEMP_ROOTS)
            or (path + os.sep).startswith(SHARED_CACHES))


def file_digest(path: str) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def path_state(path: str) -> str:
    """What a stat can tell a step: absent, a directory, or a file of a size."""
    try:
        st = os.stat(path)
    except OSError:
        return "absent"
    if os.path.isdir(path):
        return "dir"
    return f"file {st.st_size}"


def listing(path: str) -> str:
    try:
        names = sorted(os.listdir(path))
    except OSError:
        return "absent"
    return hashlib.sha256("\0".join(names).encode()).hexdigest()


GIT_FAILED = "error"


def git_output(cwd: str, argv: list[str]) -> str:
    try:
        done = subprocess.run(["git", *argv], cwd=cwd, stdin=subprocess.DEVNULL,
                              capture_output=True, timeout=120)
    except (OSError, subprocess.SubprocessError) as error:
        # Not an output: a git read that timed out or could not run keys
        # nothing (inputs_of refuses to cache on it, and inputs_unchanged
        # never matches it), so a timeout is never replayed as a PASS.
        return f"{GIT_FAILED} {error}"
    return hashlib.sha256(bytes([done.returncode & 0xFF]) + done.stdout).hexdigest()


def git_command(cwd: str, argv: list[str]) -> list:
    """[cwd, argv] with leading `-C DIR` options folded into cwd."""
    argv = list(argv)
    while len(argv) >= 2 and argv[0] == "-C":
        cwd = os.path.normpath(os.path.join(cwd, argv[1]))
        argv = argv[2:]
    return [cwd, argv]


def git_replayable(argv: list[str]) -> bool:
    if any(word in ("-C", "-c") for word in argv):
        return False
    words = [word for word in argv if not word.startswith("-")]
    sub = words[0] if words else ""
    if any(a.startswith(("--stdin", "--batch")) or a == "-w" for a in argv):
        return False
    if sub == "config" and not any(a.startswith("--get") for a in argv):
        return False
    return sub in GIT_READS


class FileMemo:
    """Content digests, reusing a stored one while size and mtime agree."""

    def __init__(self, known: dict):
        self.known = known
        self.lock = threading.Lock()

    def digest(self, path: str) -> str:
        try:
            st = os.stat(path)
        except OSError:
            return "absent"
        if os.path.isdir(path):
            return "dir"
        stamp = [st.st_size, st.st_mtime_ns]
        with self.lock:
            entry = self.known.get(path)
        if entry and entry[:2] == stamp:
            return entry[2]
        try:
            value = file_digest(path)
        except OSError:
            return "unreadable"
        with self.lock:
            self.known[path] = [*stamp, value]
        return value


def read_trace(trace_dir: Path) -> dict:
    trace: dict = {"r": set(), "w": set(), "l": set(), "s": set(), "g": [], "x": []}
    for part in sorted(trace_dir.glob("*.jsonl")):
        for line in part.read_text(encoding="utf-8", errors="replace").splitlines():
            try:
                record = json.loads(line)
            except ValueError:
                trace["x"].append("unreadable trace line")
                continue
            kind = record[0]
            if kind in ("r", "w", "l", "s"):
                trace[kind].add(record[1])
            elif kind == "g":
                command = git_command(record[1], record[2])
                if command not in trace["g"]:
                    trace["g"].append(command)
            elif kind == "x":
                trace["x"].append(record[1])
    return trace


def inputs_of(trace: dict, memo: FileMemo) -> tuple[dict | None, str]:
    """The step's input key from its trace, or (None, why it is not cacheable)."""
    if trace["x"]:
        return None, trace["x"][0]
    if len(trace["g"]) > GIT_REPLAY_LIMIT:
        return None, f"{len(trace['g'])} git commands"
    for cwd, argv in trace["g"]:
        if not git_replayable(argv):
            return None, f"git {' '.join(argv)[:60]}"
    written = trace["w"]
    keep = lambda p: p not in written and not _is_temp(p)  # noqa: E731
    replayed = [[cwd, argv, git_output(cwd, argv)] for cwd, argv in trace["g"]]
    for cwd, argv, value in replayed:
        if value.startswith(GIT_FAILED):
            return None, f"git {' '.join(argv)[:60]} did not answer ({value[:60]})"
    reads = sorted(p for p in trace["r"] if keep(p))
    return {
        "r": {portable(p): memo.digest(p) for p in reads},
        "l": {portable(p): listing(p) for p in sorted(trace["l"]) if keep(p)},
        "s": {portable(p): path_state(p) for p in sorted(trace["s"] - trace["r"]) if keep(p)},
        "g": [[portable(cwd), argv, value] for cwd, argv, value in replayed],
    }, ""


def moved_during(inputs: dict, since_ns: int) -> str:
    """The first input whose file or directory changed at or after `since_ns`,
    a timestamp read from the filesystem's own clock when the step started.

    The key is taken after the step exits, so a digest records the bytes
    there THEN, not the bytes the step read: a parallel writer or an outside
    edit during the run would key a PASS to content the step never judged
    (S055, sweep 2026-10-03).  Any input touched since the step started makes
    the run uncacheable; the comparison is `>=`, so a write in the same clock
    tick as the start counts as during."""
    # A stat'ed or opened DIRECTORY is keyed as "dir" (path_state, FileMemo):
    # its mtime moves whenever an entry is added beside it, which says
    # nothing the key records.  pathlib's resolve() stats every ancestor of a
    # tree path, so /Users/ember is in every step's `s`, and a sibling
    # session's write there refused to cache host_check, ledger, reach_check
    # and spec_cite_check on every laptop run (lane iter-arch, 2026-10-04).
    # A listed directory is different: its listing IS the key.
    for kind in ("r", "l", "s"):
        for path in inputs[kind]:
            where = located(path)
            try:
                if kind != "l" and os.path.isdir(where):
                    continue
                if os.stat(where).st_mtime_ns >= since_ns:
                    return where
            except OSError:
                continue
    return ""


def fs_now(directory: Path) -> int:
    """The filesystem clock now: the mtime of a file created in `directory`.
    A file's mtime comes from the kernel's coarse clock, which can lag
    `time.time_ns()`; comparing like with like is what makes `>=` sound."""
    marker = directory / "started"
    marker.write_bytes(b"")
    return marker.stat().st_mtime_ns


def inputs_unchanged(inputs: dict, memo: FileMemo) -> bool:
    for path, value in inputs["r"].items():
        if memo.digest(located(path)) != value:
            return False
    for path, value in inputs["l"].items():
        if listing(located(path)) != value:
            return False
    for path, value in inputs["s"].items():
        if path_state(located(path)) != value:
            return False
    for cwd, argv, value in inputs["g"]:
        if value.startswith(GIT_FAILED) or git_output(located(cwd), argv) != value:
            return False
    return True


def toolchain_identity() -> list:
    """The launchers a step may run that the trace cannot see into, by path
    and content: FN_ACL2 and FN_SBCL when set, else `acl2` and `sbcl` on PATH.
    An environment red (a box whose launcher is broken or absent) is keyed
    to that launcher, so fixing the box changes the key and the red re-runs."""
    found = []
    for variable, name in (("FN_ACL2", "acl2"), ("FN_SBCL", "sbcl")):
        path = os.environ.get(variable) or shutil.which(name) or ""
        if not path:
            found.append([name, "absent", ""])
            continue
        try:
            value = file_digest(path) if os.path.isfile(path) else "dir"
        except OSError:
            value = "unreadable"
        found.append([name, path, value])
    return found


def step_key(command: list[str]) -> str:
    """One key per (command, environment, interpreter, toolchain): the tree's
    bytes are the entry's inputs, never part of the key, so every worktree of
    the same bytes asks the store for the same entry."""
    env = {k: v for k, v in os.environ.items() if k.startswith("FN_") and k not in ENV_IGNORED}
    material = json.dumps([command, sorted(env.items()), sys.version, sys.executable,
                           toolchain_identity()])
    return hashlib.sha256(material.encode()).hexdigest()[:24]


def box_name() -> str:
    try:
        return os.uname().nodename.split(".")[0]
    except (OSError, AttributeError):
        return "unknown"


def head_sha() -> str:
    try:
        done = subprocess.run(["git", "rev-parse", "--short=9", "HEAD"], capture_output=True,
                              text=True, timeout=30)
    except (OSError, subprocess.SubprocessError):
        return "unknown"
    return done.stdout.strip() or "unknown"


def load_json(path: Path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return default


def save_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value), encoding="utf-8")
    os.replace(temporary, path)


# ------------------------------------------------------------------ execute

class Executor:
    def __init__(self, directory: Path, cache: Path, jobs: int, use_cache: bool,
                 since: str = "", baseline: Path | None = None,
                 write_baseline: Path | None = None, changed: Changes | None = None):
        self.since = since
        self.changed = changed if changed is not None else (changed_paths(since) if since else None)
        self.baseline = baseline
        self.write_baseline = write_baseline
        self.directory = directory
        self.cache = cache
        self.jobs = max(1, jobs)
        self.use_cache = use_cache
        self.lock = threading.Lock()
        self.memo = FileMemo(load_json(cache / "digests.json", {}))
        self.durations = load_json(cache / "durations.json", {})
        self.learned = set(load_json(cache / "writers.json", []))
        # Per step key: whether its last traced run read a shared cache.
        self.worlds = load_json(cache / "worlds.json", {})
        self.head = head_sha()
        self.processes: dict[int, subprocess.Popen] = {}
        self.traces: dict[int, dict] = {}
        (directory / "logs").mkdir(parents=True, exist_ok=True)

    def entry_path(self, key: str) -> Path:
        return self.cache / "steps" / f"{key}.json"

    def cached(self, step: dict) -> dict | None:
        if not self.use_cache or step["warm"]:
            return None
        entry = load_json(self.entry_path(step["key"]), None)
        if not entry or entry.get("command") != step["command"]:
            return None
        return entry if inputs_unchanged(entry["inputs"], self.memo) else None

    def scope_path(self, key: str) -> Path:
        return self.cache / "scope" / f"{key}.json"

    def scope_of(self, step: dict) -> dict | None:
        """The step's last traced inputs: its scope record, else (a cache that
        predates them) its last pass's cache entry."""
        record = load_json(self.scope_path(step["key"]), None)
        if record:
            return record
        entry = load_json(self.entry_path(step["key"]), None)
        if not entry:
            return None
        inputs = entry["inputs"]
        return {"command": entry["command"], "x": "", "r": sorted(
            {rel_path(located(p)) for p in [*inputs["r"], *inputs["s"]]} - {None}),
            "l": sorted({rel_path(located(p)) for p in inputs["l"]} - {None}),
            "g": [[located(cwd), argv] for cwd, argv, _ in inputs["g"]]}

    def scope(self, steps: list[dict]) -> list[dict]:
        """The steps the change can reach; the others get a "skipped" row."""
        assert self.changed is not None
        kept = []
        for step in steps:
            why = reached_by(self.scope_of(step), step["command"], self.changed)
            if why:
                kept.append(step)
                print(f"check_steps: {step['name']}: {why}", flush=True)
                continue
            note = (f"skipped (unaffected by the {len(self.changed.paths)} path(s) "
                    f"changed since {self.since})")
            row = {"index": step["index"], "step": step["name"],
                   "command": shlex.join(step["command"]), "exit": 0, "seconds": 0.0,
                   "finding": "", "skipped": note}
            # The store's verdict for the untouched step, carried beside the
            # row so a scoped table still shows a known red (tools/reds.py
            # reads it); the row's own exit stays 0: a scoped run judges the
            # change, and its gate is `--baseline`.
            entry = self.cached(step)
            if entry is not None and entry.get("exit", 0):
                row["last"] = {"exit": entry["exit"], "head": entry["head"],
                               "finding": first_finding(entry["output"].splitlines()),
                               "box": entry.get("box", ""), "when": entry.get("when", ""),
                               "log": entry.get("log", "")}
                row["skipped"] += f"; last verdict exit {entry['exit']}: {row['last']['finding']}"
            self.record(row)
        return kept

    def emit(self, text: str) -> None:
        with self.lock:
            sys.stdout.write(text)
            sys.stdout.flush()

    def record(self, row: dict) -> None:
        with self.lock:
            with open(self.directory / RESULTS, "a", encoding="utf-8") as results:
                results.write(json.dumps(row) + "\n")

    def perform(self, step: dict, alone: bool = False) -> None:
        index, name, command = step["index"], step["name"], step["command"]
        header = f"== {name}: {shlex.join(command)}\n"
        slug = re.sub(r"[^\w.-]", "_", name)[:60]
        log = self.directory / "logs" / f"{index:02d}-{slug}.log"
        entry = self.cached(step)
        if entry is not None:
            code = entry.get("exit", 0)
            note = f"cached (inputs unchanged since {entry['head']})"
            if code:
                note = (f"red, {note}; run on {entry.get('box', '?')} {entry.get('when', '?')}, "
                        f"log {entry.get('log', '?')}")
            log.write_text(entry["output"], encoding="utf-8")
            self.emit(header + f"-- {note}; its output then:\n" + entry["output"])
            self.record({"index": index, "step": name, "command": shlex.join(command),
                         "exit": code, "seconds": 0.0, "cached": note,
                         "finding": first_finding(entry["output"].splitlines()) if code else ""})
            return
        serial_stream = alone or self.jobs == 1
        if not serial_stream:
            self.emit(f"-- started {name}\n")
        trace_dir = Path(tempfile.mkdtemp(prefix=f"check-trace-{index:02d}-"))
        began = fs_now(trace_dir)
        env = dict(os.environ)
        env["FN_CHECK_TRACE"] = str(trace_dir)
        env["PYTHONPATH"] = os.pathsep.join(
            [str(TRACER)] + ([env["PYTHONPATH"]] if env.get("PYTHONPATH") else []))
        env.setdefault("PYTHONUNBUFFERED", "1")
        started = time.monotonic()
        if serial_stream:
            self.emit(header)
        try:
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                       text=True, bufsize=1, errors="replace", env=env,
                                       start_new_session=True)
        except OSError as error:
            code, output = 127, f"cannot run: {error}\n"
        else:
            with self.lock:
                self.processes[index] = process
            assert process.stdout is not None
            parts = []
            for line in process.stdout:
                parts.append(line)
                if serial_stream:
                    self.emit(line)
            process.stdout.close()
            code = process.wait()
            output = "".join(parts)
            with self.lock:
                self.processes.pop(index, None)
        seconds = round(time.monotonic() - started, 1)
        log.write_text(output, encoding="utf-8")
        if not serial_stream:
            self.emit(header + output)
        trace = read_trace(trace_dir)
        shutil.rmtree(trace_dir, ignore_errors=True)
        save_json(self.scope_path(step["key"]), scope_record(command, trace))
        with self.lock:
            self.traces[index] = trace
            self.durations[step["key"]] = seconds
            self.worlds[step["key"]] = any(
                (p + os.sep).startswith(SHARED_CACHES)
                for p in trace["r"] | trace["l"] | trace["w"] | trace["s"])
        if code in VERDICT_EXITS:  # a forced run refreshes the cache too
            inputs, why = inputs_of(trace, self.memo)
            if inputs is not None:
                moved = moved_during(inputs, began)
                if moved:
                    inputs, why = None, f"{moved} changed while it ran"
            if inputs is None:
                self.emit(f"-- {name}: not cacheable ({why})\n")
                try:
                    self.entry_path(step["key"]).unlink()
                except OSError:
                    pass
            else:
                save_json(self.entry_path(step["key"]),
                          {"command": command, "head": self.head, "inputs": inputs,
                           "output": output, "seconds": seconds, "exit": code,
                           "box": box_name(), "log": str(log.resolve()),
                           "when": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())})
        else:  # a non-verdict (NOT RUN, a signal, 127) replaces nothing and is kept by nobody
            try:
                self.entry_path(step["key"]).unlink()
            except OSError:
                pass
        self.record({"index": index, "step": name, "command": shlex.join(command), "exit": code,
                     "seconds": seconds,
                     "finding": first_finding(output.splitlines()) if code else ""})

    def hazards(self, steps: list[dict], alone: list[dict]) -> list[str]:
        """Steps that wrote a repository file another step touched.

        A parallel one is learned as a writer (it runs first and alone from
        the next run); a learned writer whose traced run conflicts with
        nothing any more is forgotten.  Only steps that ran (not cached)
        have a trace; a learned writer that was cached stays learned."""
        found = []
        root = str(ROOT) + os.sep
        mine = str(self.directory.resolve()) + os.sep
        ours = str(self.cache.resolve()) + os.sep
        for step in steps:
            trace = self.traces.get(step["index"])
            if trace is None:
                continue
            command = shlex.join(step["command"])
            writes = {p for p in trace["w"] if p.startswith(root)
                      and not p.startswith((mine, ours)) and not _is_temp(p)}
            conflict = ""
            for other in steps:
                o = self.traces.get(other["index"])
                if other is step or o is None or not writes:
                    continue
                touched = (writes & (o["r"] | o["w"] | o["s"])) | \
                    {p for p in writes if os.path.dirname(p) in o["l"]}
                if touched:
                    conflict = f"{step['name']} wrote {sorted(touched)[0]} which {other['name']} touched"
                    break
            if conflict and step not in alone:
                found.append(conflict)
                self.learned.add(command)
                # Neither verdict judged a settled tree: the reader may have
                # read mid-write, and the writer's own key is no better.
                # Drop both cache entries, so the next run runs both (S055).
                for named in (step, other):
                    try:
                        self.entry_path(named["key"]).unlink()
                    except OSError:
                        pass
            elif not conflict and command in self.learned:
                self.learned.discard(command)
                print(f"check_steps: {step['name']} no longer writes what another step reads; "
                      f"it fans out again")
        return found

    def execute(self, steps: list[dict]) -> int:
        started = time.monotonic()
        total = len(steps)
        if self.changed is not None:
            steps = self.scope(steps)
            print(f"check_steps: {len(self.changed.paths)} path(s) changed since {self.since}; "
                  f"{len(steps)} of {total} steps can be affected", flush=True)
        writers = WRITERS | self.learned
        warm = [s for s in steps if s["warm"]]
        first = [s for s in steps if not s["warm"]
                 and (s["name"] in writers or shlex.join(s["command"]) in writers)]
        rest = [s for s in steps if s not in first and s not in warm]
        rest.sort(key=lambda s: -self.durations.get(s["key"], 60.0))
        try:
            if self.jobs == 1:
                for step in warm + first + sorted(rest, key=lambda s: s["index"]):
                    self.perform(step, alone=True)
            else:
                # Warm-ups start at once.  A writer runs alone (after the
                # warm-ups when it reads what they fill); then everything
                # else fans out, the steps that read what the warm-ups fill
                # (by their last traced run; a step never traced counts)
                # once they have.
                reads_world = lambda s: bool(warm) and self.worlds.get(s["key"], True)  # noqa: E731
                with concurrent.futures.ThreadPoolExecutor(self.jobs) as pool:
                    futures = [pool.submit(self.perform, s) for s in warm]

                    def warmed() -> None:
                        for future in futures[:len(warm)]:
                            future.result()

                    for step in first:
                        if reads_world(step):
                            warmed()
                        self.perform(step, alone=True)
                    late = [s for s in rest if reads_world(s)]
                    futures += [pool.submit(self.perform, s) for s in rest if s not in late]
                    warmed()
                    futures += [pool.submit(self.perform, s) for s in late]
                    for future in futures:
                        future.result()
        except KeyboardInterrupt:
            with self.lock:
                for process in self.processes.values():
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except OSError:
                        pass
            raise
        hazards = self.hazards(steps, first)
        save_json(self.cache / "digests.json", self.memo.known)
        save_json(self.cache / "durations.json", self.durations)
        save_json(self.cache / "writers.json", sorted(self.learned))
        save_json(self.cache / "worlds.json", self.worlds)
        for hazard in hazards:
            print(f"check_steps: WARNING {hazard}; it runs first and alone from now on "
                  f"({self.cache / 'writers.json'}); name it in WRITERS in tools/check_steps.py")
        cached = sum(1 for row in read_results(self.directory) if row.get("cached"))
        skipped = total - len(steps)
        footer = (f" (jobs {self.jobs}, wall {time.monotonic() - started:.1f} s, "
                  f"{cached} cached{f', {skipped} skipped' if skipped else ''}"
                  f"{'' if self.use_cache else ', cache off'})")
        return summary(self.directory, footer, self.baseline, self.write_baseline)


def plan_steps(directory: Path) -> list[dict]:
    try:
        lines = (directory / PLAN).read_text(encoding="utf-8").splitlines()
    except OSError:
        return []
    steps = []
    for index, line in enumerate(line for line in lines if line.strip()):
        planned = json.loads(line)
        command = planned["command"]
        steps.append({"index": index, "name": step_name(command), "command": command,
                      "key": step_key(command), "warm": bool(planned.get("warm"))})
    return steps


def default_jobs() -> int:
    configured = os.environ.get("CHECK_JOBS", "").strip()
    if configured.isdigit() and int(configured) > 0:
        return int(configured)
    return max(1, (os.cpu_count() or 2) // 2)


def execute(directory: Path, jobs: int, use_cache: bool, cache: Path, since: str = "",
            baseline: Path | None = None, write_baseline: Path | None = None,
            changed: Changes | None = None) -> int:
    steps = plan_steps(directory)
    if not steps:
        print(f"check: no step planned under {directory}")
        return 1
    (directory / RESULTS).unlink(missing_ok=True)
    return Executor(directory, cache, jobs, use_cache, since, baseline, write_baseline,
                    changed).execute(steps)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="action", required=True)
    for action in ("begin", "summary"):
        p = sub.add_parser(action)
        p.add_argument("directory")
    for action, text in (("run", "one step now: DIRECTORY -- COMMAND ..."),
                         ("add", "plan one step: DIRECTORY -- COMMAND ...")):
        p = sub.add_parser(action, help=text)
        if action == "add":
            p.add_argument("--warm", action="store_true",
                           help="a warm-up: it fills a shared cache (build/cache/) and is "
                                "never itself cached; the steps that read that cache wait "
                                "for it")
        p.add_argument("directory")
        p.add_argument("command", nargs=argparse.REMAINDER)
    p = sub.add_parser("execute", help="run the planned steps and print the table")
    p.add_argument("directory")
    p.add_argument("--jobs", type=int, default=0,
                   help="workers (default: CHECK_JOBS, else half the cores); 1 is serial")
    p.add_argument("--no-cache", action="store_true",
                   help="run every step, whatever its inputs (make check FORCE=1)")
    p.add_argument("--cache", default=os.environ.get("FN_VERDICT_STORE") or str(DEFAULT_CACHE),
                   help="the verdict store (default FN_VERDICT_STORE, else build/check-cache); "
                        "entries key tree files by relative path, so one store serves every "
                        "worktree on a box")
    p.add_argument("--changed-since", metavar="REV", default="",
                   help="run only the steps a diff from REV can reach (their last traced "
                        "inputs; a step never traced here runs)")
    p.add_argument("--baseline", metavar="FILE", default="",
                   help="a step table (check-baseline-<sha>.txt): print NEW reds vs it, "
                        "exit nonzero only for those")
    p.add_argument("--write-baseline", metavar="FILE", default="",
                   help="also write this run's step table to FILE")
    args = parser.parse_args(argv)
    directory = Path(args.directory)
    if args.action == "begin":
        return begin(directory)
    if args.action == "summary":
        return summary(directory)
    if args.action == "execute":
        try:
            return execute(directory, args.jobs or default_jobs(), not args.no_cache,
                           Path(args.cache), args.changed_since,
                           Path(args.baseline) if args.baseline else None,
                           Path(args.write_baseline) if args.write_baseline else None)
        except KeyboardInterrupt:
            return 130
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error(f"{args.action} needs a command after --")
    if args.action == "add":
        return add(directory, command, args.warm)
    try:
        return run(directory, command)
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    os.environ.setdefault("PYTHONUNBUFFERED", "1")
    raise SystemExit(main())

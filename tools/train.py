#!/usr/bin/env python3.12
"""Drive the integrator's merge train: merge, regen, gate, push.

Run from the batch tree (a git worktree on branch integrate/<name>).  The order
of regeneration is fixed and the push is conditional on gates that ran at the
exact HEAD being pushed, recorded in build/train/<branch>.json.

    train.py merge LANE@SHA [LANE@SHA ...]
    train.py regen [--label N]
    train.py certify BOX             # ONE farm run (install, certify), then emits
    train.py boxstep BOX             # tools-only trains / persvati fallback: the box step in a fresh tree
    train.py image [--label L]       # read HEAD's image run (tools/hbox_native.sh) for the image gate
    train.py gate
    train.py push
    train.py status

A books train runs `certify BOX`: one farm run of books/wire-export plus the
train's changed books and tests (one cache install, one certify), then the emit
and check half of BOX_CMD over ssh in that run's tree, under swarm-build and a
timeout.  It records the same box-step.json as `boxstep` plus the farm run, the
certify id and the install/certify/emit wall seconds (also in the train state,
shown by `status`).

`certify BOX` certifies the affected closure of the train: every Makefile
root transitively affected by a changed book, every root the train adds to
the Makefile's ACL2_BOOKS, plus the critical witness tests
of affected theorem books (COORDINATION section 5: the affected closure
certifies on the exact artifact before a push, regardless of tree size; the
lane selection, direct includers only, missed the far consumers of trains 49
and 58).

Known reds.  `planning/known-reds.json` is dev's recorded baseline of reds,
each row owned by an open repair item.  A train is *non-regressing* when every
red it meets is a row there; it is *green* only when the file has no rows, and
`push` and `status` say which.  A certify whose failed books are all `certify`
rows goes on to its emits and records them; any other failed or killed book
fails it.  The `baseline` gate refuses a row this train adds relative to
origin/dev (rows shrink only), a row whose item is missing or closed, and a
malformed file.  The one way in is an amendment record in
`planning/known-reds-amendments.json` (append-only; the row, the dev sha where
it was measured, the item, the owner, the coordinator ruling; ruled 2026-10-09
13:05): the gate accepts exactly the added rows an amendment names, refuses a
rewritten or dropped amendment record, and refuses an amendment that names no
present row (unless the row was retired and its item is closed), so amendments
cannot be stockpiled.  `push` and `status` print the amendment count beside
the row count.

The image gate.  A train whose diff touches the heap probe, a launcher or
host/native/ (IMAGE_RULES) must run the rule's native modules
(test_native_operator_verbs, heap_from_profile and the served natives) on
HEAD's image: `tools/hbox_native.sh HEAD MODULES`, then `train.py image`
reads each module's rc and case statuses from the box.  The obliged set may
span several runs at HEAD (heap_from_profile runs under `--mem 2G`): each
`train.py image --label L` adds its run's modules to HEAD's record, and a
module read from two runs is refused.  The gate passes when
every obliged module ran at HEAD and each red case is a `native` known red;
a module that has not run (an interrupted image gate) refuses the push.
Every command ends with one line `TRAIN-DONE CMD rc=N`.

The box step (`boxstep`) certifies wire-export incrementally on a build box,
regenerates planning/interfaces.json and specs/wire-grammar.json there, runs
the world, build-list and host checks, commits the fetched outputs and records
the resulting sha in build/train/box-step.json.  The `box_step` gate passes
when that sha is HEAD, or when it is an ancestor of HEAD, no file under
books/, specs/ or tests/acl2/ changed since it, and the local checks
(LOCAL_BOX_CHECKS) are all 0 at HEAD; the gate then records the sha it
inherits from (coordinator ruling, 2026-10-07, during the hbox outage).  Any
other case refuses: the train runs `boxstep` first.
"""
from __future__ import annotations

import argparse
import fnmatch
import json
import os
import shutil
import subprocess
import sys
import re
import shlex
import tempfile
import time
from pathlib import Path

PY = os.environ.get("TRAIN_PY", "python3.12")
PY3 = os.environ.get("TRAIN_PY3", "python3")

# Conflicted files that are regenerated anyway: the train side wins.
GENERATED = (
    "planning/interfaces.json",
    "specs/wire-grammar.json",
    # keystone_emit --write-manifest rewrites it from the tree at regen;
    # its owners say never hand-merge it (trains 41, 45, 46 conflicted on it)
    "planning/teeth-obligations.json",
    # tools/extract/world.py writes the image-world umbrellas, their -part-N
    # links and the extraction world files from the native build scripts
    # (deputy C, 2026-10-08: commit-held-host bounced on the six parts)
    "books/image-world*.lisp",
    "tools/extract/world*.lisp",
)


def _generated(path: str) -> bool:
    return any(fnmatch.fnmatchcase(path, g) for g in GENERATED)
# planning/proofs.json is NOT here: ledger.py --write regenerates only its
# event arrays, and lanes curate its rows (re-pointing a PRF row at a renamed
# keystone), so a conflict there goes back to the lane like source does.
# Tail-append files: keep both sides' lines.
UNION = ("planning/decisions.md",)

# Files the regen step is allowed to commit (only those that exist/changed).
REGEN_OUTPUTS = (
    "books/image-world*.lisp",
    "tools/extract/world*.lisp",
    "planning/proofs.json",
    "planning/teeth-obligations.json",
    # harness_check --write-stubs rewrites only the marked derived-stub
    # blocks; the tree is clean before regen, so only those changes match
    "tests/*.lisp",
)
HBOX_OUTPUTS = ("planning/interfaces.json", "specs/wire-grammar.json")

BOX_CMD = (
    "python3 tools/certify_books.py --incremental --jobs 6 --timeout-seconds 1800 books/wire-export && "
    "python3 tools/interface_emit.py --write && python3 tools/interface_emit.py --check && "
    "python3 tools/protocol_emit.py --wire --write && python3 tools/protocol_emit.py --wire --check && "
    "python3 tools/extract/world.py --check && python3 tools/host_check.py --build-lists && "
    "python3 tools/host_check.py --read && python3 tools/host_check.py --world"
)

# The half of BOX_CMD after the certify step; `certify` runs it in the farm tree.
# Timed one by one; interface_emit writes and checks in ONE invocation (it
# computes the declarations and the host reading once).
EMIT_STEPS = (
    ("interface_emit", "python3 tools/interface_emit.py --write --check"),
    ("protocol_emit", "python3 tools/protocol_emit.py --wire --write && python3 tools/protocol_emit.py --wire --check"),
    ("world", "python3 tools/extract/world.py --check"),
    ("build_lists", "python3 tools/host_check.py --build-lists"),
    ("host_read", "python3 tools/host_check.py --read"),
    ("host_world", "python3 tools/host_check.py --world"),
)
EMIT_CMD = " && ".join(
    f"{{ s=$(date +%s); {c}; r=$?; echo \"== step {n} $(( $(date +%s) - s ))\"; [ $r = 0 ]; }}"
    for n, c in EMIT_STEPS)
EMIT_TIMEOUT_SECONDS = 3600
FARM_TIMEOUT_SECONDS = 1800
SSH = os.environ.get("TRAIN_SSH", "ssh")
WRAPS = {"hbox": "swarm-build"}

# Paths whose change since the last box step makes a new box step necessary.
BOX_PATHS = ("books", "specs", "tests/acl2")
# What the gate runs locally when it inherits a box step instead.
LOCAL_BOX_CHECKS = (
    ("interface_emit", ["tools/interface_emit.py", "--check"]),
    ("world", ["tools/extract/world.py", "--check"]),
    ("build_lists", ["tools/host_check.py", "--build-lists"]),
    ("host_read", ["tools/host_check.py", "--read"]),
    ("host_world", ["tools/host_check.py", "--world"]),
)

# The Python suites the integrator ran by hand before a push, now gate
# conditions: the push refuses on them like the others (train 36 pushed two
# test_ledger reds through `gate; push` chained with `;`).  Always these; and
# the test file of every tools/<x>.py the train changes, and every changed
# tests/test_*.py except tests/test_native_* (they need a native image).  Each runs as `python -m unittest <file>` from the root
# (test_train imports `tools.train`, so not as a bare script).
UNIT_TESTS = ("tests/test_ledger.py", "tests/test_keystone_emit.py",
              "tests/test_keystone_critical.py",
              "tests/test_train.py", "tests/test_farm.py")

GATES = ("ancestor", "ledger", "current_view", "main_last", "keystone", "host_load", "ascii",
         "box_step", "lock_delta", "baseline", "secrets", "unit", "image")

# The image gate (coordinator 2026-10-09, after train 74).  A train whose diff
# against origin/dev touches a rule's paths runs the rule's native modules on
# the train's own image in the same train (COORDINATION section 5), picked
# from the diff rather than remembered: train 63 changed the launcher's heap
# decision and no train ran test_native_served_line_stack until train 73,
# which found it red.  A path ending in "/" is a directory prefix.
SERVED_NATIVES = ("tests.test_native_served_differential", "tests.test_native_owner",
                  "tests.test_native_article_slots", "tests.test_native_reader_index",
                  "tests.test_native_bounds_blob", "tests.test_native_served_cost",
                  "tests.test_native_served_line_stack", "tests.test_native_over_window")
IMAGE_RULES = (
    ("the heap probe, a launcher or host/native/",
     ("books/heap-figure.lisp", "packaging/fn", "packaging/launcher-decide.sh",
      "tools/build_native_host.sh", "tools/extract/core_launcher.py", "host/native/"),
     ("tests.test_native_operator_verbs", "tests.test_native_heap_from_profile") + SERVED_NATIVES),
)
# tools/hbox_native.sh's local record of a run (box=, dir=, source=), under
# the batch tree; LABEL is the first 12 hex digits of the run's commit.
IMAGE_RUN_RECORD = "build/hbox-native/{label}.run"
# a case status that is not a red (tools/test_budget.py's vocabulary)
IMAGE_CASE_PASS = ("ok", "skip")
# tools/hbox_native.sh's module status when it ran and every test skipped
# (a fixture or memory cap absent): it ran, it is not a red, and the gate
# prints it so the uncovered module is never silent
IMAGE_RC_ALL_SKIPPED = 4

# Dev's recorded reds with owners (COORDINATION section 5).  Each row is
# {"kind", "subject", "item", "owner", "evidence"}; (kind, subject) is unique.
KNOWN_REDS = "planning/known-reds.json"
KNOWN_RED_KINDS = ("certify", "native", "check", "extraction")
KNOWN_RED_FIELDS = ("kind", "subject", "item", "owner", "evidence")
# Amendments admit a row added after the baseline entered (COORDINATION section 5).
# Each record names its row by the same (kind, subject) key.
KNOWN_RED_AMENDMENTS = "planning/known-reds-amendments.json"
AMENDMENT_FIELDS = ("kind", "subject", "dev_sha", "item", "owner", "ruling")


class TrainError(Exception):
    pass


# --------------------------------------------------------------------------- plumbing

def say(msg: str) -> None:
    print(msg, flush=True)


def git(root: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    p = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True)
    if check and p.returncode != 0:
        raise TrainError(f"git {' '.join(args)} failed rc {p.returncode}: {p.stderr.strip()}")
    return p


def toplevel(start: Path) -> Path:
    p = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=start, capture_output=True, text=True)
    if p.returncode != 0:
        raise TrainError("not inside a git work tree")
    return Path(p.stdout.strip())


class Train:
    def __init__(self, root: Path):
        self.root = root
        self.branch = git(root, "rev-parse", "--abbrev-ref", "HEAD").stdout.strip()
        if self.branch == "HEAD":
            raise TrainError("detached HEAD: the batch tree must be on branch integrate/<name>")
        self.dir = root / "build" / "train"
        self.logs = self.dir / "logs"
        self.state_path = self.dir / (self.branch.replace("/", "__") + ".json")

    # ---- state
    def load(self) -> dict:
        if self.state_path.exists():
            return json.loads(self.state_path.read_text())
        return {"branch": self.branch, "lanes": [], "regen": [], "regen_commits": 0, "gates": {}}

    def save(self, st: dict) -> None:
        self.dir.mkdir(parents=True, exist_ok=True)
        tmp = self.state_path.with_suffix(".tmp")
        tmp.write_text(json.dumps(st, indent=2, sort_keys=True) + "\n")
        os.replace(tmp, self.state_path)

    def head(self) -> str:
        return git(self.root, "rev-parse", "HEAD").stdout.strip()

    def dirty(self) -> bool:
        return bool(git(self.root, "status", "--porcelain").stdout.strip())

    # ---- running commands
    def run(self, step: str, argv: list[str], cwd: Path | None = None) -> int:
        say("$ " + " ".join(argv))
        self.logs.mkdir(parents=True, exist_ok=True)
        log = self.logs / f"{step}.log"
        p = subprocess.run(argv, cwd=cwd or self.root, capture_output=True, text=True)
        out = p.stdout + p.stderr
        log.write_text(out)
        if p.returncode != 0:
            say(f"  step {step} FAILED rc {p.returncode} (log: {log})")
            for line in out.splitlines()[-30:]:
                say("  | " + line)
        else:
            say(f"  ok (log: {log})")
        return p.returncode

    def fetch(self) -> None:
        say("$ git fetch origin")
        git(self.root, "fetch", "--no-tags", "origin")


# --------------------------------------------------------------------------- known reds

def parse_known_reds(text: str) -> list[dict]:
    """The rows of a known-reds file; TrainError when it is malformed."""
    try:
        data = json.loads(text)
    except ValueError as error:
        raise TrainError(f"{KNOWN_REDS} is not JSON: {error}") from error
    rows = data.get("rows") if isinstance(data, dict) else None
    if not isinstance(rows, list):
        raise TrainError(f"{KNOWN_REDS} has no list 'rows'")
    seen = set()
    for row in rows:
        if not isinstance(row, dict) or any(not isinstance(row.get(f), str) or not row.get(f)
                                            for f in KNOWN_RED_FIELDS):
            raise TrainError(f"{KNOWN_REDS}: a row lacks one of {', '.join(KNOWN_RED_FIELDS)}: {str(row)[:120]}")
        if row["kind"] not in KNOWN_RED_KINDS:
            raise TrainError(f"{KNOWN_REDS}: kind {row['kind']!r} is not one of {', '.join(KNOWN_RED_KINDS)}")
        key = (row["kind"], row["subject"])
        if key in seen:
            raise TrainError(f"{KNOWN_REDS}: {key[0]} {key[1]} appears twice")
        seen.add(key)
    return rows


def known_reds_at(t: "Train", rev: str) -> list[dict] | None:
    """The rows at REV, or None when REV has no known-reds file."""
    p = git(t.root, "show", f"{rev}:{KNOWN_REDS}", check=False)
    return parse_known_reds(p.stdout) if p.returncode == 0 else None


def parse_amendments(text: str) -> list[dict]:
    """The records of an amendments file; TrainError when it is malformed."""
    try:
        data = json.loads(text)
    except ValueError as error:
        raise TrainError(f"{KNOWN_RED_AMENDMENTS} is not JSON: {error}") from error
    records = data.get("amendments") if isinstance(data, dict) else None
    if not isinstance(records, list):
        raise TrainError(f"{KNOWN_RED_AMENDMENTS} has no list 'amendments'")
    last: dict = {}
    for rec in records:
        if not isinstance(rec, dict) or any(not isinstance(rec.get(f), str) or not rec.get(f)
                                            for f in AMENDMENT_FIELDS):
            raise TrainError(f"{KNOWN_RED_AMENDMENTS}: a record lacks one of "
                             f"{', '.join(AMENDMENT_FIELDS)}: {str(rec)[:120]}")
        key = (rec["kind"], rec["subject"])
        prev = last.get(key)
        if prev is not None:
            # An owner transfer (coordinator 2026-10-09): a later record for
            # the same row names the owner it takes over from, with the first
            # record's item and dev sha.  The earlier records stay as written
            # (the measured owner); the last one is the row's current owner.
            if not (rec.get("transfer_from") == prev["owner"] and rec["owner"] != prev["owner"]
                    and rec["item"] == prev["item"] and rec["dev_sha"] == prev["dev_sha"]):
                raise TrainError(f"{KNOWN_RED_AMENDMENTS}: {key[0]} {key[1]} is amended twice "
                                 "(a later record must be an owner transfer: transfer_from the "
                                 "previous owner, the same item and dev_sha, a new owner)")
        elif "transfer_from" in rec:
            raise TrainError(f"{KNOWN_RED_AMENDMENTS}: {key[0]} {key[1]}: a transfer with no "
                             "earlier record")
        last[key] = rec
    return records


def amendments_at(t: "Train", rev: str) -> list[dict]:
    """The amendment records at REV; none when REV has no amendments file."""
    p = git(t.root, "show", f"{rev}:{KNOWN_RED_AMENDMENTS}", check=False)
    return parse_amendments(p.stdout) if p.returncode == 0 else []


def verdict_words(rows: list[dict] | None, amendments: list[dict] | None = None) -> str:
    if rows is None:
        return f"no known-red baseline ({KNOWN_REDS} missing): not green"
    if not rows:
        return "green: the known-red baseline is empty"
    amended = {(a["kind"], a["subject"]) for a in amendments or []}
    n_amended = sum(1 for r in rows if (r["kind"], r["subject"]) in amended)
    return (f"non-regressing against {len(rows)} known reds, {n_amended} amended "
            f"({KNOWN_REDS}, {KNOWN_RED_AMENDMENTS}); NOT green")


def certify_failures(root: Path, certify_id: str | None) -> tuple[list[str], list[str]] | None:
    """(failed books, killed books) of a certify's manifest under build/acl2,
    or None when no manifest came back (the verdict is then unknown)."""
    if not certify_id:
        return None
    try:
        manifest = json.loads((root / "build" / "acl2" / certify_id / "manifest.json").read_text())
    except (OSError, ValueError):
        return None
    results = manifest.get("book_results") or {}
    reasons = manifest.get("book_failures") or {}
    import farm  # the one reading of a killed ACL2 (farm.verdict_lines)

    failed, killed = [], []
    for book in sorted(set(reasons) | {b for b, v in results.items() if v != "passed"}):
        match = farm.KILLED_REASON.search("; ".join(reasons.get(book) or []))
        signalled = farm.killed_signal(match.group(1)) if match else None
        (killed if signalled is not None else failed).append(book)
    return failed, killed


# --------------------------------------------------------------------------- merge

def _stage(root: Path, n: int, path: str) -> str | None:
    p = git(root, "show", f":{n}:{path}", check=False)
    return p.stdout if p.returncode == 0 else None


def _union_resolve(t: Train, path: str) -> None:
    ours, base, theirs = (_stage(t.root, n, path) or "" for n in (2, 1, 3))
    with tempfile.TemporaryDirectory() as td:
        files = []
        for name, text in (("ours", ours), ("base", base), ("theirs", theirs)):
            f = Path(td) / name
            f.write_text(text)
            files.append(str(f))
        p = subprocess.run(["git", "merge-file", "-p", "--union", *files], capture_output=True, text=True)
        if p.returncode < 0 or p.returncode > 127:
            raise TrainError(f"git merge-file failed for {path}")
        merged = p.stdout
    (t.root / path).write_text(merged)
    git(t.root, "add", "--", path)


def merge_one(t: Train, st: dict, lane: str, sha: str) -> bool:
    name = lane[5:] if lane.startswith("lane/") else lane
    target = t.branch if t.branch.startswith("integrate/") else f"integrate/{t.branch}"
    msg = f"Merge lane/{name} @{sha} into {target}"
    entry = {"name": name, "sha": sha, "merge": None, "status": "pending", "files": []}
    st["lanes"].append(entry)
    say(f"$ git merge --no-ff -m {msg!r} {sha}")
    p = git(t.root, "merge", "--no-ff", "-m", msg, sha, check=False)
    if p.returncode == 0:
        entry.update(status="merged", merge=t.head())
        t.save(st)
        return True
    conflicted = git(t.root, "diff", "--name-only", "--diff-filter=U").stdout.split()
    if not conflicted:
        git(t.root, "merge", "--abort", check=False)
        entry.update(status="failed", files=[p.stderr.strip() or p.stdout.strip()])
        say(f"  lane {name}: merge failed without conflicts: {entry['files'][0]}")
        t.save(st)
        return False
    bad = [f for f in conflicted if not _generated(f) and f not in UNION]
    if bad:
        git(t.root, "merge", "--abort", check=False)
        entry.update(status="conflict", files=bad)
        say(f"  lane {name}@{sha}: source conflict in {', '.join(bad)}; merge aborted, back to its deputy")
        t.save(st)
        return False
    for f in conflicted:
        if _generated(f):
            say(f"  conflict {f}: take train side (ours)")
            if git(t.root, "checkout", "--ours", "--", f, check=False).returncode == 0:
                git(t.root, "add", "--", f)
            else:
                git(t.root, "rm", "-q", "--", f)
        else:
            say(f"  conflict {f}: union of both sides")
            _union_resolve(t, f)
    git(t.root, "commit", "--no-edit")
    entry.update(status="merged", merge=t.head(), files=conflicted)
    t.save(st)
    return True


def cmd_merge(t: Train, args) -> int:
    if t.dirty():
        raise TrainError("working tree is dirty; refusing to merge")
    t.fetch()
    st = t.load()
    rc = 0
    for spec in args.lanes:
        if "@" not in spec:
            raise TrainError(f"expected LANE@SHA, got {spec!r}")
        lane, sha = spec.rsplit("@", 1)
        if not merge_one(t, st, lane, sha):
            rc = 1
    merged = [l["name"] for l in st["lanes"] if l["status"] == "merged"]
    say(f"merged {len(merged)} lane(s) so far: {', '.join(merged) or '-'}")
    return rc


# --------------------------------------------------------------------------- regen

def _commit_named(t: Train, paths, msg: str) -> bool:
    # a path may be a glob pathspec (the world files: a regen can add or drop
    # a -part-N link), so additions and deletions under it are committed too
    changed = [p for p in paths if git(t.root, "status", "--porcelain", "--", p).stdout.strip()]
    if not changed:
        say("  nothing to commit")
        return False
    git(t.root, "add", "-A", "--", *changed)
    mf = t.dir / "commit-msg.txt"
    t.dir.mkdir(parents=True, exist_ok=True)
    mf.write_text(msg + "\n")
    say(f"$ git commit -F {mf}  # {msg.splitlines()[0]}")
    git(t.root, "commit", "-F", str(mf), "--only", "--", *changed)
    return True


def cmd_regen(t: Train, args) -> int:
    if t.dirty():
        raise TrainError("working tree is dirty; refusing to regenerate")
    st = t.load()
    st["regen"] = []
    st["gates"] = {}
    steps = st["regen"]

    def done(step: str, rc: int) -> int:
        steps.append({"step": step, "rc": rc})
        t.save(st)
        return rc

    # ledger.py --write: proofs.json's event arrays (the views are not committed)
    for step, argv in (
        # first: the books it writes are what the ledger and teeth read
        ("world", [PY3, "tools/extract/world.py"]),
        ("ledger", [PY, "tools/ledger.py", "--write"]),
        # the raw harnesses' derived-stub blocks (31 had drifted by train 51)
        ("stubs", [PY, "tools/harness_check.py", "--write-stubs"]),
        # the teeth obligation manifest of the merged tree (the keystone gate
        # checks it; a conflict on it took the train side at merge)
        ("teeth", [PY, "tools/keystone_emit.py", "--write-manifest"]),
    ):
        rc = t.run(f"regen-{step}", argv)
        if done(step, rc):
            return rc
    st["regen_commits"] = st.get("regen_commits", 0) + 1
    # the label the integrator numbers trains by; the state file's own count
    # restarts with each state file, so it is only the fallback
    n = args.label or st["regen_commits"]
    msg = f"Regenerate train {n}: image-world and extraction world files, proofs.json events, derived harness stubs, teeth obligation manifest"
    _commit_named(t, REGEN_OUTPUTS, msg)
    if done("commit", 0):
        return 1
    say("regen done at " + t.head()[:9])
    return 0


# --------------------------------------------------------------------------- box step

def box_record_path(t: Train) -> Path:
    return t.dir / "box-step.json"


def load_box_record(t: Train) -> dict | None:
    path = box_record_path(t)
    return json.loads(path.read_text()) if path.exists() else None


def cmd_boxstep(t: Train, args) -> int:
    if t.dirty():
        raise TrainError("working tree is dirty; the box step ships HEAD")
    ran_at = t.head()
    argv = ["sh", "tools/remote_check.sh", args.box]
    for out in HBOX_OUTPUTS:
        argv += ["--fetch", out]
    argv += ["--cmd", BOX_CMD]
    rc = t.run(f"boxstep-{args.box}", argv)
    if rc != 0:
        say(f"box step on {args.box} failed (rc {rc}); nothing recorded")
        return rc
    _commit_named(t, HBOX_OUTPUTS, f"interfaces.json, wire-grammar.json: the box step's emits on {args.box} at {ran_at[:9]}")
    record = {"sha": t.head(), "ran_at": ran_at, "box": args.box}
    t.dir.mkdir(parents=True, exist_ok=True)
    box_record_path(t).write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    say(f"box step recorded: {args.box} at {record['sha'][:9]}")
    return 0


def _changed_roots(t: Train, prefix: str) -> list[str]:
    out = git(t.root, "diff", "--name-only", "--diff-filter=AM", "origin/dev", "HEAD", "--", prefix).stdout.split()
    return [p[:-5] for p in out if p.startswith(prefix + "/") and p.endswith(".lisp")]


def makefile_root_list(text: str) -> list[str]:
    """The Makefile's ACL2_BOOKS roots (tools/ledger.py makefile_roots's reading)."""
    match = re.search(r"(?ms)^ACL2_BOOKS\s*\??=\s*(.*?)(?=^\S|\Z)", text)
    if not match:
        raise TrainError("Makefile: no ACL2_BOOKS assignment")
    return [token for token in match.group(1).replace("\\\n", " ").split() if token]


def _added_roots(t: "Train") -> list[str]:
    """Roots HEAD's Makefile lists that origin/dev's does not.  A book that
    becomes a root without changing (a kept claim nothing certified, a test
    re-hooked) is affected by the train though no changed book reaches it;
    train 76 listed three such roots and the changed-book selection missed
    them."""
    head = t.root / "Makefile"
    if not head.is_file():
        return []  # no Makefile, no roots
    shown = git(t.root, "show", "origin/dev:Makefile", check=False)
    # a Makefile new in this train makes every root it lists new
    before = set(makefile_root_list(shown.stdout)) if shown.returncode == 0 else set()
    return [r for r in makefile_root_list(head.read_text(encoding="utf-8")) if r not in before]


def _critical_witness_roots(root: Path, changed: list[str]) -> list[str]:
    """Critical teeth whose theorem's closure changed, from regen's manifest.

    `book` defines the theorem; `owner_book` supplies its teeth and may be
    a test outside the Makefile roots. Include that test even when only a
    transitive dependency of the theorem changed.
    """
    if not changed:
        return []
    import certs

    manifest = root / "planning/teeth-obligations.json"
    try:
        entries = json.loads(manifest.read_text())["entries"]
        witnesses: dict[str, set[str]] = {}
        for entry in entries:
            owner = entry.get("owner_book", "")
            if entry.get("critical") and owner.startswith("tests/acl2/"):
                book = entry["book"].removesuffix(".lisp")
                witnesses.setdefault(book, set()).add(owner.removesuffix(".lisp"))
        targets = set(changed)
        selected = set()
        for book, tests in witnesses.items():
            if targets.intersection(certs.closure(root, book)):
                selected.update(tests)
        return sorted(selected)
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise TrainError(f"cannot select critical witnesses from {manifest}: {error}") from error


def cache_seed_command(t: Train, box: str, tree: str) -> tuple[str, str | None]:
    """Best-effort reuse of the last box step's content-keyed emit caches.

    ledger-forms, ledger-tree (including suspects), callgraph, reach,
    certify-audit and wire-emit all validate content keys before reuse;
    wire-emit also validates the destination wire-grammar.json bytes.
    The success marker, not merely a local record, determines cache_seed.
    """
    def skip(reason):
        return f"echo {shlex.quote('== cache seed skipped: ' + reason)}", None

    try:
        previous = load_box_record(t)
        if not previous:
            return skip("no previous box record")
        if previous.get("box") != box:
            return skip("previous box differs")
        run = previous.get("run")
        if not isinstance(run, str) or not run or Path(run).name != run:
            return skip("no previous farm run")
        record = json.loads((t.root / "build" / "farm" / f"{run}.json").read_text())
        if record.get("host", record.get("box", box)) != box:
            return skip("previous farm box differs")
        previous_tree = record.get("remote_path")
        if not isinstance(previous_tree, str) or not previous_tree:
            return skip("no previous farm tree")
    except (OSError, ValueError, AttributeError):
        return skip("previous farm record unavailable")
    source = shlex.quote(previous_tree.rstrip("/") + "/build/cache/.")
    destination = shlex.quote(tree.rstrip("/") + "/build/cache/")
    success = shlex.quote("== cache seed " + run)
    if previous_tree.rstrip("/") == tree.rstrip("/"):
        # farm reuses one remote tree per worktree: its build/cache is already there
        return f"echo {shlex.quote('== cache seed ' + run + ' (same tree; cache in place)')}", run
    return (f"if [ -d {source} ]; then "
            f"if mkdir -p {destination} && cp -a {source} {destination}; then "
            f"echo {success}; else echo '== cache seed skipped: copy failed'; fi; "
            "else echo '== cache seed skipped: previous cache missing'; fi", run)


def emit_remote_command(tree: str, envs: str, box: str, seed: str) -> str:
    wrap = WRAPS.get(box, "")
    body = (f"{seed}; {envs}; "
            'eval "$(python3 tools/native_env.py sbcl --export 2>/dev/null)"; '
            + EMIT_CMD)
    # The copy shares the emits' timeout and hbox resource wrapper.
    return (f"cd {shlex.quote(tree)} && "
            f"{wrap + ' ' if wrap else ''}timeout {EMIT_TIMEOUT_SECONDS} sh -c {shlex.quote(body)}")


def cmd_certify(t: Train, args) -> int:
    if t.dirty():
        # farm ships the worktree (rsync without .git/ and build/), so an
        # untracked file would be certified and emitted as if it were HEAD
        raise TrainError("working tree is dirty (untracked files included); the box step ships HEAD")
    ran_at = t.head()
    books = _changed_roots(t, "books")
    tests = _changed_roots(t, "tests/acl2")
    # critical witness tests whose theorem closure changed: always, since a
    # stale witness fails keystone_emit's critical gate (trains 52 and 55
    # needed a hand certify of them)
    witnesses = _critical_witness_roots(t.root, books)
    added = _added_roots(t)
    if added:
        say(f"certify: {len(added)} root(s) new in the Makefile: " + ", ".join(added))
    roots = list(dict.fromkeys(["books/wire-export", *books, *tests, *witnesses, *added]))
    argv = [PY, "tools/farm.py"]
    # the affected closure: every Makefile root a changed book reaches
    for b in books:
        argv += ["--affected-by", b]
    argv += ["--timeout-seconds", str(FARM_TIMEOUT_SECONDS), "submit", args.box, *roots]
    t0 = time.monotonic()
    say("$ " + " ".join(argv))
    sub = subprocess.run(argv, cwd=t.root, capture_output=True, text=True)
    t.logs.mkdir(parents=True, exist_ok=True)
    (t.logs / f"certify-submit-{args.box}.log").write_text(sub.stdout + sub.stderr)
    for line in sub.stderr.splitlines()[-12:]:
        say("  | " + line)
    run = sub.stdout.strip().splitlines()[-1].strip() if sub.stdout.strip() else ""
    if sub.returncode != 0 or not run:
        say(f"certify on {args.box}: submit failed (rc {sub.returncode}); nothing recorded")
        return sub.returncode or 1
    t1 = time.monotonic()
    rc = t.run(f"certify-wait-{args.box}", [PY, "tools/farm.py", "wait", args.box, run])
    t2 = time.monotonic()
    rec = json.loads((t.root / "build" / "farm" / f"{run}.json").read_text())
    known_seen: list[str] = []
    if rc != 0:
        outcome = certify_failures(t.root, rec.get("certify_id"))
        if outcome is None:
            say(f"certify on {args.box} failed (rc {rc}) and no manifest came back; nothing recorded")
            return rc
        failed, killed = outcome
        rows = known_reds_at(t, "HEAD") or []
        known = {r["subject"] for r in rows if r["kind"] == "certify"}
        new = [b for b in failed if b not in known]
        if killed or new or not failed:
            for b in new:
                say(f"  NEW certify red (not in {KNOWN_REDS}): {b}")
            for b in killed:
                say(f"  KILLED (no verdict): {b}")
            say(f"certify on {args.box} failed (rc {rc}); nothing recorded")
            return rc
        known_seen = failed
        say(f"certify on {args.box}: {len(failed)} failed book(s), every one a known red: {', '.join(failed)}")
    tree = rec["remote_path"]
    env = subprocess.run([PY3, "tools/box_table.py", "env", args.box], cwd=t.root, capture_output=True, text=True)
    envs = env.stdout.strip() if env.returncode == 0 and env.stdout.strip() else "true"
    seed, seed_run = cache_seed_command(t, args.box, tree)
    remote_cmd = emit_remote_command(tree, envs, args.box, seed)
    say(f"$ {SSH} {args.box} <emits in {tree}>")
    log = t.logs / f"certify-emit-{args.box}.log"
    p = subprocess.run([SSH, args.box, remote_cmd], capture_output=True, text=True)
    log.write_text(p.stdout + p.stderr)
    cache_seed = seed_run if seed_run and any(line == f"== cache seed {seed_run}" or line.startswith(f"== cache seed {seed_run} ")
                                              for line in p.stdout.splitlines()) else None
    steps = {m.group(1): int(m.group(2)) for m in re.finditer(r"^== step (\S+) (\d+)$", p.stdout, re.M)}
    if p.returncode != 0:
        say(f"emits on {args.box} failed (rc {p.returncode}; log {log}); nothing recorded")
        for line in (p.stdout + p.stderr).splitlines()[-30:]:
            say("  | " + line)
        return p.returncode
    for out in HBOX_OUTPUTS:
        f = subprocess.run(f"{shlex.quote(SSH)} {args.box} {shlex.quote('cd ' + shlex.quote(tree) + ' && tar cf - ' + out)} | tar xf - -C {shlex.quote(str(t.root))}",
                           shell=True, capture_output=True, text=True)
        if f.returncode != 0:
            say(f"could not fetch {out} from {args.box}:{tree}: {f.stderr.strip()}; nothing recorded")
            return 1
    t3 = time.monotonic()
    wall = {"install": round(t1 - t0), "certify": round(t2 - t1), "emit": round(t3 - t2), "total": round(t3 - t0), "emit_steps": steps}
    _commit_named(t, HBOX_OUTPUTS, f"interfaces.json, wire-grammar.json: the train certify's emits on {args.box} at {ran_at[:9]}")
    record = {"sha": t.head(), "ran_at": ran_at, "box": args.box, "run": run,
              "certify_id": rec.get("certify_id"), "wall": wall, "cache_seed": cache_seed,
              "known_reds_seen": known_seen}
    t.dir.mkdir(parents=True, exist_ok=True)
    box_record_path(t).write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    st = t.load()
    st["box_wall"] = wall
    st["box_run"] = run
    st["cache_seed"] = cache_seed
    st["certify_known_reds_seen"] = known_seen
    t.save(st)
    say(f"certify recorded: {args.box} run {run} at {record['sha'][:9]}; wall install {wall['install']}s "
        f"certify {wall['certify']}s emit {wall['emit']}s "
        f"({', '.join(f'{k} {v}s' for k, v in steps.items())}) total {wall['total']}s")
    return 0


# --------------------------------------------------------------------------- gate

# The lock gate's contract with tools/lock_discipline_check.py --json
# (ruling 21): exit 0 and a JSON object carrying every field below with its
# type.  Any other exit (a killed child is negative), unparseable output, a
# missing or mistyped field, or a malformed `new` entry is a CHECKER FAILURE,
# never an empty finding set.
LOCK_JSON_FIELDS = {"new": list, "stale": list, "findings": list}
# Repair-item states that no longer own a key (anything else is open).
CLOSED_ITEM_STATES = frozenset({"landed", "refuted", "duplicate", "closed"})


def _lock_keys(t: Train, cwd: Path) -> tuple[set[str] | None, str | None]:
    """(keys new against the checker's baseline, None), or (None, why) when
    the checker broke its contract."""
    p = subprocess.run([PY, "tools/lock_discipline_check.py", "--json"], cwd=cwd, capture_output=True, text=True)
    say(f"$ (in {cwd}) {PY} tools/lock_discipline_check.py --json  -> rc {p.returncode}")

    def fail(why: str):
        say(f"  lock_discipline_check contract broken: {why}: " + (p.stdout + p.stderr)[-300:])
        return None, why

    if p.returncode != 0:
        return fail(f"exit status {p.returncode}")
    try:
        data = json.loads(p.stdout)
    except ValueError:
        return fail("output is not JSON")
    if not isinstance(data, dict):
        return fail("output is not a JSON object")
    for field, kind in LOCK_JSON_FIELDS.items():
        if field not in data:
            return fail(f"missing field {field!r}")
        if not isinstance(data[field], kind):
            return fail(f"field {field!r} is not a {kind.__name__}")
    keys = set()
    for e in data["new"]:
        # `new` holds key strings (lock-check-full-output, d4d8514f6) or
        # finding dicts with a 'key' (earlier checkers): accept both.
        key = e if isinstance(e, str) else e.get("key") if isinstance(e, dict) else None
        if not isinstance(key, str) or not key:
            return fail(f"malformed entry in 'new': {str(e)[:80]}")
        keys.add(key)
    return keys, None


def _lock_owners(root: Path, keys) -> dict[str, list[dict]]:
    """For each key, the repair items naming it verbatim (id, owner, state)."""
    def strings(v):
        if isinstance(v, str):
            yield v
        elif isinstance(v, dict):
            for x in v.values():
                yield from strings(x)
        elif isinstance(v, list):
            for x in v:
                yield from strings(x)

    items = []
    for path in sorted((root / "planning" / "repair" / "items").glob("*.json")):
        try:
            d = json.loads(path.read_text())
        except (OSError, ValueError):
            continue
        if isinstance(d, dict):
            # match the item's decoded text, not its JSON spelling (a key
            # after "\n" is preceded by the escape's letter n in the raw file)
            text = "\n".join(strings(d))
            items.append((d.get("id", path.stem), d.get("owner"), d.get("state"), text))
    out = {}
    for k in keys:
        pat = re.compile(r"(?<![\w|*:-])" + re.escape(k) + r"(?![\w|*:-])")
        out[k] = [{"item": i, "owner": o, "state": s} for i, o, s, raw in items if pat.search(raw)]
    return out


def _ascii_gate(t: Train) -> int:
    """ascii_check refusals in files this train changes (books/, host/).  The
    tree carries older refusals (make check's debt); a train must add none:
    U+2019 in host docstrings broke the ASCII-reading natives (lock-io-out)."""
    changed = set(git(t.root, "diff", "--name-only", "origin/dev", "HEAD", "--", "books", "host").stdout.split())
    if not changed:
        say("books/ and host/ unchanged vs origin/dev: ascii_check skipped")
        return 0
    p = subprocess.run([PY, "tools/ascii_check.py"], cwd=t.root, capture_output=True, text=True)
    t.logs.mkdir(parents=True, exist_ok=True)
    (t.logs / "gate-ascii.log").write_text(p.stdout + p.stderr)
    hits = [line for line in p.stdout.splitlines()
            if line.startswith("REFUSED ") and line.split()[1].split(":")[0] in changed]
    say(f"$ {PY} tools/ascii_check.py  -> {len(hits)} refusal(s) in {len(changed)} changed file(s)")
    for line in hits[:20]:
        say("  | " + line)
    return 1 if hits else 0


def _baseline_gate(t: Train) -> tuple[int, dict]:
    """(rc, record) of the known-reds gate: the file parses at HEAD, every
    row's repair item exists and is open, and no row is added relative to
    origin/dev unless an amendment names it (the first file is the baseline
    itself).  The amendments are append-only and each names a present row."""
    try:
        head_rows = known_reds_at(t, "HEAD")
        dev_rows = known_reds_at(t, "origin/dev")
        head_amend = amendments_at(t, "HEAD")
        dev_amend = amendments_at(t, "origin/dev")
    except TrainError as error:
        say(f"baseline: {error}")
        return 1, {"error": str(error)}
    if head_rows is None:
        say(f"baseline: {KNOWN_REDS} is missing at HEAD")
        return 1, {"error": "missing"}
    items = t.root / "planning" / "repair" / "items"

    def item_state(name):
        try:
            return json.loads((items / f"{name}.json").read_text()).get("state"), True
        except (OSError, ValueError):
            return None, False

    unowned, closed = [], []
    for row in head_rows:
        state, found = item_state(row["item"])
        if not found:
            unowned.append(f"{row['kind']} {row['subject']} ({row['item']})")
        elif state in CLOSED_ITEM_STATES:
            closed.append(f"{row['kind']} {row['subject']} ({row['item']} {state})")
    keys = lambda rows: {(r["kind"], r["subject"]) for r in rows}
    row_by_key = {(r["kind"], r["subject"]): r for r in head_rows}
    amended = {(a["kind"], a["subject"]): a for a in head_amend}
    added_all = sorted(keys(head_rows) - keys(dev_rows)) if dev_rows is not None else []
    added = [k for k in added_all if k not in amended]
    admitted = [k for k in added_all if k in amended]
    gone = sorted(keys(dev_rows) - keys(head_rows)) if dev_rows is not None else []
    # append-only: every record on origin/dev is at HEAD, unchanged and in order
    rewritten = head_amend[:len(dev_amend)] != dev_amend
    dangling, mismatched = [], []
    for k, a in amended.items():
        row = row_by_key.get(k)
        if row is None:
            state, found = item_state(a["item"])
            if not (found and state in CLOSED_ITEM_STATES):
                dangling.append(f"{k[0]} {k[1]}")
        elif (row["item"], row["owner"]) != (a["item"], a["owner"]):
            mismatched.append(f"{k[0]} {k[1]}")
    for k in added:
        say(f"  known red ADDED by this train (rows shrink only): {k[0]} {k[1]}")
    for k in admitted:
        say(f"  known red added by amendment ({amended[k]['item']}, measured at {amended[k]['dev_sha']}): {k[0]} {k[1]}")
    if rewritten:
        say(f"  {KNOWN_RED_AMENDMENTS} is append-only: a record on origin/dev was edited or dropped")
    for k in dangling:
        say(f"  amendment names no known-red row (amendments cannot be stockpiled): {k}")
    for k in mismatched:
        say(f"  amendment disagrees with its row on item or owner: {k}")
    for k in unowned:
        say(f"  known red with no repair item: {k}")
    for k in closed:
        say(f"  known red whose item is closed (remove the row or reopen the item): {k}")
    n_amended = sum(1 for k in amended if k in row_by_key)
    say(f"baseline: {len(head_rows)} row(s), {n_amended} amended; added {len(added)}; "
        f"added by amendment {len(admitted)}; gone {len(gone)}"
        + ("; first baseline (none on origin/dev)" if dev_rows is None else ""))
    rc = 1 if (added or unowned or closed or rewritten or dangling or mismatched) else 0
    return rc, {"rows": len(head_rows), "amended": n_amended, "added": [list(k) for k in added],
                "admitted": [list(k) for k in admitted], "gone": [list(k) for k in gone],
                "amendments_rewritten": rewritten, "dangling_amendments": dangling,
                "mismatched_amendments": mismatched,
                "unowned": unowned, "closed_items": closed, "established": dev_rows is None}


def image_modules(changed: list[str]) -> dict[str, list[str]]:
    """The native modules the train's diff obliges (IMAGE_RULES), each with
    the changed paths that oblige it."""
    need: dict[str, list[str]] = {}
    for _why, paths, modules in IMAGE_RULES:
        hits = [f for f in changed
                if any(f.startswith(p) if p.endswith("/") else f == p for p in paths)]
        if hits:
            for m in modules:
                need.setdefault(m, [])
                need[m] += [h for h in hits if h not in need[m]]
    return need


def parse_image_results(text: str) -> dict[str, dict]:
    """The box's per-module outcome from the lines `RC MODULE N` (rc/test-MODULE)
    and `FN_TEST_BUDGET_RESULT {...}` (logs/test-MODULE.log): module -> {"rc",
    "cases": {case: status}}.  A module with an rc and no result line has no
    cases (killed, or refused before its first test)."""
    out: dict[str, dict] = {}
    for line in text.splitlines():
        words = line.split()
        if len(words) == 3 and words[0] == "RC" and words[2].lstrip("-").isdigit():
            out.setdefault(words[1], {"cases": {}})["rc"] = int(words[2])
        elif line.startswith("FN_TEST_BUDGET_RESULT "):
            try:
                record = json.loads(line.split(" ", 1)[1])
            except ValueError:
                continue
            module = record.get("module")
            if isinstance(module, str):
                entry = out.setdefault(module, {"cases": {}})
                entry["cases"] = {c: s for c, s in record.get("cases") or []}
    return {m: e for m, e in out.items() if "rc" in e}


def image_verdict(need: dict[str, list[str]], record: dict | None, head: str,
                  rows: list[dict] | None) -> tuple[int, dict]:
    """The image gate's decision.  Green when nothing is obliged, or when every
    obliged module ran on the image of HEAD and each red case in it is a
    `native` row of planning/known-reds.json.  A module that did not run (an
    interrupted image gate) refuses the push until it has; so does a module
    that failed with no case recorded."""
    if not need:
        return 0, {"skipped": True}
    if record is None:
        return 1, {"error": "no image run recorded at HEAD; run tools/hbox_native.sh HEAD "
                            "MODULES, then `train.py image`", "need": sorted(need)}
    if record.get("source") != head:
        return 1, {"error": "the recorded image run is of %s, not HEAD" % str(record.get("source"))[:9],
                   "need": sorted(need)}
    known = {r["subject"] for r in rows or [] if r.get("kind") == "native"}
    results = record.get("modules", {})
    missing = sorted(m for m in need if m not in results)
    unexplained, known_seen, skipped = [], [], []
    for m in sorted(need):
        if m not in results:
            continue
        rc, cases = results[m]["rc"], results[m]["cases"]
        reds = sorted(c for c, s in cases.items() if s not in IMAGE_CASE_PASS)
        if rc == IMAGE_RC_ALL_SKIPPED and not reds:
            skipped.append(m)
        elif rc != 0 and not reds:
            unexplained.append(f"{m} (rc {rc}, no case recorded)")
        for c in reds:
            (known_seen if c in known else unexplained).append(c)
    extra = {"need": sorted(need), "runs": sorted(record.get("runs") or {}), "missing": missing,
             "unexplained": unexplained, "known_reds": known_seen, "skipped": skipped}
    return (1 if missing or unexplained else 0), extra


def merge_image_run(prior: dict | None, head: str, box: str, directory: str,
                    modules: dict[str, dict]) -> dict:
    """HEAD's image record with one more run read into it.  An obliged set can
    need several runs at HEAD (heap_from_profile's small cases run only under
    `hbox_native.sh --mem 2G`, the other modules at the default), so the record
    keeps each module with the run it came from.  A record of another commit is
    replaced; re-reading a run replaces that run's modules; a module already
    read from a different run at HEAD is refused, so no module's verdict is
    ever chosen between two runs."""
    record = {"source": head, "runs": {}, "modules": {}}
    if prior and prior.get("source") == head and "runs" in prior:
        record["runs"] = {d: b for d, b in prior["runs"].items() if d != directory}
        record["modules"] = {m: e for m, e in prior["modules"].items() if e.get("run") != directory}
    twice = sorted(m for m in modules if m in record["modules"])
    if twice:
        raise TrainError("module(s) already read from another run at HEAD: " + ", ".join(
            f"{m} ({record['modules'][m]['run']})" for m in twice) + f"; not read again from {directory}")
    record["runs"][directory] = box
    for m, e in modules.items():
        record["modules"][m] = dict(e, run=directory)
    return record


def image_record_path(t: "Train", label: str) -> Path:
    return t.root / IMAGE_RUN_RECORD.format(label=label)


def cmd_image(t: Train, args) -> int:
    """Read one of HEAD's image runs from its box into the train state: each
    module's rc and case statuses and the run it came from, for the image gate
    (merge_image_run: several runs at HEAD combine, one module per run)."""
    head = t.head()
    label = args.label or head[:12]
    path = image_record_path(t, label)
    if not path.is_file():
        raise TrainError(f"no image run record {path}; run tools/hbox_native.sh {head[:9]} MODULES")
    run = dict(l.split("=", 1) for l in path.read_text().splitlines() if "=" in l)
    if run.get("source") != head:
        raise TrainError(f"{path} is of {run.get('source', '?')[:9]}, not HEAD {head[:9]}")
    script = ("cd %s && for f in rc/test-*; do [ -f \"$f\" ] && echo \"RC ${f#rc/test-} $(cat \"$f\")\"; done; "
              "grep -h FN_TEST_BUDGET_RESULT logs/test-*.log 2>/dev/null; true") % shlex.quote(run["dir"])
    p = subprocess.run(["timeout", "60", "ssh", "-n", run["box"], script],
                       capture_output=True, text=True)
    if p.returncode != 0:
        raise TrainError(f"reading {run['box']}:{run['dir']} failed (rc {p.returncode}): {p.stderr.strip()[:200]}")
    st = t.load()
    read = parse_image_results(p.stdout)
    st["image"] = merge_image_run(st.get("image"), head, run["box"], run["dir"], read)
    t.save(st)
    for m, e in sorted(read.items()):
        reds = [c for c, s in e["cases"].items() if s not in IMAGE_CASE_PASS]
        say(f"image {m}: rc {e['rc']}, {len(e['cases'])} cases, red {len(reds)} ({run['dir']})")
    return 0


def _launches_native_image(path: Path) -> bool:
    """A suite that imports tests/native_harness starts the built image
    (tests/test_bp_node_native.py and the other BP suites are named
    *_native.py, not test_native_*; train 54 ran one and it found no image)."""
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return False
    return re.search(r"^\s*(from\s+tests\.native_harness\s+import|from\s+native_harness\s+import|"
                     r"import\s+(tests\.)?native_harness\b)", text, re.M) is not None


def unit_tests(root: Path, changed: list[str]) -> list[str]:
    """UNIT_TESTS, then the tests of what the train changed, in order, once each."""
    tests = list(UNIT_TESTS)
    for path in changed:
        p = Path(path)
        if p.name.startswith("test_native_") or _launches_native_image(root / p):
            # needs a native image (build/fn-host-*); N's native gate on the
            # box is its gate, not this tree
            continue
        if p.parent.as_posix() == "tests" and p.name.startswith("test_") and p.suffix == ".py":
            candidate = path
        elif p.parent.as_posix() == "tools" and p.suffix == ".py":
            candidate = f"tests/test_{p.stem}.py"
        else:
            continue
        if candidate not in tests and (root / candidate).is_file():
            tests.append(candidate)
    return tests


def cmd_gate(t: Train, args) -> int:
    if t.dirty():
        raise TrainError("working tree is dirty; gates must run at a committed HEAD")
    t.fetch()
    st = t.load()
    head = t.head()
    gates: dict = {}
    st["gates"] = gates

    def rec(name: str, rc: int, **extra) -> None:
        gates[name] = {"rc": rc, "head": head, **extra}
        t.save(st)

    anc = git(t.root, "merge-base", "--is-ancestor", "origin/dev", "HEAD", check=False).returncode
    say(f"origin/dev is ancestor of HEAD: {'yes' if anc == 0 else 'NO'}")
    rec("ancestor", anc)
    rec("ledger", t.run("gate-ledger", [PY, "tools/ledger.py", "--check"]))
    rec("current_view", t.run("gate-current_view", [PY, "tools/current_view.py", "--check"]))
    # check-fast's main_last_check: a test file whose __main__ block is not last
    # silently skips every class after it (dev d67a244fa, tests/test_image_set.py)
    rec("main_last", t.run("gate-main_last", [PY, "tools/main_last_check.py"]))
    # the teeth gate: a new toothless keystone or a stale teeth manifest
    # (train 41: a lane's new keystones without teeth, caught by hand)
    rec("keystone", t.run("gate-keystone", [PY, "tools/keystone_emit.py", "--check"]))

    host = git(t.root, "diff", "--name-only", "origin/dev", "HEAD", "--", "host").stdout.split()
    if host:
        rec("host_load", t.run("gate-host_load", [PY, "tools/host_check.py", "--load"]))
    else:
        say("host unchanged vs origin/dev: host_check --load skipped")
        rec("host_load", 0, skipped=True)

    rec("ascii", _ascii_gate(t))

    box = load_box_record(t)
    if box is None:
        say("box_step: no box step recorded; run `train.py boxstep BOX`")
        rec("box_step", 1, error="no box step recorded")
    elif box["sha"] == head:
        say(f"box_step: ran at HEAD on {box['box']}")
        rec("box_step", 0, ran_on=box["box"])
    elif git(t.root, "merge-base", "--is-ancestor", box["sha"], "HEAD", check=False).returncode != 0:
        say(f"box_step: the recorded box step {box['sha'][:9]} is not an ancestor of HEAD; run `train.py boxstep BOX`")
        rec("box_step", 1, error="box step not an ancestor", box_sha=box["sha"])
    else:
        changed = git(t.root, "diff", "--name-only", box["sha"], "HEAD", "--", *BOX_PATHS).stdout.split()
        if changed:
            say(f"box_step: {len(changed)} file(s) under {', '.join(BOX_PATHS)} changed since the box step at "
                f"{box['sha'][:9]} (first: {changed[0]}); run `train.py boxstep BOX`")
            rec("box_step", 1, error="box paths changed since the box step", box_sha=box["sha"], changed=changed)
        else:
            local = {name: t.run(f"gate-box-{name}", [PY, *argv]) for name, argv in LOCAL_BOX_CHECKS}
            rc = 0 if all(v == 0 for v in local.values()) else 1
            say(f"box_step: inherits {box['sha'][:9]} ({box['box']}); local checks "
                + ", ".join(f"{k}={v}" for k, v in local.items()))
            rec("box_step", rc, inherits_from=box["sha"], box=box["box"], local_checks=local)

    tmp = Path(tempfile.mkdtemp(prefix="dev-", dir=str(t.dir)))
    wt = tmp / "dev"
    try:
        git(t.root, "worktree", "add", "--detach", str(wt), "origin/dev")
        old, why_old = _lock_keys(t, wt)
    finally:
        git(t.root, "worktree", "remove", "--force", str(wt), check=False)
        shutil.rmtree(tmp, ignore_errors=True)
    new, why_new = _lock_keys(t, t.root)
    if old is None or new is None:
        rec("lock_delta", 1, error="lock_discipline_check failed its contract",
            dev_error=why_old, head_error=why_new)
    else:
        # Ruling 21: the only green is "this train adds no key relative to
        # dev".  Dev's existing keys are the recorded red list, each owned by
        # an open repair item; a key with no item, or whose every item is
        # closed, fails the gate too.  Nothing else exists.
        added, gone = sorted(new - old), sorted(old - new)
        owners = _lock_owners(t.root, sorted(new))
        reds = [{"key": k, "items": owners[k]} for k in sorted(new & old)]
        unowned = sorted(k for k in new & old if not owners[k])
        closed = sorted(k for k in new & old if owners[k]
                        and all(i["state"] in CLOSED_ITEM_STATES for i in owners[k]))
        say(f"lock delta: added {added or '-'}; gone {gone or '-'}; "
            f"owned reds on dev {len(reds) - len(unowned) - len(closed)}")
        for k in added:
            say(f"  NEW lock key added by this train: {k}")
        for k in unowned:
            say(f"  UNOWNED lock key on dev (no repair item names it): {k}")
        for k in closed:
            say(f"  lock key persists but its items are closed: {k} "
                + ", ".join(i["item"] for i in owners[k]))
        rc = 1 if (added or unowned or closed) else 0
        rec("lock_delta", rc, added=added, gone=gone, unowned=unowned,
            closed_items=closed, owned_reds=reds)

    base_rc, base_record = _baseline_gate(t)
    rec("baseline", base_rc, **base_record)

    files = git(t.root, "diff", "--name-only", "origin/dev", "HEAD").stdout.split()
    if files:
        rec("secrets", t.run("gate-secrets", [PY3, "tools/secrets_check.py", *files]))
    else:
        rec("secrets", 0, skipped=True)

    unit = unit_tests(t.root, files)
    results = {}
    for test in unit:
        if not (t.root / test).is_file():
            say(f"unit: {test} is missing")
            results[test] = 1
        else:
            results[test] = t.run("gate-unit-" + Path(test).stem, [PY, "-m", "unittest", test])
    rec("unit", 0 if all(v == 0 for v in results.values()) else 1, tests=results)

    need = image_modules(files)
    image_rc, image_record = image_verdict(need, st.get("image"), head, known_reds_at(t, "HEAD"))
    if need:
        say(f"image: obliged {len(need)} module(s) by " + ", ".join(sorted({f for v in need.values() for f in v})[:5]))
        for m in image_record.get("missing", []):
            say(f"  NOT RUN on HEAD's image: {m}")
        for c in image_record.get("unexplained", []):
            say(f"  RED and not a known red: {c}")
        for m in image_record.get("skipped", []):
            say(f"  ran with every test skipped (not covered): {m}")
        if "error" in image_record:
            say(f"  {image_record['error']}")
    else:
        say("image: no change obliges an image module")
    rec("image", image_rc, **image_record)

    bad = [n for n, g in gates.items() if g["rc"] != 0]
    say(f"gates at {head[:9]}: " + ", ".join(f"{n}={g['rc']}" for n, g in gates.items()))
    return 1 if bad else 0


# --------------------------------------------------------------------------- push

def cmd_push(t: Train, args) -> int:
    st = t.load()
    head = t.head()
    if t.dirty():
        raise TrainError("working tree is dirty; push refused")
    for s in st.get("regen", []):
        if s["rc"] != 0:
            raise TrainError(f"regen step {s['step']} failed (rc {s['rc']}); push refused")
    gates = st.get("gates", {})
    for name in GATES:
        g = gates.get(name)
        if g is None:
            raise TrainError(f"gate {name} has not run; push refused")
        if g["head"] != head:
            raise TrainError(f"gate {name} ran at {g['head'][:9]} but HEAD is {head[:9]}; re-run gate")
        if g["rc"] != 0:
            raise TrainError(f"gate {name} failed (rc {g['rc']}); push refused")
    t.fetch()
    if git(t.root, "merge-base", "--is-ancestor", "origin/dev", "HEAD", check=False).returncode != 0:
        raise TrainError("origin/dev is no longer an ancestor of HEAD; re-merge and re-gate")
    old = git(t.root, "rev-parse", "origin/dev").stdout.strip()
    for target in ("dev", t.branch):
        say(f"$ git push origin HEAD:{target}")
        p = git(t.root, "push", "origin", f"HEAD:{target}", check=False)
        if p.returncode != 0:
            raise TrainError(f"push to {target} failed: {p.stderr.strip()}")
    carried = ", ".join(f"{l['name']}@{l['sha'][:9]}" for l in st["lanes"] if l["status"] == "merged")
    say(f"dev {old[:9]}..{head[:9]} carried: {carried or '-'}")
    say("verdict: " + verdict_words(known_reds_at(t, "HEAD"), amendments_at(t, "HEAD")))
    b = gates["box_step"]
    say("box step: " + (f"inherited from {b['inherits_from'][:9]} ({b['box']})" if "inherits_from" in b
                        else f"ran at HEAD on {b['ran_on']}"))
    return 0


# --------------------------------------------------------------------------- status

def cmd_status(t: Train, args) -> int:
    st = t.load()
    head = t.head()
    say(f"branch {t.branch} HEAD {head[:9]} state {t.state_path}")
    for l in st["lanes"]:
        say(f"  lane {l['name']}@{l['sha'][:9]}: {l['status']}" + (f" ({', '.join(l['files'])})" if l["files"] else ""))
    for s in st.get("regen", []):
        say(f"  regen {s['step']}: rc {s['rc']}")
    if st.get("box_wall"):
        w = st["box_wall"]
        say(f"  certify {st.get('box_run')}: install {w['install']}s, certify {w['certify']}s, emit {w['emit']}s, total {w['total']}s")
    try:
        say("  verdict: " + verdict_words(known_reds_at(t, "HEAD"), amendments_at(t, "HEAD")))
    except TrainError as error:
        say(f"  verdict: {error}")
    for n in GATES:
        g = st.get("gates", {}).get(n)
        if g:
            say(f"  gate {n}: rc {g['rc']} at {g['head'][:9]}" + ("" if g["head"] == head else " (STALE)"))
        else:
            say(f"  gate {n}: not run")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    m = sub.add_parser("merge")
    m.add_argument("lanes", nargs="+", metavar="LANE@SHA")
    r = sub.add_parser("regen")
    r.add_argument("--label", metavar="N", help="the train number for the regen commit messages")
    b = sub.add_parser("boxstep")
    b.add_argument("box", choices=("hbox", "persvati"))
    c = sub.add_parser("certify")
    c.add_argument("box", choices=("hbox", "persvati"))
    g = sub.add_parser("gate")
    i = sub.add_parser("image")
    i.add_argument("--label", help="the run's label (default: HEAD's first 12 hex digits); "
                   "each run read at HEAD adds its modules to HEAD's image record")
    sub.add_parser("push")
    sub.add_parser("status")
    args = ap.parse_args(argv)
    try:
        t = Train(toplevel(Path.cwd()))
        rc = {"merge": cmd_merge, "regen": cmd_regen, "boxstep": cmd_boxstep, "certify": cmd_certify, "gate": cmd_gate,
              "image": cmd_image, "push": cmd_push, "status": cmd_status}[args.cmd](t, args)
    except TrainError as e:
        say(f"train: {e}")
        rc = 2
    # one completion line per command, for a Monitor on a detached run
    say(f"TRAIN-DONE {args.cmd} rc={rc}")
    return rc


if __name__ == "__main__":
    sys.exit(main())

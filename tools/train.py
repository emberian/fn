#!/usr/bin/env python3.12
"""Drive the integrator's merge train: merge, regen, gate, push.

Run from the batch tree (a git worktree on branch integrate/<name>).  The order
of regeneration is fixed and the push is conditional on gates that ran at the
exact HEAD being pushed, recorded in build/train/<branch>.json.

    train.py merge LANE@SHA [LANE@SHA ...]
    train.py regen [--label N]
    train.py certify BOX             # books train: ONE farm run (install, certify), then the emits in its tree
    train.py boxstep BOX             # tools-only trains / persvati fallback: the box step in a fresh tree
    train.py gate [--strict-lock]
    train.py push
    train.py status

A books train runs `certify BOX`: one farm run of books/wire-export plus the
train's changed books and tests (one cache install, one certify), then the emit
and check half of BOX_CMD over ssh in that run's tree, under swarm-build and a
timeout.  It records the same box-step.json as `boxstep` plus the farm run, the
certify id and the install/certify/emit wall seconds (also in the train state,
shown by `status`).

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
)
# planning/proofs.json is NOT here: ledger.py --write regenerates only its
# event arrays, and lanes curate its rows (re-pointing a PRF row at a renamed
# keystone), so a conflict there goes back to the lane like source does.
# Tail-append files: keep both sides' lines.
UNION = ("planning/decisions.md",)

# Files the regen step is allowed to commit (only those that exist/changed).
REGEN_OUTPUTS = (
    "planning/proofs.json",
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

GATES = ("ancestor", "ledger", "current_view", "main_last", "host_load", "box_step", "lock_delta", "secrets")


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
    bad = [f for f in conflicted if f not in GENERATED and f not in UNION]
    if bad:
        git(t.root, "merge", "--abort", check=False)
        entry.update(status="conflict", files=bad)
        say(f"  lane {name}@{sha}: source conflict in {', '.join(bad)}; merge aborted, back to its deputy")
        t.save(st)
        return False
    for f in conflicted:
        if f in GENERATED:
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
    present = [p for p in paths if (t.root / p).exists()]
    changed = [p for p in present if git(t.root, "status", "--porcelain", "--", p).stdout.strip()]
    if not changed:
        say("  nothing to commit")
        return False
    git(t.root, "add", "--", *changed)
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
        ("ledger", [PY, "tools/ledger.py", "--write"]),
    ):
        rc = t.run(f"regen-{step}", argv)
        if done(step, rc):
            return rc
    st["regen_commits"] = st.get("regen_commits", 0) + 1
    # the label the integrator numbers trains by; the state file's own count
    # restarts with each state file, so it is only the fallback
    n = args.label or st["regen_commits"]
    msg = f"Regenerate train {n}: proofs.json events"
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
    roots = list(dict.fromkeys(["books/wire-export", *books, *tests]))
    argv = [PY, "tools/farm.py"]
    if books:
        argv += ["--lane"]
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
    if rc != 0:
        say(f"certify on {args.box} failed (rc {rc}); nothing recorded")
        return rc
    rec = json.loads((t.root / "build" / "farm" / f"{run}.json").read_text())
    tree = rec["remote_path"]
    env = subprocess.run([PY3, "tools/box_table.py", "env", args.box], cwd=t.root, capture_output=True, text=True)
    envs = env.stdout.strip() if env.returncode == 0 and env.stdout.strip() else "true"
    seed, seed_run = cache_seed_command(t, args.box, tree)
    remote_cmd = emit_remote_command(tree, envs, args.box, seed)
    say(f"$ {SSH} {args.box} <emits in {tree}>")
    log = t.logs / f"certify-emit-{args.box}.log"
    p = subprocess.run([SSH, args.box, remote_cmd], capture_output=True, text=True)
    log.write_text(p.stdout + p.stderr)
    cache_seed = seed_run if seed_run and f"== cache seed {seed_run}" in p.stdout.splitlines() else None
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
              "certify_id": rec.get("certify_id"), "wall": wall, "cache_seed": cache_seed}
    t.dir.mkdir(parents=True, exist_ok=True)
    box_record_path(t).write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    st = t.load()
    st["box_wall"] = wall
    st["box_run"] = run
    st["cache_seed"] = cache_seed
    t.save(st)
    say(f"certify recorded: {args.box} run {run} at {record['sha'][:9]}; wall install {wall['install']}s "
        f"certify {wall['certify']}s emit {wall['emit']}s "
        f"({', '.join(f'{k} {v}s' for k, v in steps.items())}) total {wall['total']}s")
    return 0


# --------------------------------------------------------------------------- gate

def _lock_keys(t: Train, cwd: Path) -> set[str] | None:
    p = subprocess.run([PY, "tools/lock_discipline_check.py", "--json"], cwd=cwd, capture_output=True, text=True)
    say(f"$ (in {cwd}) {PY} tools/lock_discipline_check.py --json  -> rc {p.returncode}")
    try:
        data = json.loads(p.stdout)
        # `new` holds key strings (lock-check-full-output, d4d8514f6) or
        # finding dicts with a 'key' (earlier checkers): accept both.
        return {e if isinstance(e, str) else e["key"] for e in data.get("new", [])}
    except (ValueError, KeyError, TypeError, AttributeError):
        say("  lock_discipline_check output not parseable: " + (p.stdout + p.stderr)[-300:])
        return None


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

    host = git(t.root, "diff", "--name-only", "origin/dev", "HEAD", "--", "host").stdout.split()
    if host:
        rec("host_load", t.run("gate-host_load", [PY, "tools/host_check.py", "--load"]))
    else:
        say("host unchanged vs origin/dev: host_check --load skipped")
        rec("host_load", 0, skipped=True)

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
        old = _lock_keys(t, wt)
    finally:
        git(t.root, "worktree", "remove", "--force", str(wt), check=False)
        shutil.rmtree(tmp, ignore_errors=True)
    new = _lock_keys(t, t.root)
    if old is None or new is None:
        rec("lock_delta", 1, error="unparseable lock_discipline_check output")
    else:
        added, gone = sorted(new - old), sorted(old - new)
        say(f"lock delta: added {added or '-'}; gone {gone or '-'}")
        if added:
            say("  WARNING: new lock-discipline keys (attributed at convergence)")
        rec("lock_delta", 1 if (added and args.strict_lock) else 0, added=added, gone=gone)

    files = git(t.root, "diff", "--name-only", "origin/dev", "HEAD").stdout.split()
    if files:
        rec("secrets", t.run("gate-secrets", [PY3, "tools/secrets_check.py", *files]))
    else:
        rec("secrets", 0, skipped=True)

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
    g.add_argument("--strict-lock", action="store_true")
    sub.add_parser("push")
    sub.add_parser("status")
    args = ap.parse_args(argv)
    try:
        t = Train(toplevel(Path.cwd()))
        return {"merge": cmd_merge, "regen": cmd_regen, "boxstep": cmd_boxstep, "certify": cmd_certify, "gate": cmd_gate,
                "push": cmd_push, "status": cmd_status}[args.cmd](t, args)
    except TrainError as e:
        say(f"train: {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main())

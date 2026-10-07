#!/usr/bin/env python3.12
"""Drive the integrator's merge train: merge, regen, gate, push.

Run from the batch tree (a git worktree on branch integrate/<name>).  The order
of regeneration is fixed and the push is conditional on gates that ran at the
exact HEAD being pushed, recorded in build/train/<branch>.json.

    train.py merge LANE@SHA [LANE@SHA ...]
    train.py regen [--cite ID ...] [--cite-from DIR] [--hbox]
    train.py gate [--strict-lock]
    train.py push
    train.py status
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

PY = os.environ.get("TRAIN_PY", "python3.12")
PY3 = os.environ.get("TRAIN_PY3", "python3")

# Conflicted files that are regenerated anyway: the train side wins.
GENERATED = (
    "planning/ledger.json",
    "planning/ledger.md",
    "planning/current.md",
    "planning/repair/STATUS.md",
    "planning/interfaces.json",
    "specs/wire-grammar.json",
)
# planning/proofs.json is NOT here: ledger.py --write regenerates only its
# event arrays, and lanes curate its rows (re-pointing a PRF row at a renamed
# keystone), so a conflict there goes back to the lane like source does.
# Tail-append files: keep both sides' lines.
UNION = ("planning/evidence-index.tsv", "planning/decisions.md")
EVIDENCE_INDEX = "planning/evidence-index.tsv"
DEDUPE = ("planning/evidence-index.tsv",)

# Files the regen step is allowed to commit (only those that exist/changed).
REGEN_OUTPUTS = (
    EVIDENCE_INDEX,
    "planning/ledger.json",
    "planning/ledger.md",
    "planning/proofs.json",
    "planning/current.md",
    "planning/repair/STATUS.md",
)
HBOX_OUTPUTS = ("planning/interfaces.json", "specs/wire-grammar.json")

HBOX_CMD = (
    "python3 tools/interface_emit.py --write && python3 tools/interface_emit.py --check && "
    "python3 tools/protocol_emit.py --wire --write && python3 tools/protocol_emit.py --wire --check && "
    "python3 tools/extract/world.py --check && python3 tools/build_lists_check.py && "
    "python3 tools/host_check.py --read && python3 tools/host_check.py --world"
)

GATES = ("ancestor", "ledger", "current_view", "host_load", "lock_delta", "secrets")


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
    if path in DEDUPE:
        seen: set[str] = set()
        keep = []
        for line in merged.splitlines(keepends=True):
            if line in seen:
                continue
            seen.add(line)
            keep.append(line)
        merged = "".join(keep)
    (t.root / path).write_text(merged)
    git(t.root, "add", "--", path)


def _comm_23_missing(root: Path, path: str) -> list[str]:
    """Lines of origin/dev:path (sorted) absent from the working file (comm -23)."""
    ref = git(root, "show", f"origin/dev:{path}", check=False)
    if ref.returncode != 0:
        return []
    have = sorted((root / path).read_text().splitlines())
    want = sorted(ref.stdout.splitlines())
    i = 0
    missing = []
    for w in want:
        while i < len(have) and have[i] < w:
            i += 1
        if i < len(have) and have[i] == w:
            i += 1
        else:
            missing.append(w)
    return missing


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
    if (t.root / EVIDENCE_INDEX).exists():
        missing = _comm_23_missing(t.root, EVIDENCE_INDEX)
        if missing:
            git(t.root, "merge", "--abort", check=False)
            entry.update(status="conflict", files=[EVIDENCE_INDEX])
            say(f"  lane {name}: evidence-index lost {len(missing)} origin/dev line(s); merge aborted")
            t.save(st)
            return False
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

    # (1) cite
    for mid in args.cite or []:
        run_dir = t.root / "build" / "acl2" / mid
        if args.cite_from:
            src = Path(args.cite_from) / "build" / "acl2" / mid
            if not src.is_dir():
                say(f"cite-from: {src} missing")
                return done(f"cite-from:{mid}", 1) or 1
            say(f"$ copy {src} -> {run_dir}")
            shutil.copytree(src, run_dir, dirs_exist_ok=True)
        if not run_dir.is_dir():
            say(f"run dir {run_dir} does not exist")
            done(f"cite:{mid}", 1)
            return 1
        rc = t.run(f"cite-{mid}", [PY, "tools/evidence_manifests.py", "add", mid])
        if done(f"cite:{mid}", rc):
            return rc
    # (2)-(4)
    for step, argv in (
        ("ledger", [PY, "tools/ledger.py", "--write"]),
        ("current_view", [PY, "tools/current_view.py", "--write"]),
        ("repair", [PY, "planning/repair/repair.py", "report"]),
    ):
        rc = t.run(f"regen-{step}", argv)
        if done(step, rc):
            return rc
    # (5)
    st["regen_commits"] = st.get("regen_commits", 0) + 1
    # the label the integrator numbers trains by; the state file's own count
    # restarts with each state file, so it is only the fallback
    n = args.label or st["regen_commits"]
    cited = " ".join(args.cite or [])
    msg = f"Regenerate train {n}: ledger, current view, repair status" + (f" after citing {cited}" if cited else "")
    _commit_named(t, REGEN_OUTPUTS, msg)
    if done("commit", 0):
        return 1
    # (6)
    if args.hbox:
        argv = ["sh", "tools/remote_check.sh", "hbox", "--fetch", "planning/interfaces.json",
                "--fetch", "specs/wire-grammar.json", "--cmd", HBOX_CMD]
        rc = t.run("regen-hbox", argv)
        if done("hbox", rc):
            return rc
        _commit_named(t, HBOX_OUTPUTS, f"Regenerate train {n}: interfaces and wire grammar from hbox")
        done("hbox_commit", 0)
    say("regen done at " + t.head()[:9])
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

    host = git(t.root, "diff", "--name-only", "origin/dev", "HEAD", "--", "host").stdout.split()
    if host:
        rec("host_load", t.run("gate-host_load", [PY, "tools/host_check.py", "--load"]))
    else:
        say("host unchanged vs origin/dev: host_check --load skipped")
        rec("host_load", 0, skipped=True)

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
    r.add_argument("--cite", action="append", metavar="ID")
    r.add_argument("--cite-from", metavar="DIR")
    r.add_argument("--hbox", action="store_true")
    r.add_argument("--label", metavar="N", help="the train number for the regen commit messages")
    g = sub.add_parser("gate")
    g.add_argument("--strict-lock", action="store_true")
    sub.add_parser("push")
    sub.add_parser("status")
    args = ap.parse_args(argv)
    try:
        t = Train(toplevel(Path.cwd()))
        return {"merge": cmd_merge, "regen": cmd_regen, "gate": cmd_gate,
                "push": cmd_push, "status": cmd_status}[args.cmd](t, args)
    except TrainError as e:
        say(f"train: {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main())

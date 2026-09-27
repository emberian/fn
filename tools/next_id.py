#!/usr/bin/env python3
"""Identifiers: what is taken everywhere, and a shared ledger that hands them out.

    python3 tools/next_id.py                       # next free of every kind, and why
    python3 tools/next_id.py claim PRF --lane NAME --note "what it is" [--count N]
    python3 tools/next_id.py claims [--lane NAME] [--kind PRF]
    python3 tools/next_id.py check [--base origin/dev] [--lane NAME]
    python3 tools/next_id.py backfill --since 2026-09-27T00:00:00Z [--dry-run]

Nearly every merge on 2026-09-27 renumbered an id.  The old tool read this
worktree's registries only, so its answer was as fresh as the lane's last
merge, and the second lane to reach for a number took the same one (four
lanes on PRF-035..040 in one evening, 2026-09-21; the board's CLAIM line
caught it at merge, never at allocation).  Now:

* **Taken** is everything any lane can see: this tree's registries and text,
  the lines every unmerged branch (lane/*, batch/*, dev, origin/dev, touched
  in the last --days, default 3) added, the uncommitted edits and
  LANEDUMP.md of every recently touched worktree under build/lanes/, the
  coordinator's LANEDUMP-*.md, and the claims ledger.  A kind is D (the
  decisions.md headings), PRF, SCN, PKT, or a requirement prefix
  (planning/requirements.json: STO, NNT, HST, ...).  A number is taken when
  it appears as KIND-N in any of those (PKT ids live in prose, so prose
  counts); the next free is one past the largest, so a stray mention costs
  a number and never a collision.
* **claim** appends to the ledger, build/coordinator/id-claims.jsonl in the
  main checkout (the `git --git-common-dir`'s tree, so every worktree
  finds the same file; FN_ID_CLAIMS names another), under an exclusive
  flock, one JSON row per id: {"id", "kind", "lane", "note", "at", "host",
  "tree", "source": "claim"}.  The number is one past the largest taken
  anywhere or claimed, decided inside the lock, so two lanes claiming at
  once get two numbers.
* **From a box** (hbox, persvati: their trees are rsync copies with no
  ledger), `claim` runs itself on the laptop over ssh when FN_ID_CLAIMS_SSH
  names it (`user@host` or `user@host:/path/to/fn`); otherwise it refuses
  and prints the laptop command.  A lane's agent always has the laptop
  shell, so claiming there is the default.
* **check** lists the ids this tree adds against --base (registry rows,
  decision headings, and PKT/other numbers above the base's largest): each
  is claimed by this lane (ok), claimed by another (COLLISION, exit 1) or
  unclaimed (UNCLAIMED, exit 3).  tools/merge_registry.py consults the same
  ledger: a registry row the merge adds with no claim is named, and an id
  collision names who claimed the number.
* **backfill** records every id numbered above the largest on origin/dev at
  --since and taken anywhere now, attributed to the lane its source names
  (source "backfill"); ids already in the ledger are skipped.

A decision's sub-ids (D14-a, D14-b) do not consume a number; the base does.
"""
from __future__ import annotations

import argparse
import collections
import concurrent.futures
import contextlib
import datetime as dt
import fcntl
import json
import os
from pathlib import Path
import re
import shlex
import socket
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
REGISTRIES = (("planning/proofs.json", "proofs"),
              ("planning/requirements.json", "requirements"),
              ("tests/scenarios/catalog.json", "scenarios"))
DECISIONS = "planning/decisions.md"
FIXED_KINDS = ("PRF", "SCN", "PKT")
# The text of a numbered id of a hyphenated kind.  Three or more digits: a
# kind's ids are zero-padded to three, and "PRF-1" in prose is not an id.
TEXT_ID = re.compile(r"(?<![A-Za-z0-9-])([A-Z]{3})-(\d{3,})(?![0-9])")
# decisions.md: every D-number in it is a decision or its sub-id (D14-a).
DECISION_HEAD = re.compile(r"(?<![A-Za-z0-9])D(\d+)(?![0-9])")
DEFAULT_DAYS = 3
# Measurement data under planning/evidence (JSON transcripts, digests) is
# not where ids are taken, and it is most of the bytes; its prose is read.
EVIDENCE_DATA = ":(exclude,glob)planning/evidence/**/*.json"
LAPTOP_TREE = "/Users/ember/dev/fn"


class Refused(Exception):
    pass


def git(*args: str, cwd: Path | None = None, check: bool = False) -> str:
    done = subprocess.run(["git", *args], cwd=cwd or ROOT, capture_output=True, text=True,
                          errors="replace")
    if check and done.returncode != 0:
        raise Refused(f"git {' '.join(args)}: {done.stderr.strip()}")
    return done.stdout if done.returncode == 0 else ""


def format_id(kind: str, number: int) -> str:
    return f"D{number}" if kind == "D" else f"{kind}-{number:03d}"


def parse_id(text: str) -> tuple[str, int] | None:
    match = re.fullmatch(r"D(\d+)|([A-Z]{3})-(\d+)", text.strip())
    if not match:
        return None
    if match.group(1):
        return "D", int(match.group(1))
    return match.group(2), int(match.group(3))


# --- the ledger --------------------------------------------------------------

def ledger_path(root: Path | None = None) -> Path | None:
    """The main checkout's build/coordinator/id-claims.jsonl, or FN_ID_CLAIMS."""
    root = root or ROOT
    named = os.environ.get("FN_ID_CLAIMS")
    if named:
        return Path(named).expanduser()
    common = git("rev-parse", "--path-format=absolute", "--git-common-dir", cwd=root).strip()
    if not common:
        return None
    coordinator = Path(common).parent / "build" / "coordinator"
    return coordinator / "id-claims.jsonl" if coordinator.is_dir() else None


def read_ledger(path: Path | None) -> list[dict]:
    if path is None or not path.is_file():
        return []
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        with contextlib.suppress(json.JSONDecodeError):
            row = json.loads(line)
            if isinstance(row, dict) and parse_id(str(row.get("id", ""))):
                rows.append(row)
    return rows


@contextlib.contextmanager
def ledger_lock(path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path.with_name(path.name + ".lock"), "a") as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


def append_rows(path: Path, rows: list[dict]) -> None:
    with open(path, "a", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())


def claims_by_id(rows: list[dict]) -> dict[str, dict]:
    """The first row per id (a later duplicate is a ledger defect, not a claim)."""
    first: dict[str, dict] = {}
    for row in rows:
        first.setdefault(row["id"], row)
    return first


# --- what is taken -----------------------------------------------------------

class Taken:
    """kind -> number -> the first source that shows it."""

    def __init__(self) -> None:
        self.seen: dict[str, dict[int, str]] = collections.defaultdict(dict)

    def add(self, kind: str, number: int, source: str) -> None:
        self.seen[kind].setdefault(number, source)

    def add_text(self, text: str, source: str, kinds: set[str]) -> None:
        for kind, digits in TEXT_ID.findall(text):
            if kind in kinds:
                self.add(kind, int(digits), source)

    def add_decisions(self, text: str, source: str) -> None:
        for digits in DECISION_HEAD.findall(text):
            self.add("D", int(digits), source)

    def largest(self, kind: str) -> tuple[int, str] | None:
        numbers = self.seen.get(kind)
        if not numbers:
            return None
        top = max(numbers)
        return top, numbers[top]


def requirement_kinds(root: Path | None = None) -> set[str]:
    root = root or ROOT
    try:
        rows = json.loads((root / "planning/requirements.json").read_text())["requirements"]
    except (OSError, ValueError, KeyError, TypeError):
        return set()
    return {row["id"].rpartition("-")[0] for row in rows
            if isinstance(row, dict) and "-" in str(row.get("id", ""))}


def all_kinds(root: Path | None = None) -> set[str]:
    root = root or ROOT
    return set(FIXED_KINDS) | requirement_kinds(root)


def scan_tree(taken: Taken, root: Path, kinds: set[str], label: str) -> None:
    """Every tracked file's working-tree text, and the decisions headings."""
    # One generic pattern, filtered here: an alternation of the kinds made
    # git grep five times slower (11 s against 2 s on this tree).
    out = git("grep", "-ohIE", "[A-Z]{3}-[0-9]{3,}", "--", ".", EVIDENCE_DATA, cwd=root)
    taken.add_text(out, label, kinds)
    with contextlib.suppress(OSError):
        taken.add_decisions((root / DECISIONS).read_text(errors="replace"), label)


def added_lines(diff: str) -> tuple[str, str]:
    """(every added line, the added lines of decisions.md) of a unified diff."""
    lines, decisions, current = [], [], ""
    for line in diff.splitlines():
        if line.startswith("+++ "):
            current = line[6:] if line.startswith("+++ b/") else ""
        elif line.startswith("+") and not line.startswith("+++"):
            lines.append(line[1:])
            if current == DECISIONS:
                decisions.append(line[1:])
    return "\n".join(lines), "\n".join(decisions)


def recent_refs(days: float, root: Path | None = None) -> list[str]:
    """dev, origin/dev, batch/* and lane/* refs committed to in the last DAYS
    and not merged into HEAD (a merged ref adds nothing HEAD lacks)."""
    root = root or ROOT
    cutoff = time.time() - days * 86400
    out = git("for-each-ref", "--no-merged=HEAD",
              "--format=%(committerdate:unix) %(refname:short)",
              "refs/heads/lane", "refs/heads/batch", "refs/heads/dev",
              "refs/remotes/origin/dev", "refs/remotes/origin/batch", cwd=root)
    refs = []
    for line in out.splitlines():
        stamp, _, name = line.partition(" ")
        if stamp.isdigit() and int(stamp) >= cutoff:
            refs.append(name)
    return refs


def parallel(function, items: list) -> list:
    """FUNCTION over ITEMS on a few threads (each call is one git process), in order."""
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        return list(pool.map(function, items))


def scan_refs(taken: Taken, refs: list[str], kinds: set[str],
              root: Path | None = None) -> None:
    """What each ref added since it and this tree's HEAD diverged."""
    root = root or ROOT
    diffs = parallel(lambda ref: git("diff", "--no-color", "--no-ext-diff", "-U0",
                                     f"HEAD...{ref}", "--", ".", EVIDENCE_DATA, cwd=root),
                     refs)
    for ref, diff in zip(refs, diffs):
        text, decisions = added_lines(diff)
        taken.add_text(text, f"branch {ref}", kinds)
        taken.add_decisions(decisions, f"branch {ref}")


def main_checkout(root: Path | None = None) -> Path | None:
    root = root or ROOT
    common = git("rev-parse", "--path-format=absolute", "--git-common-dir", cwd=root).strip()
    return Path(common).parent if common else None


# Where a worktree's uncommitted ids are taken: the registries and the
# decisions (a lane's prose ids are in its LANEDUMP.md, read whole).  Diffing
# five files keeps each of ~200 worktrees to milliseconds; a whole-tree
# `git diff` is ten thousand stats each (22 s for the machine).
UNCOMMITTED_PATHS = tuple(path for path, _ in REGISTRIES) + ("planning/proof-events.json",
                                                              DECISIONS)


def recently_touched(path: Path, cutoff: float) -> bool:
    for probe in (path / "LANEDUMP.md", *(path / one for one in UNCOMMITTED_PATHS)):
        with contextlib.suppress(OSError):
            if probe.stat().st_mtime >= cutoff:
                return True
    return False


def scan_worktrees(taken: Taken, days: float, kinds: set[str], root: Path | None = None) -> None:
    """Uncommitted edits and LANEDUMP.md of each recently touched lane worktree,
    and the coordinator's LANEDUMP-*.md."""
    root = root or ROOT
    main = main_checkout(root)
    if main is None:
        return
    cutoff = time.time() - days * 86400
    out = git("worktree", "list", "--porcelain", cwd=root)
    trees = [Path(line[len("worktree "):]) for line in out.splitlines()
             if line.startswith("worktree ")]
    trees = [tree for tree in trees
             if tree.resolve() != root.resolve() and recently_touched(tree, cutoff)]
    diffs = parallel(lambda tree: git("diff", "--no-color", "--no-ext-diff", "-U0", "HEAD",
                                      "--", *UNCOMMITTED_PATHS, cwd=tree), trees)
    for tree, diff in zip(trees, diffs):
        label = f"worktree {tree.name}"
        text, decisions = added_lines(diff)
        taken.add_text(text, label + " (uncommitted)", kinds)
        taken.add_decisions(decisions, label + " (uncommitted)")
        dump = tree / "LANEDUMP.md"
        with contextlib.suppress(OSError):
            if dump.stat().st_mtime >= cutoff:
                taken.add_text(dump.read_text(errors="replace"), f"{tree.name}/LANEDUMP.md",
                               kinds)
    for dump in sorted((main / "build" / "coordinator").glob("LANEDUMP-*.md")):
        with contextlib.suppress(OSError):
            if dump.stat().st_mtime >= cutoff:
                taken.add_text(dump.read_text(errors="replace"), f"coordinator/{dump.name}",
                               kinds)


def scan_ledger(taken: Taken, rows: list[dict]) -> None:
    for row in rows:
        parsed = parse_id(row["id"])
        if parsed:
            taken.add(parsed[0], parsed[1], f"claim by {row.get('lane') or '?'}")


def scan_all(days: float = DEFAULT_DAYS, local: bool = False,
             root: Path | None = None) -> tuple[Taken, set[str]]:
    root = root or ROOT
    kinds = all_kinds(root)
    taken = Taken()
    scan_tree(taken, root, kinds, "this tree")
    if not local:
        scan_refs(taken, recent_refs(days, root), kinds, root)
        scan_worktrees(taken, days, kinds, root)
    scan_ledger(taken, read_ledger(ledger_path(root)))
    return taken, kinds


def next_free(taken: Taken, kind: str) -> int:
    top = taken.largest(kind)
    return (top[0] + 1) if top else 1


# --- commands ----------------------------------------------------------------

def default_lane(root: Path | None = None) -> str | None:
    root = root or ROOT
    named = os.environ.get("FN_LANE")
    if named:
        return Path(named).name
    parts = root.resolve().parts
    if "lanes" in parts and parts.index("lanes") + 1 < len(parts):
        return parts[parts.index("lanes") + 1]
    return None


def show(args) -> int:
    started = time.monotonic()
    taken, kinds = scan_all(args.days, args.local)
    wanted = [args.kind.upper()] if args.kind else ["D", *sorted(kinds)]
    for kind in wanted:
        top = taken.largest(kind)
        why = f"largest {format_id(kind, top[0])}: {top[1]}" if top else "none taken"
        print(f"{kind:<4} next free {format_id(kind, next_free(taken, kind)):<9} ({why})")
    scope = ("this tree and the ledger" if args.local else
             f"this tree, branches and worktrees touched in {args.days:g} days, "
             "LANEDUMPs and the ledger")
    print(f"\nscanned {scope} in {time.monotonic() - started:.1f} s.  Take one with:\n"
          "  python3 tools/next_id.py claim KIND --lane NAME --note 'what it is'")
    return 0


def remote_claim(args, target: str) -> int:
    host, _, tree = target.partition(":")
    tree = tree or LAPTOP_TREE
    words = ["python3", f"{tree}/tools/next_id.py", "claim", args.kind,
             "--lane", args.lane, "--note", args.note, "--count", str(args.count),
             "--days", str(args.days), "--from-host", socket.gethostname()]
    done = subprocess.run(["ssh", "-o", "BatchMode=yes", host,
                           " ".join(shlex.quote(word) for word in words)],
                          capture_output=True, text=True)
    sys.stdout.write(done.stdout)
    sys.stderr.write(done.stderr)
    return done.returncode


def claim(args) -> int:
    kind = args.kind.upper()
    lane = args.lane or default_lane()
    if not lane:
        raise Refused("claim needs --lane NAME (or FN_LANE, or a build/lanes/NAME tree)")
    args.lane = lane
    if not args.note.strip():
        raise Refused("claim needs --note: one line saying what the id is for")
    if args.count < 1:
        raise Refused("--count takes a positive number")
    path = ledger_path()
    if path is None:
        target = os.environ.get("FN_ID_CLAIMS_SSH")
        if target:
            return remote_claim(args, target)
        raise Refused(
            "no claims ledger here (not a git worktree of the main checkout, and "
            "FN_ID_CLAIMS is unset).  Claim from the laptop, in your lane's worktree:\n"
            f"  python3 tools/next_id.py claim {kind} --lane {lane} --note "
            f"{shlex.quote(args.note)}" + (f" --count {args.count}" if args.count > 1 else "")
            + "\nor set FN_ID_CLAIMS_SSH=user@laptop[:/path/to/fn] to claim over ssh.")
    taken, kinds = scan_all(args.days)
    if kind != "D" and kind not in kinds:
        raise Refused(f"unknown kind {kind}: D, {', '.join(sorted(kinds))}")
    with ledger_lock(path):
        rows = read_ledger(path)
        scan_ledger(taken, rows)
        start = next_free(taken, kind)
        now = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        made = [{"id": format_id(kind, number), "kind": kind, "lane": lane,
                 "note": args.note.strip(), "at": now,
                 "host": args.from_host or socket.gethostname(),
                 "tree": str(ROOT), "source": "claim"}
                for number in range(start, start + args.count)]
        append_rows(path, made)
    for row in made:
        print(row["id"])
    print(f"claimed for {lane} in {path}", file=sys.stderr)
    return 0


def list_claims(args) -> int:
    rows = read_ledger(ledger_path())
    for row in rows:
        if args.lane and row.get("lane") != args.lane:
            continue
        if args.kind and row.get("kind") != args.kind.upper():
            continue
        print(f"{row['id']:<9} {row.get('lane') or '?':<28} {row.get('at', ''):<21} "
              + (row.get("note", "") if str(row.get("note", "")).startswith(
                  str(row.get("source", ""))) else f"{row.get('source', '')}: {row.get('note', '')}"))
    return 0


def registry_ids(text: str, key: str) -> set[str]:
    with contextlib.suppress(ValueError, TypeError, KeyError):
        document = json.loads(text)
        rows = document[key] if isinstance(document, dict) else document
        return {row["id"] for row in rows if isinstance(row, dict) and "id" in row}
    return set()


def added_ids(base: str, root: Path | None = None) -> tuple[list[str], str]:
    """The ids this tree (committed and not) adds against BASE's merge-base."""
    root = root or ROOT
    merge_base = git("merge-base", "HEAD", base, cwd=root).strip()
    if not merge_base:
        raise Refused(f"no merge base between HEAD and {base}")
    found: list[str] = []
    for path, key in REGISTRIES:
        before = registry_ids(git("show", f"{merge_base}:{path}", cwd=root), key)
        with contextlib.suppress(OSError):
            now = registry_ids((root / path).read_text(), key)
            found += sorted(now - before)
    old_decisions = set(DECISION_HEAD.findall(git("show", f"{merge_base}:{DECISIONS}",
                                                  cwd=root)))
    with contextlib.suppress(OSError):
        for digits in DECISION_HEAD.findall((root / DECISIONS).read_text()):
            if digits not in old_decisions:
                found.append(f"D{int(digits)}")
    # PKT ids live in prose: the numbers above the base's largest.
    base_taken = Taken()
    base_taken.add_text(git("grep", "-ohIE", "PKT-[0-9]{3,}", merge_base, "--", ".",
                            cwd=root), "base", {"PKT"})
    base_top = (base_taken.largest("PKT") or (0, ""))[0]
    diff = git("diff", "--no-color", "-U0", merge_base, "--", ".", EVIDENCE_DATA, cwd=root)
    text, _ = added_lines(diff)
    here = Taken()
    here.add_text(text, "diff", {"PKT"})
    found += [format_id("PKT", number) for number in sorted(here.seen.get("PKT", {}))
              if number > base_top]
    unique: list[str] = []
    for ident in found:
        if ident not in unique:
            unique.append(ident)
    return unique, merge_base


def check(args) -> int:
    lane = args.lane or default_lane()
    ids, merge_base = added_ids(args.base)
    claims = claims_by_id(read_ledger(ledger_path()))
    collisions = unclaimed = 0
    for ident in ids:
        row = claims.get(ident)
        if row is None:
            unclaimed += 1
            print(f"UNCLAIMED {ident}: no row in the claims ledger "
                  f"(python3 tools/next_id.py claim {parse_id(ident)[0]} --lane {lane or 'NAME'}"
                  " --note ... takes a free one; renumber to it)")
        elif lane and row.get("lane") != lane:
            collisions += 1
            print(f"COLLISION {ident}: claimed by {row.get('lane')} at {row.get('at')} "
                  f"({row.get('note')}); renumber this lane's use")
        else:
            print(f"ok        {ident}: claimed by {row.get('lane')} ({row.get('note')})")
    print(f"{len(ids)} id(s) added against {args.base} (merge base {merge_base[:12]}): "
          f"{collisions} collision(s), {unclaimed} unclaimed")
    return 1 if collisions else 3 if unclaimed else 0


def lane_of(source: str, commit_lane: str | None = None) -> str:
    if source.startswith("branch "):
        ref = source.split(" ", 1)[1]
        for prefix in ("origin/", "lane/"):
            if ref.startswith(prefix):
                ref = ref[len(prefix):]
        return commit_lane or ref
    if source.startswith("worktree "):
        return source.split(" ")[1]
    if source.endswith("/LANEDUMP.md"):
        return source.split("/")[0]
    if source.startswith("coordinator/LANEDUMP-"):
        return source[len("coordinator/LANEDUMP-"):-len(".md")]
    return commit_lane or "unattributed"


def first_commits(ref: str, since: str, kinds: set[str]) -> dict[str, str]:
    """id -> the first commit on REF since SINCE whose diff added it (one log pass)."""
    out = git("log", "--reverse", "--no-merges", "--format=FNCOMMIT %H", "-p", "-U0",
              "--no-color", f"--since={since}", ref, "--", ".", EVIDENCE_DATA)
    first: dict[str, str] = {}
    commit = ""
    for line in out.splitlines():
        if line.startswith("FNCOMMIT "):
            commit = line.split()[1]
        elif line.startswith("+") and not line.startswith("+++"):
            for kind, digits in TEXT_ID.findall(line):
                if kind in kinds:
                    first.setdefault(format_id(kind, int(digits)), commit)
            for digits in DECISION_HEAD.findall(line):
                first.setdefault(format_id("D", int(digits)), commit)
    return first


def lanes_of_commits(commits: set[str]) -> dict[str, str]:
    """commit -> the lane/* branch name-rev finds for it (the nearest containing one)."""
    if not commits:
        return {}
    done = subprocess.run(["git", "name-rev", "--name-only", "--refs=lane/*", "--stdin"],
                          cwd=ROOT, input="\n".join(sorted(commits)) + "\n",
                          capture_output=True, text=True, errors="replace")
    found = {}
    for commit, name in zip(sorted(commits), done.stdout.splitlines()):
        name = re.sub(r"[~^].*$", "", name.strip())
        if name.startswith("lane/"):
            found[commit] = name[len("lane/"):]
    return found


def backfill(args) -> int:
    path = ledger_path()
    if path is None:
        raise Refused("no claims ledger here; run backfill in a worktree of the main checkout")
    base_commit = git("rev-list", "-1", f"--before={args.since}", args.base).strip()
    if not base_commit:
        raise Refused(f"no commit on {args.base} before {args.since}")
    kinds = all_kinds()
    before = Taken()
    before.add_text(git("grep", "-ohIE", "[A-Z]{3}-[0-9]{3,}",
                        base_commit, "--", ".", EVIDENCE_DATA),
                    "base", kinds)
    before.add_decisions(git("show", f"{base_commit}:{DECISIONS}"), "base")
    taken, _ = scan_all(args.days)
    existing = claims_by_id(read_ledger(path))
    now = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    wanted: list[tuple[str, str, int]] = []
    for kind in ["D", *sorted(kinds)]:
        floor = (before.largest(kind) or (0, ""))[0]
        for number in sorted(n for n in taken.seen.get(kind, {}) if n > floor):
            if format_id(kind, number) not in existing:
                wanted.append((format_id(kind, number), kind, number))
    # One log pass per ref the ids were seen on, for the commit that added each.
    refs = {"HEAD"}
    for _, kind, number in wanted:
        source = taken.seen[kind][number]
        if source.startswith("branch "):
            refs.add(source.split(" ", 1)[1])
    firsts = {ref: first_commits(ref, args.since, kinds) for ref in sorted(refs)}
    commit_lanes = lanes_of_commits({commit for first in firsts.values()
                                     for commit in first.values()})
    rows = []
    for ident, kind, number in wanted:
        source = taken.seen[kind][number]
        ref = source.split(" ", 1)[1] if source.startswith("branch ") else "HEAD"
        commit = firsts.get(ref, {}).get(ident) if source.startswith(("branch ", "this tree")) \
            else None
        commit_lane = commit_lanes.get(commit) if commit else None
        rows.append({"id": ident, "kind": kind, "lane": lane_of(source, commit_lane),
                     "note": f"backfill: taken before the ledger; first seen in {source}"
                             + (f", commit {commit[:12]}" if commit else ""),
                     "at": now, "host": socket.gethostname(), "tree": str(ROOT),
                     "source": "backfill"})
    for row in rows:
        print(f"{row['id']:<9} {row['lane']:<28} {row['note']}")
    print(f"{len(rows)} id(s) above {args.base}'s largest at {args.since} "
          f"({base_commit[:12]})" + (" (dry run: nothing written)" if args.dry_run else ""))
    if rows and not args.dry_run:
        with ledger_lock(path):
            existing = claims_by_id(read_ledger(path))
            append_rows(path, [row for row in rows if row["id"] not in existing])
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--days", type=float, default=DEFAULT_DAYS,
                        help="branches and worktrees touched in this many days count")
    parser.add_argument("--local", action="store_true",
                        help="this tree and the ledger only (fast, and stale)")
    parser.add_argument("--kind", default=None, help="one kind only")
    sub = parser.add_subparsers(dest="command")
    p = sub.add_parser("claim", help="take the next free id(s) of KIND in the ledger")
    p.add_argument("kind")
    p.add_argument("--lane", default=None)
    p.add_argument("--note", required=True)
    p.add_argument("--count", type=int, default=1)
    p.add_argument("--days", type=float, default=DEFAULT_DAYS)
    p.add_argument("--from-host", default=None, help=argparse.SUPPRESS)
    p.set_defaults(run=claim)
    p = sub.add_parser("claims", help="the ledger's rows")
    p.add_argument("--lane", default=None)
    p.add_argument("--kind", default=None)
    p.set_defaults(run=list_claims)
    p = sub.add_parser("check", help="this tree's new ids against the ledger")
    p.add_argument("--base", default="origin/dev")
    p.add_argument("--lane", default=None)
    p.set_defaults(run=check)
    p = sub.add_parser("backfill", help="record ids taken before the ledger existed")
    p.add_argument("--since", required=True, help="ISO time; ids above the base's largest then")
    p.add_argument("--base", default="origin/dev")
    p.add_argument("--days", type=float, default=DEFAULT_DAYS)
    p.add_argument("--dry-run", action="store_true")
    p.set_defaults(run=backfill)
    args = parser.parse_args(argv)
    try:
        return args.run(args) if getattr(args, "run", None) else show(args)
    except Refused as refusal:
        print(f"next_id: {refusal}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())

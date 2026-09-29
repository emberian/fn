#!/usr/bin/env python3
"""Fetch named branches from origin, one fetch at a time per repository.

    python3 tools/lane_fetch.py                    # origin/dev
    python3 tools/lane_fetch.py dev lane/join-f2-midx
    python3 tools/lane_fetch.py --clear-stale dev  # remove a stale ref lock, retry once

Every lane worktree shares one repository.  A bare `git fetch origin` updates
every remote ref (hundreds of lane branches), and ten lanes doing it at once
race on the ref locks; an interrupted one leaves
`refs/remotes/origin/lane/X.lock` behind, and from then on every bare fetch in
every worktree fails on it (online-reclaim-4/5/6: "cannot lock ref
refs/remotes/origin/lane/closure-theorems"; `git fetch origin dev` worked).

THE REVERT CHECK (obstructions-8 item 69).  A merge of dev can carry a
runner's REVERT of the lane's own work: correctness-remainder-8 took BC's six
reverts through a merge and silently lost what they undid.  After a fetch of
dev this prints every revert commit the merge `git merge origin/dev` would
bring in (subject "Revert ...", in HEAD..origin/dev) and, for each, whether
it undoes this lane's work: the commit it names ("This reverts commit SHA"),
or for a reverted merge its second parent, lies on HEAD's first-parent chain
(the lane's own commits), or its subject names the lane's branch.
`--merge` then runs the merge, and REFUSES (exit 4) while such a revert is
incoming unless --allow-revert; the ordinary answer is to ask the runner to
revert the revert, or to re-apply the work on top after the merge.

    python3 tools/lane_fetch.py --merge                # fetch dev, check, merge
    python3 tools/lane_fetch.py --merge --allow-revert # merge although it reverts ours

So this fetches only the branches named, each into its own
`refs/remotes/origin/B`, holding an exclusive lock in the repository's common
directory so fetches from different worktrees queue instead of racing.  A
failure that names a ref lock prints the lock file, its age, and the command
that removes it; `--clear-stale` removes a lock file older than
--stale-seconds (default 300) -- safe under this tool's own lock, since no
other fetch through it is running -- and retries once.
"""
from __future__ import annotations

import argparse
import fcntl
from pathlib import Path
import re
import subprocess
import sys
import time

LOCKED = re.compile(r"Unable to create '([^']+\.lock)': File exists|"
                    r"cannot lock ref '([^']+)'")


def git(args: list[str], cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True)


def common_dir(cwd: Path) -> Path:
    done = git(["rev-parse", "--git-common-dir"], cwd)
    if done.returncode != 0:
        raise SystemExit(f"lane_fetch: not a git worktree: {cwd}")
    path = Path(done.stdout.strip())
    return path if path.is_absolute() else (cwd / path).resolve()


def lock_files(stderr: str, common: Path) -> list[Path]:
    """The ref lock files a failed fetch names."""
    found = []
    for match in LOCKED.finditer(stderr):
        if match.group(1):
            path = Path(match.group(1))
        else:
            path = common / (match.group(2) + ".lock")
        if path not in found:
            found.append(path)
    return found


def fetch(branches: list[str], cwd: Path, clear_stale: bool = False,
          stale_seconds: int = 300, now=time.time) -> int:
    common = common_dir(cwd)
    specs = [f"+refs/heads/{b}:refs/remotes/origin/{b}" for b in branches]
    with open(common / "fn-lane-fetch.lock", "a") as holder:
        fcntl.flock(holder, fcntl.LOCK_EX)
        for attempt in (0, 1):
            done = git(["fetch", "origin", *specs], cwd)
            if done.returncode == 0:
                sys.stderr.write(done.stderr)
                print("lane_fetch: fetched " + ", ".join(f"origin/{b}" for b in branches))
                return 0
            locks = [path for path in lock_files(done.stderr, common) if path.exists()]
            if not locks:
                sys.stderr.write(done.stderr)
                print(f"lane_fetch: git fetch exited {done.returncode}", file=sys.stderr)
                return done.returncode
            stale = [p for p in locks if now() - p.stat().st_mtime >= stale_seconds]
            for path in locks:
                age = int(now() - path.stat().st_mtime)
                print(f"lane_fetch: ref lock {path} (age {age}s) blocks the fetch; "
                      + ("stale: " if path in stale else "recent (a fetch may be running): ")
                      + f"remove it with `rm {path}` or rerun with --clear-stale",
                      file=sys.stderr)
            if not clear_stale or attempt or not stale:
                return done.returncode
            for path in stale:
                path.unlink(missing_ok=True)
                print(f"lane_fetch: removed stale {path}; retrying", file=sys.stderr)
    return 1


REVERT_SUBJECT = re.compile(r"^Revert\b")
REVERTS_COMMIT = re.compile(r"This reverts commit ([0-9a-f]{7,40})")


def _out(args: list[str], cwd: Path) -> str:
    done = git(args, cwd)
    return done.stdout if done.returncode == 0 else ""


def incoming_reverts(incoming: str, cwd: Path, branch: str | None = None) -> list[dict]:
    """Each revert commit in HEAD..INCOMING, oldest first: its sha, subject,
    the commit it reverts, and whether that is this lane's work (on HEAD's
    first-parent chain, or its subject names BRANCH)."""
    branch = branch or _out(["branch", "--show-current"], cwd).strip() or None
    log = _out(["log", "--reverse", "--format=%H%x00%s%x00%b%x01", f"HEAD..{incoming}"], cwd)
    ours = set(_out(["rev-list", "--first-parent", "HEAD"], cwd).split())
    found = []
    for record in log.split("\x01"):
        parts = record.strip("\n").split("\x00")
        if len(parts) < 3 or not REVERT_SUBJECT.match(parts[1]):
            continue
        sha, subject, body = parts
        named = REVERTS_COMMIT.search(body)
        target = _out(["rev-parse", "--verify", "-q", named.group(1) + "^{commit}"],
                      cwd).strip() if named else ""
        parents = _out(["rev-list", "--parents", "-n", "1", target], cwd).split() if target else []
        work = parents[2] if len(parents) > 2 else target  # a merge: what it merged
        target_subject = _out(["log", "-1", "--format=%s", target], cwd).strip() if target else ""
        owned = bool(work and work in ours) or bool(
            branch and re.search(r"(?<![\w/-])" + re.escape(branch) + r"(?![\w-])",
                                 subject + "\n" + target_subject))
        found.append({"sha": sha, "subject": subject, "reverts": target,
                      "reverts_subject": target_subject, "ours": owned})
    return found


def revert_report(reverts: list[dict], incoming: str) -> list[str]:
    if not reverts:
        return [f"lane_fetch: no revert commit in HEAD..{incoming}"]
    lines = [f"lane_fetch: {len(reverts)} revert commit(s) in HEAD..{incoming}:"]
    for r in reverts:
        lines.append("  {} {}{}".format(r["sha"][:10], r["subject"],
                                        "  <-- REVERTS THIS LANE'S WORK" if r["ours"] else ""))
    return lines


def merge(incoming: str, cwd: Path, allow_revert: bool) -> int:
    reverts = incoming_reverts(incoming, cwd)
    for line in revert_report(reverts, incoming):
        print(line)
    ours = [r for r in reverts if r["ours"]]
    if ours and not allow_revert:
        print(f"lane_fetch: refusing to merge {incoming}: it would apply {len(ours)} revert(s) "
              "of this lane's own work (above).  Ask the runner to revert the revert, or "
              "merge with --allow-revert and re-apply the work on top.", file=sys.stderr)
        return 4
    done = git(["merge", "--no-gpg-sign", "--no-edit", incoming], cwd)
    sys.stdout.write(done.stdout)
    sys.stderr.write(done.stderr)
    return done.returncode


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("branches", nargs="*", default=["dev"])
    parser.add_argument("--clear-stale", action="store_true")
    parser.add_argument("--stale-seconds", type=int, default=300)
    parser.add_argument("--merge", action="store_true",
                        help="then merge origin/<first branch> into HEAD, refusing an "
                             "incoming revert of this lane's work")
    parser.add_argument("--allow-revert", action="store_true",
                        help="with --merge: merge although it reverts this lane's work")
    args = parser.parse_args(argv)
    for branch in args.branches:
        if not re.fullmatch(r"[A-Za-z0-9._/-]+", branch) or branch.startswith("-"):
            parser.error(f"not a branch name: {branch!r}")
    branches = args.branches or ["dev"]
    code = fetch(branches, Path.cwd(), args.clear_stale, args.stale_seconds)
    if code:
        return code
    incoming = f"origin/{branches[0]}"
    if args.merge:
        return merge(incoming, Path.cwd(), args.allow_revert)
    if branches[0] == "dev":
        for line in revert_report(incoming_reverts(incoming, Path.cwd()), incoming):
            print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())

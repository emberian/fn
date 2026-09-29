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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("branches", nargs="*", default=["dev"])
    parser.add_argument("--clear-stale", action="store_true")
    parser.add_argument("--stale-seconds", type=int, default=300)
    args = parser.parse_args(argv)
    for branch in args.branches:
        if not re.fullmatch(r"[A-Za-z0-9._/-]+", branch) or branch.startswith("-"):
            parser.error(f"not a branch name: {branch!r}")
    return fetch(args.branches or ["dev"], Path.cwd(), args.clear_stale, args.stale_seconds)


if __name__ == "__main__":
    sys.exit(main())

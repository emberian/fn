#!/usr/bin/env python3
"""Refuse a tracked LANEDUMP.md anywhere in the tree (P4, 2026-10-06).

Lane continuation notes are lane scratch: they live untracked at the lane
root, and the coordinator's copy lives in build/coordinator/lanedumps/<lane>.md
(whose first section is a continuation capped at 150 lines).  A tracked file
named LANEDUMP.md (any directory, any case) is a failure; so is an unreadable
git index.  Exit 0 clean, 1 on a tracked LANEDUMP.md or git failure.
"""
import subprocess
import sys


def tracked(root="."):
    p = subprocess.run(["git", "-C", root, "ls-files", "-z"], capture_output=True)
    if p.returncode:
        raise RuntimeError(p.stderr.decode(errors="replace").strip() or "git ls-files failed")
    return [f for f in p.stdout.decode().split("\0") if f]


def offenders(files):
    return [f for f in files if f.rsplit("/", 1)[-1].lower() == "lanedump.md"]


def main(argv=None):
    root = (argv or sys.argv[1:] or ["."])[0]
    try:
        bad = offenders(tracked(root))
    except (RuntimeError, OSError) as e:
        print(f"lanedump_check: cannot list tracked files: {e}", file=sys.stderr)
        return 1
    for f in bad:
        print(f"lanedump_check: tracked {f}; keep it untracked and put the lane's "
              "continuation in build/coordinator/lanedumps/<lane>.md", file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

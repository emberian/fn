#!/bin/sh
# Re-run the carrier move from the committed tree (worktree root as cwd).
X=$(dirname "$0")
git checkout -- $(git diff --name-only) 2>/dev/null; rm -f books/owner-carrier.lisp
python3 $X/run.py --write | cut -c1-400 && python3 $X/hand.py

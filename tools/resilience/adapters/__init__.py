"""Backend adapters: each turns a scenario into a run on one backend and
records the three histories; the verdict is always the checker's."""

import os as _os
import subprocess as _subprocess


def source_revision(root) -> str:
    """The commit a run's tree is: FN_NATIVE_SOURCE (`commit SHA` or
    `worktree ID`, exported by tools/hbox_native.sh into a shipped box tree,
    which has no git), else git's HEAD at ROOT."""
    named = _os.environ.get("FN_NATIVE_SOURCE", "").split()
    if len(named) == 2 and named[0] in ("commit", "worktree"):
        return named[1]
    return _subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()

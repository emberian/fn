#!/usr/bin/env python3
"""A machine-wide cap on concurrent ACL2 processes.

ACL2 certification is memory-bound, not CPU-bound: a laptop that starts one
ACL2 per requested book swaps rather than finishes, and the box that dies is
the one every lane shares.  Every fn tool that spawns ACL2 takes a slot from
this pool first and holds it for the lifetime of that process.

A slot is an exclusive ``flock`` on a file under the slot directory.  The lock
belongs to the open file description, so it is released when the holder exits
for any reason, including a kill: a crashed run leaks no slot.  The pool is
per-machine, not per-worktree, so lanes running in different worktrees and
different shells still share one cap.

``FN_ACL2_SLOTS`` sets the pool size (default 8 on darwin, 16 elsewhere);
``FN_ACL2_SLOT_DIR`` relocates the lock files, which tests use to get a private
pool.  Waiting is the point: a tool blocks until a slot frees rather than
starting an ACL2 the machine cannot afford, and logs that it is waiting once a
minute so a wait is never mistaken for a hang.
"""

from __future__ import annotations

import contextlib
from dataclasses import dataclass
import fcntl
import os
from pathlib import Path
import sys
import time
from typing import Callable, Iterator


# 2026-09-23: this Mac has 12 cores and 96 GB, and six lanes' sessions
# starved on four slots (an eleven-minute wait to start one); seven live
# sessions used 5.2 GB between them.  Eight leaves four cores for the rest.
DEFAULT_SLOTS = {"darwin": 8}
FALLBACK_SLOTS = 16
DEFAULT_SLOT_DIR = "~/.cache/fn-acl2-slots"
REPORT_SECONDS = 60.0
POLL_SECONDS = 0.05


@dataclass
class Slot:
    """The acquired slot: which one, how long the caller waited, pool size."""

    index: int
    seconds: float
    slots: int


def slot_count() -> int:
    """The pool size.  An unparsable or non-positive setting falls back."""
    default = DEFAULT_SLOTS.get(sys.platform, FALLBACK_SLOTS)
    try:
        configured = int(os.environ.get("FN_ACL2_SLOTS", default))
    except ValueError:
        return default
    return configured if configured > 0 else default


def slot_directory() -> Path:
    return Path(os.environ.get("FN_ACL2_SLOT_DIR", DEFAULT_SLOT_DIR)).expanduser()


def default_log(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


@contextlib.contextmanager
def slot(
    label: str = "acl2",
    log: Callable[[str], None] | None = None,
    poll: float = POLL_SECONDS,
    report_every: float = REPORT_SECONDS,
) -> Iterator[Slot]:
    """Hold one ACL2 slot for the duration of the block.

    Acquisition scans the pool in order, so slots fill low-index first and the
    machine's ACL2 processes stay identifiable by which lock file they hold.
    """
    count = slot_count()
    directory = slot_directory()
    directory.mkdir(parents=True, exist_ok=True)
    paths = [directory / f"slot-{index:03d}" for index in range(count)]
    report = log or default_log
    started = time.monotonic()
    reported = 0.0
    handle: int | None = None
    index = -1
    while handle is None:
        for candidate, path in enumerate(paths):
            descriptor = os.open(path, os.O_RDWR | os.O_CREAT, 0o644)
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError:
                os.close(descriptor)
                continue
            handle, index = descriptor, candidate
            break
        if handle is None:
            waited = time.monotonic() - started
            if waited - reported >= report_every:
                reported = waited
                report(f"fn: waiting for one of {count} ACL2 slots "
                       f"({label}): {int(waited)}s")
            time.sleep(poll)
    waited = round(time.monotonic() - started, 3)
    try:
        os.ftruncate(handle, 0)
        os.pwrite(handle, f"{os.getpid()} {label}\n".encode(), 0)
    except OSError:  # pragma: no cover - diagnostics only
        pass
    try:
        yield Slot(index=index, seconds=waited, slots=count)
    finally:
        fcntl.flock(handle, fcntl.LOCK_UN)
        os.close(handle)

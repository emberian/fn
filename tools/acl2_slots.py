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

``FN_ACL2_SLOTS`` sets the pool size (default 6 on darwin, 16 elsewhere);
``FN_ACL2_DYNAMIC_SPACE_MB`` sets the heap cap every pooled ACL2 gets (default
8,000 on darwin, none elsewhere: the farm launchers carry their own);
``FN_ACL2_SLOT_DIR`` relocates the lock files, which tests use to get a private
pool.  Waiting is the point: a tool blocks until a slot frees rather than
starting an ACL2 the machine cannot afford, and logs that it is waiting once a
minute, naming the holders (the "PID LABEL" each holder wrote into its slot
file), so a wait is never mistaken for a hang and never anonymous.

``FN_ACL2_SLOT_WAIT`` (or a caller's ``wait_seconds``; ``tools/acl2
--wait-seconds``) bounds the wait: past it the acquisition refuses with
``SlotWaitExpired``, whose message names every holder, instead of waiting on
15 orphan sessions for 24 minutes (PKT-346).  Unset, the wait is unbounded,
as before: the farm and the certify runner queue by design.
"""

from __future__ import annotations

import contextlib
from dataclasses import dataclass
import fcntl
import os
from pathlib import Path
import sys
import threading
import time
from typing import Callable, Iterator


# 2026-09-23: this Mac has 12 cores and 96 GB, and six lanes' sessions
# starved on four slots (an eleven-minute wait to start one); seven live
# sessions used 5.2 GB between them.  Eight left four cores for the rest.
# On 2026-09-25 the laptop hard-crashed: every ACL2 here gets SBCL's 32,000 MB
# dynamic space from the Homebrew launcher, the machine has 96 GB and no swap,
# and three lanes' local sessions (one reloading a bit-vector guard proof every
# thirty seconds) exhausted it.  The pool now caps the heap of every ACL2 it
# starts (`heap_cap_user_args`), and six slots of 8,000 MB is 48 GB, half the
# machine, with the other half for bare `acl2 <` invocations nobody pooled.
DEFAULT_SLOTS = {"darwin": 6}
DEFAULT_HEAP_MB = {"darwin": 8000}


def heap_cap_user_args() -> str | None:
    """SBCL runtime arguments that bound one ACL2's dynamic space.

    The Homebrew `saved_acl2` script splices `$SBCL_USER_ARGS` after its own
    `--dynamic-space-size 32000`, and SBCL takes the last such option, so
    exporting a smaller size caps the heap without editing the launcher.  A
    runaway proof then dies with "heap exhausted" inside its own process
    instead of hanging the machine.  `FN_ACL2_DYNAMIC_SPACE_MB` overrides;
    on the farm boxes the launchers carry their own sizes and nothing is added.
    """
    configured = os.environ.get("FN_ACL2_DYNAMIC_SPACE_MB")
    if configured:
        try:
            megabytes = int(configured)
        except ValueError:
            megabytes = 0
    else:
        megabytes = DEFAULT_HEAP_MB.get(sys.platform, 0)
    return f"--dynamic-space-size {megabytes}" if megabytes > 0 else None


def apply_heap_cap(environment: dict) -> dict:
    """Add the heap cap to an ACL2 child's environment unless one is set."""
    cap = heap_cap_user_args()
    if cap and "SBCL_USER_ARGS" not in environment:
        environment["SBCL_USER_ARGS"] = cap
    return environment
FALLBACK_SLOTS = 16
DEFAULT_SLOT_DIR = "~/.cache/fn-acl2-slots"
REPORT_SECONDS = 60.0
POLL_SECONDS = 0.05


class SlotWaitExpired(RuntimeError):
    """No slot freed within the bounded wait; the message names the holders."""


def holders(directory: Path | None = None, count: int | None = None) -> list[str]:
    """What each held slot's file says: "slot-NNN: PID LABEL".

    A slot file keeps its last holder's line after release, so only files whose
    lock is held now are read.  Probing takes the lock for an instant when it is
    free and drops it at once; it never touches a held slot.
    """
    directory = directory or slot_directory()
    count = count or slot_count()
    found = []
    for index in range(count):
        path = directory / f"slot-{index:03d}"
        try:
            descriptor = os.open(path, os.O_RDONLY)
        except OSError:
            continue
        try:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_SH | fcntl.LOCK_NB)
            except OSError:
                text = os.pread(descriptor, 512, 0).decode("utf-8", "replace").strip()
                found.append(f"{path.name}: {text or '(holder wrote nothing)'}")
            else:
                fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)
    return found


def configured_wait() -> float | None:
    """FN_ACL2_SLOT_WAIT in seconds; unset, empty or unparsable: unbounded."""
    configured = os.environ.get("FN_ACL2_SLOT_WAIT", "").strip()
    try:
        seconds = float(configured)
    except ValueError:
        return None
    return seconds if seconds >= 0 else None


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
    wait_seconds: float | None = None,
) -> Iterator[Slot]:
    """Hold one ACL2 slot for the duration of the block.

    Acquisition scans the pool in order, so slots fill low-index first and the
    machine's ACL2 processes stay identifiable by which lock file they hold.
    ``wait_seconds`` (default ``FN_ACL2_SLOT_WAIT``, else unbounded) bounds the
    wait; past it ``SlotWaitExpired`` names the holders.
    """
    if wait_seconds is None:
        wait_seconds = configured_wait()
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
            if wait_seconds is not None and waited >= wait_seconds:
                held = holders(directory, count)
                raise SlotWaitExpired(
                    f"fn: no ACL2 slot of {count} freed within {wait_seconds:g}s "
                    f"({label}); holders: " + ("; ".join(held) or "none named"))
            if waited - reported >= report_every:
                reported = waited
                held = holders(directory, count)
                report(f"fn: waiting for one of {count} ACL2 slots "
                       f"({label}): {int(waited)}s; holders: "
                       + ("; ".join(held) or "none named"))
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


# -- one slot per process tree, and the one launch path ---------------------
#
# A process takes a slot for its first live ACL2 and returns it with its last,
# publishing its pid in SLOT_HOLDER_VARIABLE while it holds it.  A child it
# starts (the tests run `tools/run_store.py` as a subprocess while holding a
# bridge) inherits that slot instead of waiting for a second one, which would
# deadlock a full pool of parents each waiting on its child.  A tree therefore
# counts once against the pool however many sessions it nests.  (Moved here
# from tools/run_store.py by harness-repair, 2026-09-25, so every launcher --
# bridges, sessions, host checks, test drivers -- shares one implementation;
# PKT-162.)
SLOT_HOLDER_VARIABLE = "FN_ACL2_SLOT_HOLDER"


class _TreeSlot:
    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.stack: contextlib.ExitStack | None = None
        self.users = 0


# One record per process, however this module was imported: the tree runs it
# both as `tools.acl2_slots` and as `acl2_slots` (tools/ on sys.path), and two
# module objects with two counters would let one release the slot the other
# still counts on.
_TREE: _TreeSlot = sys.modules.setdefault("_fn_acl2_tree_slot", _TreeSlot())  # type: ignore[assignment]


def _pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def inherited_tree_slot() -> bool:
    holder = os.environ.get(SLOT_HOLDER_VARIABLE, "")
    return holder.isdigit() and _pid_alive(int(holder))


def acquire_tree_slot(label: str) -> None:
    """Count one user of this process tree's slot, taking it if needed."""
    with _TREE.lock:
        if _TREE.users == 0 and not inherited_tree_slot():
            stack = contextlib.ExitStack()
            stack.enter_context(slot(label))
            _TREE.stack = stack
            os.environ[SLOT_HOLDER_VARIABLE] = str(os.getpid())
        _TREE.users += 1


def release_tree_slot() -> None:
    """Drop one user; the last one returns the slot to the pool."""
    with _TREE.lock:
        _TREE.users = max(0, _TREE.users - 1)
        if _TREE.users == 0 and _TREE.stack is not None:
            stack, _TREE.stack = _TREE.stack, None
            if os.environ.get(SLOT_HOLDER_VARIABLE) == str(os.getpid()):
                del os.environ[SLOT_HOLDER_VARIABLE]
            stack.close()


@contextlib.contextmanager
def tree_slot(label: str) -> Iterator[None]:
    acquire_tree_slot(label)
    try:
        yield
    finally:
        release_tree_slot()


def acl2_environment(base: dict | None = None) -> dict:
    """The environment every ACL2 fn starts gets.

    The certification settings (no user customization; content-hashed
    certificates, which is what makes them valid in another worktree; no
    inherited system-books override), so a session sees the world the book
    was certified in, and the pool's heap cap.
    """
    environment = dict(os.environ if base is None else base)
    environment["ACL2_CUSTOMIZATION"] = "NONE"
    environment["ACL2_BOOK_HASH_ALISTP"] = "NIL"
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    return apply_heap_cap(environment)


def run(argv: list, label: str, env: dict | None = None, **kwargs):
    """`subprocess.run` of an ACL2 under this tree's slot, with the environment."""
    import subprocess
    with tree_slot(label):
        return subprocess.run(argv, env=acl2_environment(env), **kwargs)


def popen(argv: list, label: str, env: dict | None = None, **kwargs):
    """`subprocess.Popen` of a long-lived ACL2 session under this tree's slot.

    The slot stays counted until the caller calls `release_tree_slot()` (a
    session's close) or the process exits; a failed start releases it here.
    """
    import subprocess
    acquire_tree_slot(label)
    try:
        return subprocess.Popen(argv, env=acl2_environment(env), **kwargs)
    except BaseException:
        release_tree_slot()
        raise


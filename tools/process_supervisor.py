#!/usr/bin/env python3
"""Bounded POSIX process-group supervision for development commands.

The direct child starts a new session, so its process group is also the task
group. A task is complete only after its leader has exited and that group is
gone. On timeout or an interrupt delivered to this supervisor, the group gets
TERM, a bounded grace period, then KILL; the direct child is reaped separately.

This is deliberately development tooling. It cannot clean a child that creates
another session/process group, and a supervisor killed with SIGKILL cannot run
its cleanup handler.
"""
from __future__ import annotations

from dataclasses import dataclass
import os
import signal
import subprocess
import threading
import time
from typing import Sequence


DEFAULT_GRACE_SECONDS = 2.0
DEFAULT_OUTPUT_TAIL_BYTES = 1024 * 1024
POLL_SECONDS = 0.02


@dataclass(frozen=True)
class CommandResult:
    returncode: int
    timed_out: bool
    cancelled_by: int | None
    output_tail: bytes
    output_truncated: bool


class CommandCancelled(BaseException):
    """Internal escape from task waiting after TERM or INT."""

    def __init__(self, signum: int):
        self.signum = signum


class _TailReader:
    """Drain a task pipe without retaining more than its final byte budget."""

    def __init__(self, stream, limit: int):
        self.limit = limit
        self.tail = bytearray()
        self.truncated = False
        self.lock = threading.Lock()
        self.thread = threading.Thread(target=self._drain, args=(stream,), daemon=True)
        self.thread.start()

    def _drain(self, stream) -> None:
        while True:
            chunk = stream.read(65536)
            if not chunk:
                return
            with self.lock:
                self.tail.extend(chunk)
                if len(self.tail) > self.limit:
                    del self.tail[:len(self.tail) - self.limit]
                    self.truncated = True

    def finish(self, grace_seconds: float) -> tuple[bytes, bool]:
        self.thread.join(timeout=grace_seconds)
        # An intentionally escaped child may keep the inherited pipe open.
        # The daemon reader stays bounded and does not turn group cleanup into
        # an unbounded supervisor wait.
        with self.lock:
            return bytes(self.tail), self.truncated or self.thread.is_alive()


def _group_alive(pgid: int) -> bool:
    """Whether the group has a live member, excluding unreaped zombies.

    ``killpg(pgid, 0)`` cannot make that distinction on macOS: it can report
    EPERM for an already-killed group retained only by a non-child zombie.
    Those zombies cannot execute or retain a task resource.  POSIX ``ps`` is
    used only for the development supervisor's bounded polling decision.
    """
    try:
        listed = subprocess.run(["ps", "-o", "stat=", "-g", str(pgid)],
                                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                timeout=1, check=False)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError("cannot inspect task process group") from error
    return any(line.lstrip()[:1] != b"Z" for line in listed.stdout.splitlines())


def _signal_group(pgid: int, signum: int) -> None:
    """Signal by saved group id, even when the direct child has already died."""
    try:
        os.killpg(pgid, signum)
    except ProcessLookupError:
        pass
    except PermissionError as error:
        # On macOS, a dead non-child can remain listed as a zombie after its
        # parent exits; it produces EPERM despite no live task member.  A live
        # member that the supervisor cannot signal is a failed cleanup.
        if _group_alive(pgid):
            raise RuntimeError("cannot signal live task process group") from error


def _wait_for_group_exit(pgid: int, deadline: float) -> bool:
    while _group_alive(pgid):
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return False
        time.sleep(min(POLL_SECONDS, remaining))
    return True


def _reap_direct_child(process: subprocess.Popen[bytes], grace_seconds: float) -> None:
    try:
        process.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired as error:
        raise RuntimeError("task leader did not reap after task-group stop") from error


def _stop_group_and_reap(process: subprocess.Popen[bytes], pgid: int,
                         grace_seconds: float) -> None:
    """Stop all inherited-group members, then reap only our direct child."""
    _signal_group(pgid, signal.SIGTERM)
    if not _wait_for_group_exit(pgid, time.monotonic() + grace_seconds):
        _signal_group(pgid, signal.SIGKILL)
        if not _wait_for_group_exit(pgid, time.monotonic() + grace_seconds):
            raise RuntimeError("task process group survived SIGKILL")
    _reap_direct_child(process, grace_seconds)


def run(command: Sequence[str], *, timeout_seconds: float,
        grace_seconds: float = DEFAULT_GRACE_SECONDS,
        output_tail_bytes: int = DEFAULT_OUTPUT_TAIL_BYTES,
        cwd: str | os.PathLike[str] | None = None,
        env: dict[str, str] | None = None) -> CommandResult:
    """Run one development task and contain its POSIX process group.

    The transcript is a bounded final tail, never an unbounded ``communicate``
    byte string. On timeout/cancellation, success means no live inherited
    group member remains and this supervisor has reaped its direct child.
    """
    if not command:
        raise ValueError("command must not be empty")
    if timeout_seconds <= 0 or grace_seconds <= 0 or output_tail_bytes <= 0:
        raise ValueError("timeout, grace, and output tail must be positive")

    process = subprocess.Popen(
        list(command), cwd=cwd, env=env, stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
    pgid = process.pid
    tail = _TailReader(process.stdout, output_tail_bytes)
    previous_handlers: dict[int, signal.Handlers] = {}
    cleaning = False

    def cancelled(signum, _frame):
        # A second TERM/INT is deliberately ignored while cleanup is in
        # progress: it must not interrupt TERM -> KILL -> direct-child reap.
        if not cleaning:
            raise CommandCancelled(signum)

    for signum in (signal.SIGTERM, signal.SIGINT):
        previous_handlers[signum] = signal.signal(signum, cancelled)
    try:
        deadline = time.monotonic() + timeout_seconds
        try:
            while process.poll() is None or _group_alive(pgid):
                if time.monotonic() >= deadline:
                    cleaning = True
                    _stop_group_and_reap(process, pgid, grace_seconds)
                    output, truncated = tail.finish(grace_seconds)
                    return CommandResult(124, True, None, output, truncated)
                time.sleep(POLL_SECONDS)
            _reap_direct_child(process, grace_seconds)
            output, truncated = tail.finish(grace_seconds)
            return CommandResult(process.returncode, False, None, output, truncated)
        except CommandCancelled as error:
            cleaning = True
            _stop_group_and_reap(process, pgid, grace_seconds)
            output, truncated = tail.finish(grace_seconds)
            return CommandResult(128 + error.signum, False, error.signum,
                                 output, truncated)
    finally:
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)

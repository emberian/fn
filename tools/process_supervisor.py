#!/usr/bin/env python3
"""Bounded POSIX process-group supervision for development commands.

The direct child starts a new session, so its process group is also the task
group.  On a timeout or an interrupt delivered to this supervisor, the group
gets TERM, a bounded grace period, then KILL, and the direct child is reaped.

This is deliberately development tooling.  It cannot clean a child that
creates another session/process group, and a supervisor killed with SIGKILL
cannot run its cleanup handler.
"""
from __future__ import annotations

from dataclasses import dataclass
import os
import signal
import subprocess
import time
from typing import Sequence


DEFAULT_GRACE_SECONDS = 2.0


@dataclass(frozen=True)
class CommandResult:
    returncode: int
    timed_out: bool
    cancelled_by: int | None
    output: bytes


class CommandCancelled(BaseException):
    """Internal escape from ``communicate`` after TERM or INT."""

    def __init__(self, signum: int):
        self.signum = signum


def _signal_group(process: subprocess.Popen[bytes], signum: int) -> None:
    """Signal the task group while it still belongs to this supervisor."""
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signum)
    except ProcessLookupError:
        # The group exited between poll and killpg.  wait below still reaps
        # our direct child if it had not been collected already.
        pass


def _reap_after_stop(process: subprocess.Popen[bytes], grace_seconds: float) -> None:
    """TERM then KILL the task group and bound both waits for the child."""
    _signal_group(process, signal.SIGTERM)
    try:
        process.wait(timeout=grace_seconds)
        return
    except subprocess.TimeoutExpired:
        pass
    _signal_group(process, signal.SIGKILL)
    # SIGKILL normally makes wait immediate.  Keep this wait bounded too: an
    # uninterruptible direct child is reported to the caller instead of making
    # a development command runner hang forever.
    try:
        process.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired as error:
        raise RuntimeError("task leader did not reap after SIGKILL") from error


def run(command: Sequence[str], *, timeout_seconds: float,
        grace_seconds: float = DEFAULT_GRACE_SECONDS,
        cwd: str | os.PathLike[str] | None = None,
        env: dict[str, str] | None = None) -> CommandResult:
    """Run one development task and contain its POSIX process group.

    ``timeout_seconds`` and ``grace_seconds`` must be positive.  Standard
    output and standard error are combined so a caller can report one bounded
    command transcript.  The returned child is always reaped unless the OS
    leaves the direct child uninterruptible even after SIGKILL.
    """
    if not command:
        raise ValueError("command must not be empty")
    if timeout_seconds <= 0 or grace_seconds <= 0:
        raise ValueError("timeout and grace must be positive")

    process = subprocess.Popen(
        list(command), cwd=cwd, env=env, stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
    previous_handlers: dict[int, signal.Handlers] = {}

    def cancelled(signum, _frame):
        raise CommandCancelled(signum)

    for signum in (signal.SIGTERM, signal.SIGINT):
        previous_handlers[signum] = signal.signal(signum, cancelled)
    try:
        try:
            output, _ = process.communicate(timeout=timeout_seconds)
            return CommandResult(process.returncode, False, None, output)
        except subprocess.TimeoutExpired as error:
            _reap_after_stop(process, grace_seconds)
            output = (error.output or b"")
            return CommandResult(124, True, None, output)
        except CommandCancelled as error:
            _reap_after_stop(process, grace_seconds)
            return CommandResult(128 + error.signum, False, error.signum, b"")
    finally:
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)


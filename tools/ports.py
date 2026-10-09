"""Loopback listener ports for the nodes that tests and tools start.

A port found by binding port 0 and closing the probe lies inside the kernel's
ephemeral range, and the kernel gives that port to the next socket that needs
one: a client's connect, another probe, a node's outgoing peer connection.  A
node configured with it then fails its bind with EADDRINUSE whenever another
socket on the box got there first (NATIVE-HARNESS-PORT-RACE: 25 failures in 11
modules of the drain image gate at c0e35e156 while the load sweep ran nodes on
the same box; L's conn-capacity cell lost restarts the same way).

`reserve()` returns a port BELOW the ephemeral range, where the kernel assigns
no port to any socket, after taking an exclusive lock on a per-port file that
it holds for the rest of the process's life.  Every caller of this module on
the box (the native suites at --jobs 4, the load sweep, the measurement tools)
therefore gets a port no other caller holds, and a crashed process releases
its locks with its descriptors.  The claim is scoped: the lock orders callers
of this module; a program that binds a fixed port in the pool by itself is
outside it.
"""
from __future__ import annotations

import errno
import fcntl
import os
import random
import socket
import stat
import subprocess
import threading
from pathlib import Path

# The pool's floor; its ceiling is the kernel's first ephemeral port.
POOL_LOW = 20000
# Linux's default first ephemeral port, when the box does not say.
DEFAULT_EPHEMERAL_LOW = 32768
ATTEMPTS = 4096

_held: dict[int, int] = {}  # port -> the descriptor holding its lock
_lock = threading.Lock()


def ephemeral_low() -> int:
    """The kernel's first ephemeral port: Linux's ip_local_port_range, the
    BSDs' and macOS's portrange.first."""
    try:
        return int(Path("/proc/sys/net/ipv4/ip_local_port_range").read_text().split()[0])
    except (OSError, ValueError, IndexError):
        pass
    for name in ("net.inet.ip.portrange.first", "net.inet.ip.portfirst"):
        try:
            out = subprocess.run(["sysctl", "-n", name], capture_output=True, text=True, timeout=10)
            if out.returncode == 0 and out.stdout.strip().isdigit():
                return int(out.stdout.strip())
        except (OSError, subprocess.SubprocessError):
            continue
    return DEFAULT_EPHEMERAL_LOW


def lock_dir() -> Path:
    """FN_PORT_LOCK_DIR, else /tmp/fn-ports-UID: one directory for every
    process of this user on the box whatever its TMPDIR, refused unless it is
    a real directory this user owns and nobody else can write."""
    path = Path(os.environ.get("FN_PORT_LOCK_DIR") or f"/tmp/fn-ports-{os.getuid()}")
    try:
        path.mkdir(mode=0o700)
    except FileExistsError:
        pass
    info = os.lstat(path)
    if (not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid()
            or info.st_mode & (stat.S_IWGRP | stat.S_IWOTH)):
        raise RuntimeError(f"{path}: not a private directory of uid {os.getuid()}; "
                           "set FN_PORT_LOCK_DIR to one")
    return path


def bindable(port: int, host: str = "127.0.0.1") -> bool:
    """Nothing holds PORT on HOST now (no listener, no socket bound to it)."""
    with socket.socket() as probe:
        try:
            probe.bind((host, port))
        except OSError as error:
            if error.errno in (errno.EADDRINUSE, errno.EACCES):
                return False
            raise
    return True


def reserve(*, low: int | None = None, high: int | None = None, rng=random) -> int:
    """A loopback port in [LOW, HIGH) (default: POOL_LOW up to the first
    ephemeral port) that no other caller of this module holds and nothing is
    bound to, locked for the rest of this process."""
    low = POOL_LOW if low is None else low
    high = ephemeral_low() if high is None else high
    if high - low < 256:
        raise RuntimeError(f"port pool [{low}, {high}) is too small; the kernel's ephemeral "
                           "range starts too low for a pool below it")
    directory = lock_dir()
    with _lock:
        for _ in range(ATTEMPTS):
            port = rng.randrange(low, high)
            if port in _held:
                continue
            fd = os.open(directory / str(port), os.O_RDWR | os.O_CREAT, 0o600)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                os.close(fd)
                continue
            if not bindable(port):
                os.close(fd)
                continue
            _held[port] = fd
            return port
    raise RuntimeError(f"no free port in [{low}, {high}) after {ATTEMPTS} attempts")

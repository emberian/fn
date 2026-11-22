"""Assertions for native nodes launched through timeout and tools/acl2."""

import signal
import subprocess


def require_launcher_sigkill(process: subprocess.Popen) -> None:
    """Require the launcher to report that its runtime died on SIGKILL."""
    # tools/acl2 exits with the child's negative wait status, which is
    # encoded as an 8-bit exit code by the OS and propagated by timeout.
    expected = (-signal.SIGKILL) & 0xff
    status = process.wait(timeout=30)
    assert status == expected, f"expected SIGKILL exit {expected}, got {status}"

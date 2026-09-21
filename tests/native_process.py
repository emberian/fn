"""Bounded cleanup for failed native-test startup diagnostics."""
import subprocess


def stop_and_diagnostics(process, timeout=10):
    """Stop before collecting pipes; an idle live server will not close stderr."""
    if process.poll() is None:
        process.terminate()
    try:
        _, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        _, stderr = process.communicate(timeout=timeout)
    return (stderr or b"")[-8192:].decode("utf-8", "replace")

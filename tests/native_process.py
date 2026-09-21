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


def wait_for_announcement(process, prefix, timeout=180, max_bytes=8192):
    """Read bounded startup lines under one deadline, including CONTROL first.

    Read the descriptor directly so select does not overlook a second line
    already buffered by Python's BufferedReader.
    """
    import os
    import select
    import time
    deadline = time.monotonic() + timeout
    buffered = b""
    observed = b""
    try:
        while len(observed) < max_bytes:
            while b"\n" in buffered:
                line, buffered = buffered.split(b"\n", 1)
                line += b"\n"
                if line.startswith(prefix):
                    return line
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not select.select([process.stdout], [], [], remaining)[0]:
                raise AssertionError("native startup deadline expired")
            chunk = os.read(process.stdout.fileno(), min(4096, max_bytes - len(observed)))
            if not chunk:
                raise AssertionError("native startup ended before announcement")
            observed += chunk
            buffered += chunk
        raise AssertionError("native startup output exceeded byte bound")
    except (AssertionError, OSError) as error:
        diagnostic = stop_and_diagnostics(process)
        raise AssertionError("{}; stdout={!r}; stderr={}".format(
            error, observed, diagnostic)) from error

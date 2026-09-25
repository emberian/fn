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


def runtime_sbcl(image):
    """The SBCL that runs IMAGE, as (executable, environment), or None.

    A raw-stub test reads host/native/*.lisp with the reader of the runtime it
    ships on: the host code names symbols (sb-bsd-sockets:sockopt-error) that
    an older system SBCL does not export.  FN_SBCL overrides; otherwise the
    runtime named by IMAGE's wrapper (a build/fn-host* script or a frozen
    image directory's runtime/sbcl); otherwise `sbcl` on PATH.
    """
    import os
    import re
    import shutil
    from pathlib import Path
    env = dict(os.environ)
    if env.get("FN_SBCL"):
        return env["FN_SBCL"], env
    image = Path(image)
    frozen = image.parent / "runtime" / "sbcl"
    if os.access(frozen, os.X_OK):
        env["SBCL_HOME"] = str(image.parent / "runtime" / "sbcl-home") + "/"
        return str(frozen), env
    try:
        wrapper = image.read_text(encoding="utf-8", errors="replace")
    except OSError:
        wrapper = ""
    runtime = re.search(r'^exec "([^"$]+)" ', wrapper, re.M)
    home = re.search(r"^export SBCL_HOME='([^']+)'", wrapper, re.M)
    if runtime and os.access(runtime.group(1), os.X_OK):
        if home:
            env["SBCL_HOME"] = home.group(1)
        return runtime.group(1), env
    found = shutil.which("sbcl")
    return (found, env) if found else None

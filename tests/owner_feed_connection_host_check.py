#!/usr/bin/env python3
"""Run the owner-feed host witness with host_check's ACL2 error discipline.

An ACL2 `ld` error from a pipe does not necessarily end the session.  The
success marker therefore lives inside the `er-progn` containing both loads,
and the transcript must show that the following top-level marker was reached
at an ACL2 logic prompt.  `tools/host_check.py` uses the same two-marker
protocol for individual host files; this runner keeps the composed witness
under that protocol.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from tools import host_check

LD_OK = "FN_OWNER_FEED_CONNECTION_HOST_LD_OK"
MARKER = "FN_OWNER_FEED_CONNECTION_HOST_LOADED"
TIMEOUT_SECONDS = 600


def driver_for(fixture: str) -> str:
    return f'''(er-progn
  (ld "host/owner-host.lisp" :ld-error-action :error)
  (ld "{fixture}" :ld-error-action :error)
  (value-triple (cw "{LD_OK} ~s0~%" "{fixture}")))
(cw "{MARKER} ~s0~%" "{fixture}")
(good-bye)
'''


def succeeded_at_logic_prompt(output: str) -> tuple[bool, str]:
    """Apply the same load/error/prompt checks as tools/host_check.py."""
    # Its parser intentionally treats any ACL2 error before LD_OK as a failed
    # load and requires the marker after LD_OK to be printed at `ACL2 !>`.
    return host_check.loaded_at_logic_prompt(
        output.replace(LD_OK, host_check.LD_OK).replace(MARKER, host_check.MARKER)
    )


def run(fixture: str) -> tuple[bool, str, str]:
    acl2 = host_check.executable()
    if acl2 is None:
        return False, "FN_ACL2 is unset or does not name an executable", ""
    environment = os.environ.copy()
    environment["ACL2_CUSTOMIZATION"] = "NONE"
    environment["ACL2_BOOK_HASH_ALISTP"] = "NIL"
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    try:
        completed = subprocess.run(
            [str(acl2)], cwd=ROOT, input=driver_for(fixture).encode(),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=environment,
            timeout=TIMEOUT_SECONDS, check=False)
    except subprocess.TimeoutExpired as error:
        return False, f"timed out after {TIMEOUT_SECONDS}s", (error.output or b"").decode("utf-8", "replace")
    output = completed.stdout.decode("utf-8", "replace")
    ok, reason = succeeded_at_logic_prompt(output)
    return ok, reason, output


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixture", nargs="?", default="tests/owner-feed-connection-host.lsp")
    args = parser.parse_args(argv)
    fixture = Path(args.fixture)
    if fixture.is_absolute() or not (ROOT / fixture).is_file():
        parser.error("fixture must be a repository-relative existing file")
    ok, reason, output = run(fixture.as_posix())
    if ok:
        print(f"owner feed connection host wrapper passed: {fixture}")
        return 0
    print(f"owner feed connection host wrapper FAILED: {fixture}: {reason}", file=sys.stderr)
    if output:
        print("\n".join(output.splitlines()[-30:]), file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())

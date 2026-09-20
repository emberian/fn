#!/usr/bin/env python3
"""Load each host file alone, in its own ACL2, and require it to succeed.

The host files are never certified: they are `ld`ed by the Python bridges
(tools/run_store.py and its siblings) and `load`ed, in raw mode, by
host/native/build.lisp.  Nothing else reads them, so a host file that uses a
name a *sibling* host file defines is green under one bridge's load order and
broken under another's, and broken outright for any tool that loads it alone.
tools/ledger.py's `host_names` lint reports that statically.  This is the
dynamic half: one fresh ACL2 per host file, that file and nothing else, and
the file must load without an error and leave the session in the logic mode
and at the `ACL2 !>` prompt it found.

Three kinds of host file, decided from host/native/build.lisp rather than a
list typed here:

  ld    the interpreted `:program` wrappers, `(ld "<file>")`.
  raw   the raw Common Lisp the image loads under its trust tag, checked with
        the same `(progn! (set-raw-mode t) (load "<file>"))` the build uses.
  skip  host/native/build.lisp itself: it ends in `:q` and `save-exec`, so
        loading it is building the image.  tools/build_native_host.sh is its
        check.

Certificates for the books a host file includes must already be installed
(`python3 tools/certs.py install`), because `ld` of an `include-book` reads a
certificate it will not produce.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
HOST_DIRS = ("host", "host/native")
BUILD_SCRIPT = "host/native/build.lisp"
# The image build script names its own raw files; reading them from it keeps
# this tool from carrying a second copy of that decision.
RAW_LOAD = re.compile(r'\(load\s+"([^"]+\.lisp)"')
# Two markers, because one is not enough.  A failed `ld` does not end a
# session reading from a pipe: ACL2 reports the error, abandons that form and
# reads the next one, so a marker on its own line prints for a file that did
# not load.  Measured: host/config-host.lisp with its `ld` edge deleted
# reported `ACL2 Error [Translate]` for an undefined function and the marker
# still appeared.  LD_OK is printed from inside an `er-progn` with the load,
# which short-circuits, and MARKER by the next top-level form, whose prompt
# is the one the loaded file left behind.
LD_OK = "FN_HOST_CHECK_LD_OK"
MARKER = "FN_HOST_CHECK_LOADED"
PROMPT = "ACL2 !>"
ERRORS = ("ACL2 Error", "HARD ACL2 ERROR")
DEFAULT_TIMEOUT_SECONDS = 600


def executable() -> Path | None:
    configured = os.environ.get("FN_ACL2", "")
    if not configured:
        return None
    if os.sep in configured:
        candidate = Path(configured).expanduser()
        return candidate.resolve() if candidate.is_file() and os.access(candidate, os.X_OK) else None
    found = shutil.which(configured)
    return Path(found).resolve() if found else None


def raw_files() -> set[str]:
    text = (ROOT / BUILD_SCRIPT).read_text(encoding="utf-8")
    return {name for name in RAW_LOAD.findall(text) if (ROOT / name).is_file()}


def host_files() -> list[str]:
    found: list[str] = []
    for directory in HOST_DIRS:
        for path in sorted((ROOT / directory).glob("*.lisp")):
            found.append(path.relative_to(ROOT).as_posix())
    return found


def driver_for(relative: str, raw: bool) -> str:
    """The whole session: this one file, then one marker at the prompt.

    `:ld-error-action :error` turns any failure inside the file into a failed
    `ld`, and the marker is printed by a form read at the top level *after*
    it, so its prompt is the prompt the file left behind.  A file that ended
    in `(program)` prints `ACL2 p>` there and fails this check; every host
    file that switches mode restores it (host/anchor-host.lisp is the one
    that switches).
    """
    load = (f'(progn! (set-raw-mode t) (load "{relative}"))' if raw
            else f'(ld "{relative}" :ld-error-action :error)')
    return ("(defttag :fn-host-check)\n" if raw else "") \
        + f'(er-progn {load}\n' \
        + f'          (value-triple (cw "{LD_OK} ~s0~%" "{relative}")))\n' \
        + ("(defttag nil)\n" if raw else "") \
        + f'(cw "{MARKER} ~s0~%" "{relative}")\n(good-bye)\n'


def loaded_at_logic_prompt(output: str) -> tuple[bool, str]:
    """Did the load succeed, and did the prompt after it say `ACL2 !>`?

    ACL2 prints its prompt before reading each form and does not echo a form
    that came from a pipe, so a marker's own output follows the prompt on one
    line.  An error reported while the file was loading fails the check even
    if the session recovered from it.
    """
    lines = output.splitlines()
    end = next((i for i, line in enumerate(lines) if LD_OK in line), len(lines))
    for line in lines[:end]:
        if any(marker in line for marker in ERRORS):
            return False, f"error while loading: {line.strip()}"
    if end == len(lines):
        return False, "the load did not complete"
    for line in lines[end:]:
        if MARKER not in line:
            continue
        before = line.split(MARKER, 1)[0].strip()
        if before.endswith(PROMPT):
            return True, ""
        return False, f"loaded, but the prompt after it was {before!r}, not {PROMPT!r}"
    return False, "loaded, but the session did not reach a prompt after it"


def check(acl2: Path, relative: str, raw: bool, timeout: int) -> tuple[bool, str, str]:
    environment = os.environ.copy()
    environment["ACL2_CUSTOMIZATION"] = "NONE"
    # Content-hashed certificates, relocatable across worktrees and hosts.
    environment["ACL2_BOOK_HASH_ALISTP"] = "NIL"
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    try:
        result = subprocess.run(
            [str(acl2)], cwd=ROOT, input=driver_for(relative, raw).encode(),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=environment,
            timeout=timeout, check=False)
    except subprocess.TimeoutExpired as error:
        partial = (error.output or b"").decode("utf-8", "replace")
        return False, f"timed out after {timeout}s", partial
    output = result.stdout.decode("utf-8", "replace")
    ok, reason = loaded_at_logic_prompt(output)
    return ok, reason, output


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*",
                        help="host files to check (default: every one)")
    parser.add_argument("--timeout-seconds", type=int, default=DEFAULT_TIMEOUT_SECONDS)
    parser.add_argument("--log-dir", default=None,
                        help="write each session's transcript here")
    args = parser.parse_args(argv)

    acl2 = executable()
    if acl2 is None:
        # Loudly, not silently: an unset FN_ACL2 is a check that did not run.
        print("host_check: SKIPPED -- FN_ACL2 is unset or does not name an "
              "executable, so no host file was loaded.  This check is not "
              "evidence until it runs with a real ACL2.", file=sys.stderr)
        return 0

    raw = raw_files()
    targets = args.files or host_files()
    log_dir = Path(args.log_dir).resolve() if args.log_dir else None
    if log_dir is not None:
        log_dir.mkdir(parents=True, exist_ok=True)

    failures: list[tuple[str, str]] = []
    checked = 0
    for relative in targets:
        if relative == BUILD_SCRIPT:
            print(f"skip     {relative} -- image build script, ends in `:q` and "
                  "`save-exec`; tools/build_native_host.sh is its check")
            continue
        checked += 1
        ok, reason, output = check(acl2, relative, relative in raw, args.timeout_seconds)
        if log_dir is not None:
            (log_dir / (relative.replace("/", "_") + ".log")).write_text(output)
        kind = "raw " if relative in raw else "ld  "
        print(f"{'ok  ' if ok else 'FAIL'} {kind}{relative}" + ("" if ok else f" -- {reason}"))
        if not ok:
            failures.append((relative, reason))
            tail = "\n".join(output.splitlines()[-25:])
            print(tail, file=sys.stderr)
    print(f"host_check: {checked - len(failures)}/{checked} host files load "
          f"alone with {acl2}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())

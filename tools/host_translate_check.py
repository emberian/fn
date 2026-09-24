#!/usr/bin/env python3
"""`ld` the host files the way the image build does, without saving an image.

tools/build_native_host.sh feeds host/native/build.lisp to ACL2: 78
`include-book`s, then 29 `(ld "host/...lisp" :ld-error-action :error)`, then
a raw-mode region and `save-exec`.  The ACL2-mode prefix -- every form before
the first `defttag` -- is where a host file is translated, and where the
9c344d1d image build failed.  This runs exactly that prefix, in one ACL2,
under the machine's slot pool (tools/acl2), and requires it to finish with no
error marker the build script would have refused.

Three outcomes, kept distinct in the exit code:

  0  every include and every `ld` completed, no error marker;
  1  ACL2 reported an error (the transcript is printed from the first one);
  2  NOT RUN: no ACL2 (FN_ACL2 unset and no `acl2` on PATH), a book the
     prefix includes has no `.cert` beside it, or every form translated but
     an include warned [Uncertified] (installed pairs that do not compose,
     which the image build would refuse).  Install certificates with
     `python3 tools/certs.py install` first; certifying them is the farm's
     job, not this check's.

    python3 tools/host_translate_check.py [--build host/native/build.lisp]
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402
from tools.ledger import head  # noqa: E402

OK = "FN_HOST_TRANSLATE_OK"
# The markers tools/build_native_host.sh fails on.
ERRORS = ("ACL2 Error", "HARD ACL2 ERROR", "ABORTING from raw Lisp")
# tools/build_native_host.sh also refuses this one; here it means the
# certificates do not compose, which is not a translate verdict either way.
UNCERTIFIED = "Warning [Uncertified]"
NOT_RUN = 2


def prefix(build: Path) -> list[object]:
    """The build script's ACL2-mode forms: everything before its first `defttag`."""
    forms: list[object] = []
    for form, _line in ledger.Reader(build.read_text(encoding="utf-8")).top_level():
        if head(form) in ("defttag", "progn!", "save-exec"):
            break
        forms.append(form)
    return forms


def text(form) -> str:
    if isinstance(form, list):
        return "(" + " ".join(text(item) for item in form) + ")"
    if isinstance(form, ledger.Sym):
        return str(form)
    if isinstance(form, str):
        return '"' + form.replace("\\", "\\\\").replace('"', '\\"') + '"'
    return str(form)


def uncertified(forms: list[object]) -> list[str]:
    missing = []
    for form in forms:
        if head(form) == "include-book" and len(form) >= 2 and isinstance(form[1], str):
            if not (ROOT / (form[1] + ".cert")).is_file():
                missing.append(form[1])
    return missing


def acl2_available() -> bool:
    configured = os.environ.get("FN_ACL2", "acl2")
    return bool(shutil.which(configured) if os.sep not in configured
                else os.access(configured, os.X_OK))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--build", default="host/native/build.lisp")
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--log", default="build/host-translate/transcript.log")
    args = parser.parse_args(argv)

    build = ROOT / args.build
    forms = prefix(build)
    loads = sum(1 for form in forms if head(form) == "ld")
    if not acl2_available():
        print("host_translate_check: NOT RUN -- no ACL2 (FN_ACL2 unset and no "
              "`acl2` on PATH).  No host file was translated.")
        return NOT_RUN
    missing = uncertified(forms)
    if missing:
        print("host_translate_check: NOT RUN -- {} of the books {} includes have no "
              "certificate here, e.g. {}.  Run `python3 tools/certs.py install` "
              "(it installs only cached pairs).  No host file was translated."
              .format(len(missing), args.build, ", ".join(missing[:5])))
        return NOT_RUN

    # Fed on stdin, as tools/build_native_host.sh feeds build.lisp: an `ld`
    # of a driver file would bind the connected book directory to that
    # file's directory and resolve every relative path from there.  A failed
    # form does not end a piped session, so success is the absence of every
    # error marker AND the final marker, printed after the last form.
    driver = "\n".join(text(form) for form in forms) + \
        '\n(value-triple (cw "{} ~x0~%" {}))\n(good-bye)\n'.format(OK, loads)
    environment = os.environ.copy()
    environment["ACL2_CUSTOMIZATION"] = "NONE"
    environment["ACL2_BOOK_HASH_ALISTP"] = "NIL"
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    started = time.monotonic()
    result = subprocess.run(
        [sys.executable, str(ROOT / "tools/acl2"), "--timeout", str(args.timeout),
         "--label", "host-translate"],
        cwd=ROOT, input=driver.encode(), stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, env=environment, check=False)
    elapsed = time.monotonic() - started
    output = result.stdout.decode("utf-8", "replace")
    log = ROOT / args.log
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(output, encoding="utf-8")
    lines = output.splitlines()
    first_error = next((i for i, line in enumerate(lines)
                        if any(marker in line for marker in ERRORS)), None)
    finished = any(OK in line for line in lines)
    if first_error is not None or not finished:
        reason = ("timed out after {}s".format(args.timeout) if result.returncode == 124
                  else "error marker" if first_error is not None
                  else "the prefix did not complete")
        print("host_translate_check: FAIL ({}) after {:.0f}s; transcript {}"
              .format(reason, elapsed, log.relative_to(ROOT)))
        start = max((first_error if first_error is not None else len(lines)) - 5, 0)
        print("\n".join(lines[start:start + 40]))
        return 1
    stale = [line for line in lines if UNCERTIFIED in line]
    if stale:
        # Every form translated, but against certificates that do not
        # compose (pairs from different snapshot origins): the image build
        # refuses this, and a clean translate over them is not the verdict.
        print("host_translate_check: NOT RUN -- the prefix translated in {:.0f}s "
              "with no error, but {} includes warned [Uncertified] (certificates "
              "that do not compose); the verdict needs a consistent certificate "
              "set.  Transcript {}".format(elapsed, len(stale), log.relative_to(ROOT)))
        return NOT_RUN
    print("host_translate_check: ok -- {} includes and {} host `ld`s of {} "
          "translated in {:.0f}s".format(len(forms) - loads, loads, args.build, elapsed))
    return 0


if __name__ == "__main__":
    sys.exit(main())

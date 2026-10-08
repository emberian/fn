#!/usr/bin/env python3
"""Run one extraction-world image phase (core.sh's export and verify) and accept it only on evidence.

Accepted means: the child exited with status 0, AND it left OUT/<phase>.done reading exactly
"XT-<PHASE>-DONE <nonce> <sha256 of OUT/defs.lisp as it is now>".  The child writes that file from inside
the form that did the work, after the work returned (core.sh's xl-done), and the nonce is fresh per
invocation, so neither a stale file nor a log line ("XT-VERIFY-DEFS OK") from a child that then died is
accepted.  Any evidence file is removed before the child starts.

    image_run.py --phase VERIFY --out OUT --nonce N --stdin FILE --log FILE --timeout S --cwd DIR -- CMD...
"""
import argparse
import hashlib
import subprocess
import sys
from pathlib import Path


def expected(phase, out, nonce):
    defs = Path(out) / "defs.lisp"
    digest = hashlib.sha256(defs.read_bytes()).hexdigest() if defs.is_file() else "no-defs"
    return "XT-%s-DONE %s %s" % (phase, nonce, digest)


def evidence_path(phase, out):
    return Path(out) / ("%s.done" % phase.lower())


def run(phase, out, nonce, stdin, log, timeout, cwd, cmd):
    """(accepted, reason)."""
    ev = evidence_path(phase, out)
    ev.unlink(missing_ok=True)
    with open(stdin, "rb") as i, open(log, "wb") as o:
        try:
            status = subprocess.run(cmd, stdin=i, stdout=o, stderr=subprocess.STDOUT, cwd=cwd,
                                    timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            return False, "the %s run passed its %d s timeout" % (phase.lower(), timeout)
    got = ev.read_text().strip() if ev.is_file() else None
    if status != 0:
        return False, "the %s run exited with status %d (%s)" % (
            phase.lower(), status, "evidence %s" % got if got else "no completion evidence")
    if got is None:
        return False, "the %s run exited 0 but left no completion evidence" % phase.lower()
    want = expected(phase, out, nonce)
    if got != want:
        return False, "the %s run's evidence %r is not this invocation's %r" % (phase.lower(), got, want)
    return True, "ok"


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for name in ("phase", "out", "nonce", "stdin", "log", "cwd"):
        p.add_argument("--" + name, required=True)
    p.add_argument("--timeout", type=int, required=True)
    p.add_argument("cmd", nargs=argparse.REMAINDER)
    a = p.parse_args()
    cmd = a.cmd[1:] if a.cmd[:1] == ["--"] else a.cmd
    ok, reason = run(a.phase.upper(), a.out, a.nonce, a.stdin, a.log, a.timeout, a.cwd, cmd)
    if not ok:
        print("core: %s; see %s" % (reason, a.log), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()

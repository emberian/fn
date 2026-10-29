#!/usr/bin/env python3
"""E2 author checks. Sequential, warm dependencies only; never a farm claim."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
BUILD = ROOT / "build" / "e2"
BOOKS = ["defsquare", "defsquare-tests", "fold-contract", "read-state-history",
         "read-state-summary", "read-state-transport", "read-state-teeth",
         "q4-checker", "q4-template", "q4-square", "q4-template-tests",
         "q1-contract", "q1-bindings", "q1-template-tests"]


def disk_gate():
    free = shutil.disk_usage(ROOT).free
    if free < 60 * 1024**3:
        raise RuntimeError(f"BLOCKED: free disk {free / 1024**3:.2f} GiB < 60 GiB; delete nothing")


def invoke(name, command, data=None, limit=60, env=None):
    disk_gate()
    env = dict(os.environ if env is None else env,
               FN_ACL2_SLOT_DIR="/tmp/fn2-a4-acl2-slots", FN_ACL2_SLOTS="6")
    log = BUILD / (name + ".log")
    started = time.monotonic()
    with log.open("wb") as output:
        process = subprocess.Popen(command, cwd=ROOT, env=env,
                                   stdin=subprocess.PIPE if data else subprocess.DEVNULL,
                                   stdout=output, stderr=subprocess.STDOUT)
        (BUILD / (name + ".pid")).write_text(str(process.pid) + "\n")
        # tools/acl2 has its own child timeout and PID-scoped termination.
        # This outer wait deliberately does not kill any unrecorded process.
        process.communicate(data.encode() if data else None, timeout=limit)
    return process.returncode, time.monotonic() - started, log.read_text(errors="replace")


def source_identity():
    paths = sorted(p for p in HERE.iterdir()
                   if p.suffix in (".lisp", ".lsp", ".py", ".sha256")
                   and p.name != "evidence-events.lsp")
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in paths}
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    digest = hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()
    (BUILD / "source-hashes.json").write_text(json.dumps(hashes, indent=2) + "\n")
    return head + "+E2-sha256:" + digest


def main():
    disk_gate()
    BUILD.mkdir(parents=True, exist_ok=True)
    (BUILD / "run.pid").write_text(str(os.getpid()) + "\n")
    revision = source_identity()
    code, elapsed, output = invoke("standalone", ["timeout", "30", "sbcl", "--script",
                                              str(HERE / "standalone-check.lsp")], limit=35)
    if code or "E2 STANDALONE PASS" not in output:
        raise RuntimeError("Standalone controls failed; see build/e2/standalone.log")
    print(f"E2 standalone seconds={elapsed:.3f}; no ACL2 claim", flush=True)
    if "--standalone" in sys.argv:
        return
    selected = BOOKS[BOOKS.index(sys.argv[sys.argv.index("--from") + 1]):] if "--from" in sys.argv else BOOKS
    ledger_path = BUILD / "certify-times.json"
    ledger = ([row for row in json.loads(ledger_path.read_text()) if row["book"] not in selected]
              if "--from" in sys.argv and ledger_path.exists() else [])
    for book in selected:
        cert = HERE / (book + ".cert")
        before = cert.stat().st_mtime_ns if cert.exists() else None
        source = (f'(set-cbd "{HERE}/")\n(set-prover-step-limit 300000)\n'
                  f'(certify-book "{book}" 1)\n(good-bye)\n')
        code, elapsed, output = invoke("cert-" + book,
                                     [str(ROOT / "tools/acl2"), "--timeout", "58"],
                                     source, limit=65)
        certified = (cert.exists() and cert.stat().st_mtime_ns != before
                     and "PermissionError" not in output
                     and elapsed < 60)
        times = re.findall(r"Time:\s+([0-9.]+) seconds", output)
        ledger.append(dict(book=book, elapsed_seconds=elapsed,
                           acl2_seconds=float(times[-1]) if times else None,
                           returncode=code, certified=certified))
        (BUILD / "certify-times.json").write_text(json.dumps(ledger, indent=2) + "\n")
        print(f"E2 certify {book} certified={certified} seconds={elapsed:.3f}", flush=True)
        if not certified:
            raise RuntimeError(f"Certification blocked/failed; see build/e2/cert-{book}.log")
    env = dict(os.environ, SQ_REVISION=revision)
    code, elapsed, output = invoke("acceptance", [str(ROOT / "tools/acl2"), "--timeout", "120"],
                                  (HERE / "driver.lsp").read_text(), limit=130, env=env)
    if code or "E2 ACCEPTANCE PASS" not in output:
        raise RuntimeError("Acceptance failed; see build/e2/acceptance.log")
    actual = hashlib.sha256((HERE / "q1-translated.sexp").read_bytes()).hexdigest()
    expected = (HERE / "q1-pass2-translated.sha256").read_text().split()[0]
    if actual != expected:
        raise RuntimeError("Q1 translated statements changed from pass 2")
    print(f"E2 Q1 FORMULAS PASS rows=39 sha256={actual}", flush=True)
    print(f"E2 acceptance seconds={elapsed:.3f}; laptop author check only", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.TimeoutExpired) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)

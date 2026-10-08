#!/usr/bin/env python3
"""K2a gate: export a fresh ACL2 world on a build box, then inspect its routes.

python3 tests/acl2/catchup-carried-transit-closure.py --host persvati

No source-regex call graph or previously exported world is accepted. The
reference advance must expose fn-statep or fn-node-statep. All unresolved
routes and proof-REPL failures are failures of this gate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.extract.executed_closure import catchup  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", default="persvati", choices=("persvati", "hbox"))
    parser.add_argument("--lane", default=None)
    args = parser.parse_args()
    branch = subprocess.check_output(["git", "branch", "--show-current"], cwd=ROOT,
                                     text=True, timeout=10).strip()
    lane = args.lane or branch.removeprefix("lane/")
    name = f"catchup-closure-{os.getpid()}"
    directory = ROOT / "build" / name
    directory.mkdir()
    logpath = directory / "repl.log"
    repl = [sys.executable, "tools/proof_repl.py"]
    started = False
    try:
        with logpath.open("w") as log:
            def run(words, timeout=90):
                subprocess.run(words, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                               timeout=timeout, check=True)

            run(repl + ["start", name, "books/owner-outcome-counted", "--host", args.host,
                        "--lane", lane, "--cached-only"], timeout=180)
            started = True
            run(repl + ["send-file", name, "tools/extract/frontend.lisp"])
            # The target book sets CBD to books/. Export only the three
            # subjects; frontend.lisp obtains their executed bodies from w.
            artifact = f"{name}.json"
            form = ("(xt-extract '(fn-oop-advance fn-oct-transit fn-ocfg-advance) "
                    f'"../build/{artifact}" state)')
            run(repl + ["send", name, form])
            metadata = json.loads((ROOT / "build/proof-repl" / name / "remote.json").read_text())
            source = f"{metadata['host']}:{metadata['tree']}/build/{artifact}"
            worldpath = directory / "world.json"
            run(["rsync", "-az", source, str(worldpath)], timeout=30)

        raw = worldpath.read_bytes()
        report = catchup(json.loads(raw))
        report["world_sha256"] = hashlib.sha256(raw).hexdigest()
        report["git_revision"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True, timeout=10).strip()
        (directory / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        for result in report["subjects"]:
            print(f"K2a {result['root']}: {len(result['reached'])} reachable functions; "
                  f"{len(result['violations'])} forbidden")
        print("K2a reference tooth: " + ", ".join(report["reference_leaves"]["violations"]))
        print(f"K2a {'PASS' if report['passed'] else 'FAIL'}: {directory / 'report.json'}")
        return int(not report["passed"])
    except (subprocess.SubprocessError, OSError, ValueError, KeyError, RecursionError) as error:
        print(f"K2a UNRESOLVED: {error}; log {logpath}", file=sys.stderr)
        return 2
    finally:
        if started:
            with logpath.open("a") as log:
                subprocess.run(repl + ["stop", name], cwd=ROOT, stdout=log,
                               stderr=subprocess.STDOUT, timeout=30, check=True)


if __name__ == "__main__":
    raise SystemExit(main())

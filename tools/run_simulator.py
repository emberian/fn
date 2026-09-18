#!/usr/bin/env python3
"""Run fixed ACL2 model scenarios and retain their ACL2-produced traces."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
BUILD_ROOT = ROOT / "build" / "simulator"
TRACE_PREFIX = "FN_SIM_TRACE "
RESULT_PREFIX = "FN_SIM_RESULT "
SCENARIOS = ("acceptance-durable",)


def digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def executable() -> Path | None:
    configured = os.environ.get("FN_ACL2", "acl2")
    if os.sep in configured:
        candidate = Path(configured).expanduser()
        return candidate.resolve() if candidate.is_file() and os.access(candidate, os.X_OK) else None
    found = shutil.which(configured)
    return Path(found).resolve() if found else None


def driver_for(scenario: str) -> str:
    if scenario != "acceptance-durable":
        raise ValueError(f"unknown scenario: {scenario}")
    return '''(ld '((include-book "books/acceptance")
      (ld "host/simulator.lisp" :ld-error-action :return :ld-error-triples t)
      (value-triple
       (cw "FN_SIM_TRACE s=acceptance-durable t=initial a=~x0 n=~x1 f=~x2~%"
           (len (fn-state-articles (fn-sim-acceptance-initial)))
           (fn-state-next-txid (fn-sim-acceptance-initial))
           (fn-state-fenced (fn-sim-acceptance-initial))))
      (value-triple
       (cw "FN_SIM_TRACE s=acceptance-durable t=prepared a=~x0 n=~x1 p=~x2 f=~x3~%"
           (len (fn-state-articles (fn-sim-acceptance-prepared)))
           (fn-state-next-txid (fn-sim-acceptance-prepared))
           (consp (fn-state-pending (fn-sim-acceptance-prepared)))
           (fn-state-fenced (fn-sim-acceptance-prepared))))
      (value-triple
       (cw "FN_SIM_TRACE s=acceptance-durable t=durable a=~x0 n=~x1 q=~x2 f=~x3~%"
           (len (fn-state-articles (fn-sim-acceptance-durable)))
           (fn-state-next-txid (fn-sim-acceptance-durable))
           (fn-acceptedp *fn-sim-message-id*
                         (fn-state-articles (fn-sim-acceptance-durable)))
           (fn-state-fenced (fn-sim-acceptance-durable))))
      (value-triple
       (if (fn-sim-acceptance-durable-okp)
           (cw "FN_SIM_RESULT s=acceptance-durable r=passed~%")
         (cw "FN_SIM_RESULT s=acceptance-durable r=failed~%"))))
    :ld-error-action :return
    :ld-error-triples t)
(quit)
'''


def parse_records(output: str, prefix: str) -> list[dict[str, str]]:
    records: list[dict[str, str]] = []
    for line in output.splitlines():
        if prefix not in line:
            continue
        fields = line.split(prefix, 1)[1].split()
        record: dict[str, str] = {}
        for field in fields:
            key, separator, value = field.partition("=")
            if not separator or not key or not value:
                raise ValueError(f"malformed ACL2 record: {line}")
            record[key] = value
        records.append(record)
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scenario", nargs="*", choices=SCENARIOS, default=list(SCENARIOS))
    parser.add_argument("--timeout-seconds", type=int, default=120)
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")

    acl2 = executable()
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_dir = BUILD_ROOT / f"run-{stamp}-{os.getpid()}"
    run_dir.mkdir(parents=True, exist_ok=False)
    manifest: dict[str, object] = {
        "requested_scenarios": args.scenario,
        "timeout_seconds": args.timeout_seconds,
        "status": "failed",
    }
    if acl2 is None:
        manifest["failure"] = "ACL2 executable is unavailable; simulator did not run."
        (run_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        print(manifest["failure"], file=sys.stderr)
        return 2

    required = (ROOT / "books" / "acceptance.cert", ROOT / "host" / "simulator.lisp")
    missing = [path.relative_to(ROOT).as_posix() for path in required if not path.is_file()]
    if missing:
        manifest["failure"] = "required certified model or host scenario is missing: " + ", ".join(missing)
        (run_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        print(manifest["failure"], file=sys.stderr)
        return 2

    manifest["acl2_executable"] = str(acl2)
    manifest["acl2_executable_sha256"] = digest(acl2)
    manifest["input_digests_sha256"] = {
        path.relative_to(ROOT).as_posix(): digest(path)
        for path in (ROOT / "books" / "acceptance.lisp", *required[1:])
    }
    outcomes: list[dict[str, object]] = []
    all_passed = True
    environment = os.environ.copy()
    environment["ACL2_CUSTOMIZATION"] = "NONE"
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    for scenario in args.scenario:
        driver = driver_for(scenario)
        (run_dir / f"{scenario}.driver.lsp").write_text(driver, encoding="utf-8")
        try:
            result = subprocess.run(
                [str(acl2)], cwd=ROOT, input=driver.encode(), stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, env=environment, timeout=args.timeout_seconds, check=False,
            )
            output = result.stdout.decode("utf-8", errors="replace")
            exit_code: int | str = result.returncode
        except subprocess.TimeoutExpired as error:
            raw = error.stdout or b""
            output = raw.decode("utf-8", errors="replace") if isinstance(raw, bytes) else str(raw)
            exit_code = "timed out"
        (run_dir / f"{scenario}.log").write_text(output, encoding="utf-8")
        try:
            traces = parse_records(output, TRACE_PREFIX)
            results = parse_records(output, RESULT_PREFIX)
        except ValueError as error:
            traces, results = [], []
            parse_error = str(error)
        else:
            parse_error = None
        passed = (
            exit_code == 0 and parse_error is None and len(results) == 1
            and results[0] == {"s": scenario, "r": "passed"}
            and len(traces) == 3 and all(trace.get("s") == scenario for trace in traces)
        )
        outcomes.append({"scenario": scenario, "exit_code": exit_code, "traces": traces,
                         "result": results, "parse_error": parse_error, "passed": passed})
        all_passed = all_passed and passed

    manifest["outcomes"] = outcomes
    manifest["status"] = "passed" if all_passed else "failed"
    (run_dir / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    for outcome in outcomes:
        print(f"{outcome['scenario']}: {'passed' if outcome['passed'] else 'failed'}")
        for trace in outcome["traces"]:
            detail = [f"step={trace.get('t', '?')}", f"articles={trace.get('a', '?')}",
                      f"next_txid={trace.get('n', '?')}", f"fenced={trace.get('f', '?')}"]
            if "p" in trace:
                detail.append(f"pending={trace['p']}")
            if "q" in trace:
                detail.append(f"accepted={trace['q']}")
            print("  " + " ".join(detail))
    print(f"Simulator evidence: {run_dir.relative_to(ROOT)}")
    return 0 if all_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())

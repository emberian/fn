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
sys.path.insert(0, str(ROOT / "tools"))
import acl2_slots  # noqa: E402

BUILD_ROOT = ROOT / "build" / "simulator"
TRACE_PREFIX = "FN_SIM_TRACE "
RESULT_PREFIX = "FN_SIM_RESULT "
PLAN_PREFIX = "FN_SIM_PLAN "
ORACLE_PREFIX = "FN_SIM_ORACLE "
SCENARIOS = ("acceptance-durable", "acceptance-world")
# acceptance-durable: one proposal, prepared, completed :durable (three trace
# lines).  acceptance-world (design W7f): the exhaustive small world in
# tests/acl2/simulator.lisp -- two proposals under every completion status,
# generation, recovery result and a repeated recovery; one trace line per
# step; the result line carries n=<schedules>.


def digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def executable() -> Path | None:
    configured = acl2_slots.configured_acl2()
    if os.sep in configured:
        candidate = Path(configured).expanduser()
        return candidate.resolve() if candidate.is_file() and os.access(candidate, os.X_OK) else None
    found = shutil.which(configured)
    return Path(found).resolve() if found else None


def driver_for(scenario: str) -> str:
    if scenario == "acceptance-world":
        return WORLD_DRIVER
    if scenario != "acceptance-durable":
        raise ValueError(f"unknown scenario: {scenario}")
    return '''(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(ld '((include-book "books/acceptance")
      (ld "tests/acl2/simulator.lisp" :ld-error-action :return :ld-error-triples t)
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


WORLD_DRIVER = '''(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(ld '((include-book "books/acceptance")
      (ld "tests/acl2/simulator.lisp" :ld-error-action :return :ld-error-triples t)
      (value-triple (prog2$ (fn-sim-world-report) t)))
    :ld-error-action :return
    :ld-error-triples t)
(quit)
'''


def scenario_passed(scenario: str, exit_code, parse_error, traces: list, results: list,
                    plans: list | None = None, oracles: list | None = None) -> bool:
    """The runner's verdict over the parsed records: ACL2 exited 0, one
    result line naming the scenario as passed, every trace line the
    scenario's; acceptance-durable prints exactly its three steps, the
    world consumes its exact schedule plan and independent oracle records."""
    if exit_code != 0 or parse_error is not None or len(results) != 1:
        return False
    result = results[0]
    if result.get("s") != scenario or result.get("r") != "passed":
        return False
    if not all(trace.get("s") == scenario for trace in traces):
        return False
    if scenario == "acceptance-world":
        # This fixed world is ten alternatives for each of two proposals.
        # A count claimed by the child cannot make a shortened run complete.
        if result.get("n") != "100" or not plans or not oracles:
            return False
        expected = []
        for k, plan in enumerate(plans):
            if plan.get("s") != scenario or plan.get("k") != str(k):
                return False
            if plan.get("n") not in ("4", "6", "8"):
                return False
            expected.extend((str(k), str(i)) for i in range(int(plan["n"])))
        if len(plans) != 100 or len(expected) != 560:
            return False
        if [(r.get("k"), r.get("i")) for r in traces] != expected:
            return False
        if [(r.get("k"), r.get("i")) for r in oracles] != expected:
            return False
        return all({"s", "k", "i", "t", "m", "g", "x", "a", "p", "f"} <= t.keys()
                   and {"s", "k", "i", "a", "p", "f", "q"} <= o.keys()
                   and o.get("s") == scenario and
                   all(key in t and t[key] == o[key] for key in ("a", "p", "f", "q"))
                   for t, o in zip(traces, oracles))
    expected = [dict(t="initial", a="0", n="0", f="NIL"),
                dict(t="prepared", a="0", n="1", p="T", f="NIL"),
                dict(t="durable", a="1", n="1", q="T", f="NIL")]
    return len(traces) == 3 and all(
        all(t.get(key) == value for key, value in e.items())
        for t, e in zip(traces, expected))


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
            if key in record:
                raise ValueError(f"duplicate ACL2 record field: {key}")
            record[key] = value
        records.append(record)
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    # No list default: argparse checks a non-string default against
    # `choices` whole (the run refused itself once SCENARIOS had two names).
    parser.add_argument("scenario", nargs="*", choices=SCENARIOS)
    parser.add_argument("--timeout-seconds", type=int, default=120)
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    args.scenario = args.scenario or list(SCENARIOS)

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

    required = (ROOT / "books" / "acceptance.cert", ROOT / "tests" / "acl2" / "simulator.lisp")
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
    for scenario in args.scenario:
        driver = driver_for(scenario)
        (run_dir / f"{scenario}.driver.lsp").write_text(driver, encoding="utf-8")
        try:
            # The machine's ACL2 pool and heap cap (PKT-162).
            result = acl2_slots.run(
                [str(acl2)], f"simulator {scenario}", cwd=ROOT, input=driver.encode(),
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=args.timeout_seconds, check=False,
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
            plans = parse_records(output, PLAN_PREFIX)
            oracles = parse_records(output, ORACLE_PREFIX)
        except ValueError as error:
            traces, results, plans, oracles = [], [], [], []
            parse_error = str(error)
        else:
            parse_error = None
        passed = scenario_passed(scenario, exit_code, parse_error, traces, results,
                                 plans, oracles)
        outcomes.append({"scenario": scenario, "exit_code": exit_code, "traces": traces,
                         "result": results, "plans": plans, "oracles": oracles,
                         "parse_error": parse_error, "passed": passed})
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

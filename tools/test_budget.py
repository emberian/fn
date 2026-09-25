#!/usr/bin/env python3
"""Run test modules one per process, report each one's wall time, fail over budget.

    python3 tools/test_budget.py tests.test_store tests.test_checkpoint
    python3 tools/test_budget.py --discover          # every tests/test_*.py
    python3 tools/test_budget.py --budget 300 --json build/test-budget.json ...

Iteration time is a property the suite must keep, not a side effect of it
(PKT-163: three store modules had grown to 1,857 to 2,280 s each, and nothing
reported it).  Each module runs in its own `python3 -m unittest` process with
a per-test timing result; the report lists every module's wall time and its
slowest tests.  A module still running at its budget is terminated and
reported OVER BUDGET, so an over-budget module costs at most its budget.

Outcomes stay distinct: a module passes, fails its tests, or exceeds its
budget, and the exit code is 0 only when every module passed within budget
(1 test failures, 2 budget exceeded, both 3).  Budgets: the default is 300 s;
`tests/test_budgets.json` may name a smaller one per module, never a larger
one, so the rule cannot be relaxed one module at a time.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import unittest

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BUDGET_SECONDS = 300.0
BUDGETS_FILE = ROOT / "tests" / "test_budgets.json"
GRACE_SECONDS = 10.0
RESULT_PREFIX = "FN_TEST_BUDGET_RESULT "


class _TimedResult(unittest.TextTestResult):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.timings: list[tuple[str, float]] = []
        self._started: dict[str, float] = {}

    def startTest(self, test):
        self._started[test.id()] = time.monotonic()
        super().startTest(test)

    def stopTest(self, test):
        started = self._started.pop(test.id(), None)
        if started is not None:
            self.timings.append((test.id(), round(time.monotonic() - started, 3)))
        super().stopTest(test)


def run_one(module: str) -> int:
    """Child mode: run one module and print its timings as one JSON line."""
    sys.path.insert(0, str(ROOT))
    os.chdir(ROOT)
    suite = unittest.defaultTestLoader.loadTestsFromName(module)
    runner = unittest.TextTestRunner(resultclass=_TimedResult, verbosity=2)
    result = runner.run(suite)
    print(RESULT_PREFIX + json.dumps({
        "module": module,
        "tests": result.testsRun,
        "failures": len(result.failures),
        "errors": len(result.errors),
        "skipped": len(result.skipped),
        "timings": result.timings,
    }), flush=True)
    return 0 if result.wasSuccessful() else 1


def budgets() -> dict[str, float]:
    if not BUDGETS_FILE.is_file():
        return {}
    data = json.loads(BUDGETS_FILE.read_text())
    return {str(name): float(value) for name, value in data.get("budgets", {}).items()}


def budget_for(module: str, default: float, table: dict[str, float]) -> float:
    return min(default, table.get(module, default))


def discover() -> list[str]:
    return sorted(f"tests.{path.stem}" for path in (ROOT / "tests").glob("test_*.py"))


def run_module(module: str, budget: float, log_dir: Path | None) -> dict:
    command = [sys.executable, str(Path(__file__).resolve()), "--one", module]
    started = time.monotonic()
    log_path = None
    if log_dir is not None:
        log_dir.mkdir(parents=True, exist_ok=True)
        log_path = log_dir / f"{module}.log"
    with open(log_path, "wb") if log_path else open(os.devnull, "wb") as log:
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        output = bytearray()
        over = False
        assert process.stdout is not None
        os.set_blocking(process.stdout.fileno(), False)
        while True:
            chunk = None
            try:
                chunk = process.stdout.read()
            except BlockingIOError:
                pass
            if chunk:
                output += chunk
                log.write(chunk)
                log.flush()
            if process.poll() is not None:
                rest = process.stdout.read() or b""
                output += rest
                log.write(rest)
                break
            if time.monotonic() - started > budget:
                over = True
                # The module's own process group: its ACL2 children go with it.
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=GRACE_SECONDS)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                output += process.stdout.read() or b""
                break
            time.sleep(0.05)
    seconds = round(time.monotonic() - started, 3)
    record = {"module": module, "seconds": seconds, "budget": budget,
              "over_budget": over, "returncode": process.returncode,
              "log": str(log_path) if log_path else None}
    for line in output.decode("utf-8", "replace").splitlines():
        if line.startswith(RESULT_PREFIX):
            record.update(json.loads(line[len(RESULT_PREFIX):]))
    record["passed"] = (not over and process.returncode == 0
                        and "tests" in record)
    return record


def summarize(record: dict, slowest: int) -> str:
    if record["over_budget"]:
        verdict = f"OVER BUDGET (terminated at {record['budget']:g} s)"
    elif record["passed"]:
        verdict = "ok"
    else:
        verdict = (f"FAILED ({record.get('failures', '?')} failures, "
                   f"{record.get('errors', '?')} errors, exit {record['returncode']})")
    line = (f"{record['module']}: {record['seconds']:.1f} s of {record['budget']:g} s, "
            f"{record.get('tests', '?')} tests, {verdict}")
    timings = sorted(record.get("timings", []), key=lambda item: -item[1])[:slowest]
    for name, seconds in timings:
        line += f"\n    {seconds:8.2f} s  {name.rsplit('.', 2)[-2]}.{name.rsplit('.', 1)[-1]}"
    return line


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("modules", nargs="*", help="dotted module names (tests.test_x)")
    parser.add_argument("--discover", action="store_true",
                        help="every tests/test_*.py module")
    parser.add_argument("--budget", type=float, default=DEFAULT_BUDGET_SECONDS,
                        help="per-module wall-time budget in seconds (default 300; "
                             "tests/test_budgets.json may only lower it)")
    parser.add_argument("--slowest", type=int, default=3,
                        help="slowest tests listed per module")
    parser.add_argument("--logs", type=Path, default=None,
                        help="directory for one log per module")
    parser.add_argument("--json", type=Path, default=None, help="write the records here")
    parser.add_argument("--one", default=None, help=argparse.SUPPRESS)
    arguments = parser.parse_args(argv)
    if arguments.one:
        return run_one(arguments.one)
    if arguments.budget > DEFAULT_BUDGET_SECONDS:
        parser.error(f"--budget may not exceed {DEFAULT_BUDGET_SECONDS:g} s")
    modules = list(arguments.modules) + (discover() if arguments.discover else [])
    if not modules:
        parser.error("name modules or pass --discover")
    table = budgets()
    records = []
    for module in modules:
        record = run_module(module, budget_for(module, arguments.budget, table),
                            arguments.logs)
        records.append(record)
        print(summarize(record, arguments.slowest), flush=True)
    if arguments.json:
        arguments.json.parent.mkdir(parents=True, exist_ok=True)
        arguments.json.write_text(json.dumps(records, indent=2) + "\n")
    failed = any(not r["passed"] and not r["over_budget"] for r in records)
    over = any(r["over_budget"] for r in records)
    total = sum(r["seconds"] for r in records)
    print(f"{len(records)} modules, {total:.1f} s; "
          f"{sum(r['passed'] for r in records)} passed within budget, "
          f"{sum(r['over_budget'] for r in records)} over budget", flush=True)
    return (1 if failed else 0) | (2 if over else 0)


if __name__ == "__main__":
    sys.exit(main())

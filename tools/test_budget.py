#!/usr/bin/env python3
"""Run test modules one per process, report each one's wall time, fail over budget.

    python3 tools/test_budget.py tests.test_store tests.test_checkpoint
    python3 tools/test_budget.py --discover          # every tests/test_*.py
    python3 tools/test_budget.py --budget 120 --json build/test-budget.json ...
    python3 tools/test_budget.py --order reverse tests.test_auth   # order dependence

Iteration time is a property the suite must keep, not a side effect of it
(PKT-163: three store modules had grown to 1,857 to 2,280 s each, and nothing
reported it).  Each module runs in its own `python3 -m unittest` process with
a per-test timing result; the report lists every module's wall time and its
slowest tests.  A module still running at its budget is terminated and
reported OVER BUDGET, so an over-budget module costs at most its budget.

Outcomes stay distinct: a module passes, fails its tests, exceeds its
budget, or skips every test it has, and the exit code is 0 only when every
module passed within budget.  The code is a sum of bits: 1 test failures,
2 budget exceeded (both 3, as before), 4 a module ran to the end with no test
executed -- every test skipped, reported `SKIPPED (N of N)` with each skip's
reason (PKT-437 (2): seven lanes read a module whose every test skipped for a
missing image as "OK").  A module with some tests skipped passes and lists
its skips; `--allow-skipped` keeps the report and drops bit 4, for a suite
run where modules are known to lack their image (the laptop's --discover).
`--verdict LOG` prints the verdict of a `--one` run's log (tools/hbox_native.sh
runs each module that way, with no budget) and exits with its code.  Budgets: a module 180 s, one
test 20 s (the Fable mandate's three minutes per module and 20 s per test,
harness-repair 2026-09-25; the module default was 300 s).  A test that
finished over its budget makes its module over budget, named in the report;
the module is not killed for it.  `tests/test_budgets.json` may name a
smaller module budget, never a larger one, so the rule cannot be relaxed one
module at a time.
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
DEFAULT_BUDGET_SECONDS = 180.0
TEST_BUDGET_SECONDS = 20.0
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


def _flatten(suite) -> list:
    out = []
    for item in suite:
        if isinstance(item, unittest.TestSuite):
            out.extend(_flatten(item))
        else:
            out.append(item)
    return out


def run_one(module: str, order: str = "default") -> int:
    """Child mode: run one module and print its timings as one JSON line.

    `order="reverse"` runs the module's tests last to first (classes stay
    contiguous, so class fixtures still run once per class).  A test that
    passes in one order and fails in the other depends on what an earlier
    test left in a shared world -- a class fixture, a process-wide session,
    the environment -- which is the contamination this option exists to find.
    """
    sys.path.insert(0, str(ROOT))
    os.chdir(ROOT)
    suite = unittest.defaultTestLoader.loadTestsFromName(module)
    if order == "reverse":
        suite = unittest.TestSuite(reversed(_flatten(suite)))
    runner = unittest.TextTestRunner(resultclass=_TimedResult, verbosity=2)
    result = runner.run(suite)
    # A setUpClass/setUpModule SkipTest is one skip for tests never counted
    # in testsRun; a skipped test is counted in both.
    counted = sum(isinstance(test, unittest.TestCase) for test, _ in result.skipped)
    print(RESULT_PREFIX + json.dumps({
        "module": module,
        "tests": result.testsRun,
        "failures": len(result.failures),
        "errors": len(result.errors),
        "skipped": len(result.skipped),
        "executed": result.testsRun - counted,
        "skips": [[test.id() if isinstance(test, unittest.TestCase) else str(test),
                   str(reason)] for test, reason in result.skipped],
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


def run_module(module: str, budget: float, log_dir: Path | None,
               order: str = "default") -> dict:
    command = [sys.executable, str(Path(__file__).resolve()), "--one", module,
               "--order", order]
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
              "over_budget": over, "terminated": over, "returncode": process.returncode,
              "log": str(log_path) if log_path else None}
    for line in output.decode("utf-8", "replace").splitlines():
        if line.startswith(RESULT_PREFIX):
            record.update(json.loads(line[len(RESULT_PREFIX):]))
    record["slow_tests"] = [[name, seconds] for name, seconds in record.get("timings", [])
                            if seconds > TEST_BUDGET_SECONDS]
    if record["slow_tests"]:
        over = True
    record["over_budget"] = over
    return verdict_fields(record)


def verdict_fields(record: dict) -> dict:
    """`all_skipped` and `passed`: a module that executed no test did not pass."""
    over = record.get("over_budget", False)
    record["all_skipped"] = (not over and record.get("returncode") == 0
                             and "tests" in record and record.get("executed", 1) == 0)
    record["passed"] = (not over and record.get("returncode") == 0
                        and "tests" in record and not record["all_skipped"])
    return record


def summarize(record: dict, slowest: int) -> str:
    if record["over_budget"] and record.get("slow_tests") and record["seconds"] < record["budget"]:
        slow = ", ".join(f"{name.rsplit('.', 1)[-1]} {seconds:.1f} s"
                         for name, seconds in record["slow_tests"])
        verdict = (f"OVER BUDGET (a test over {TEST_BUDGET_SECONDS:g} s: {slow}"
                   + ("" if record.get("returncode") == 0 else
                      f"; also exit {record.get('returncode')}") + ")")
    elif record["over_budget"]:
        verdict = f"OVER BUDGET (terminated at {record['budget']:g} s)"
    elif record["all_skipped"]:
        verdict = f"SKIPPED ({record['skipped']} of {record['skipped']}; no test executed)"
    elif record["passed"]:
        verdict = "ok" + (f" ({record['skipped']} skipped)" if record.get("skipped") else "")
    else:
        verdict = (f"FAILED ({record.get('failures', '?')} failures, "
                   f"{record.get('errors', '?')} errors, exit {record['returncode']})")
    line = (f"{record['module']}: {record['seconds']:.1f} s of {record['budget']:g} s, "
            f"{record.get('tests', '?')} tests, {verdict}")
    timings = sorted(record.get("timings", []), key=lambda item: -item[1])[:slowest]
    for name, seconds in timings:
        line += f"\n    {seconds:8.2f} s  {name.rsplit('.', 2)[-2]}.{name.rsplit('.', 1)[-1]}"
    for name, reason in record.get("skips", []):
        line += f"\n    skipped  {name}: {reason}"
    return line


def verdict_of_log(path: Path) -> int:
    """Print the verdict of a `--one` run's log; exit 0 passed, 1 failed, 4 all skipped."""
    record = {"module": path.stem, "seconds": 0.0, "budget": 0.0, "over_budget": False,
              "returncode": None}
    for line in path.read_text(errors="replace").splitlines():
        if line.startswith(RESULT_PREFIX):
            record.update(json.loads(line[len(RESULT_PREFIX):]))
    if "tests" not in record:
        print(f"{record['module']}: FAILED (no result line in {path})")
        return 1
    record["returncode"] = 0 if (record["failures"] == 0 and record["errors"] == 0) else 1
    record["seconds"] = sum(seconds for _, seconds in record.get("timings", []))
    verdict_fields(record)
    if record["all_skipped"]:
        verdict = f"SKIPPED ({record['skipped']} of {record['skipped']}; no test executed)"
    elif record["passed"]:
        verdict = f"OK ({record['executed']} ran, {record['skipped']} skipped)"
    else:
        verdict = (f"FAILED ({record['failures']} failures, {record['errors']} errors, "
                   f"{record['executed']} ran, {record['skipped']} skipped)")
    print(f"{record['module']}: {verdict}")
    for name, reason in record.get("skips", []):
        print(f"    skipped  {name}: {reason}")
    return 0 if record["passed"] else 4 if record["all_skipped"] else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("modules", nargs="*", help="dotted module names (tests.test_x)")
    parser.add_argument("--discover", action="store_true",
                        help="every tests/test_*.py module")
    parser.add_argument("--budget", type=float, default=DEFAULT_BUDGET_SECONDS,
                        help="per-module wall-time budget in seconds (default 180; "
                             "tests/test_budgets.json may only lower it)")
    parser.add_argument("--slowest", type=int, default=3,
                        help="slowest tests listed per module")
    parser.add_argument("--logs", type=Path, default=None,
                        help="directory for one log per module")
    parser.add_argument("--json", type=Path, default=None, help="write the records here")
    parser.add_argument("--order", choices=("default", "reverse"), default="default",
                        help="run each module's tests in reverse to expose a test "
                             "that depends on what an earlier one left behind")
    parser.add_argument("--allow-skipped", action="store_true",
                        help="report a module that skipped every test as SKIPPED but "
                             "leave exit bit 4 clear (a suite run known to lack images)")
    parser.add_argument("--verdict", type=Path, default=None,
                        help="print the verdict of a --one run's log and exit with it "
                             "(0 passed, 1 failed, 4 every test skipped)")
    parser.add_argument("--one", default=None, help=argparse.SUPPRESS)
    arguments = parser.parse_args(argv)
    if arguments.one:
        return run_one(arguments.one, arguments.order)
    if arguments.verdict:
        return verdict_of_log(arguments.verdict)
    if arguments.budget > DEFAULT_BUDGET_SECONDS:
        parser.error(f"--budget may not exceed {DEFAULT_BUDGET_SECONDS:g} s")
    modules = list(arguments.modules) + (discover() if arguments.discover else [])
    if not modules:
        parser.error("name modules or pass --discover")
    table = budgets()
    records = []
    for module in modules:
        record = run_module(module, budget_for(module, arguments.budget, table),
                            arguments.logs, arguments.order)
        records.append(record)
        print(summarize(record, arguments.slowest), flush=True)
    if arguments.json:
        arguments.json.parent.mkdir(parents=True, exist_ok=True)
        arguments.json.write_text(json.dumps(records, indent=2) + "\n")
    # A module killed at its budget has no verdict of its own; one that ran
    # to the end failed when its tests did, even if a test was also slow.
    failed = any(not r["terminated"] and (r["returncode"] != 0 or "tests" not in r)
                 for r in records)
    over = any(r["over_budget"] for r in records)
    skipped = sum(r["all_skipped"] for r in records)
    total = sum(r["seconds"] for r in records)
    print(f"{len(records)} modules, {total:.1f} s; "
          f"{sum(r['passed'] for r in records)} passed within budget, "
          f"{skipped} SKIPPED (no test executed), "
          f"{sum(r['over_budget'] for r in records)} over budget; "
          f"{sum(r.get('skipped', 0) for r in records)} tests skipped", flush=True)
    return ((1 if failed else 0) | (2 if over else 0)
            | (4 if skipped and not arguments.allow_skipped else 0))


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Run every native test module's image-free checks, in a tree with no image.

PKT-540/569: 29 native modules assert the source text of books and host files
(`fn-sco-store-open e config-records frontier` in a host function, a book's
call through a keystone subject).  They ran only on a native run, so a
refactor that broke one stayed green until the next image, and six went red
that way.  Their image-free tests need no image, so `make check` runs them:

    python3 tools/native_source_check.py            # every tests/test_native_*.py
    python3 tools/native_source_check.py tests.test_native_owner ...
    python3 tools/native_source_check.py --jobs 8 --timeout 180

IMAGE-FREE BY CONSTRUCTION.  The modules run in a scratch root that holds
copies of tests/ and tools/ (a test computes the repository root from its own
file, resolving symlinks) and links to every other top-level entry EXCEPT
build/: no build/fn-host* image, launcher or certificate is there to find.
Every FN_* variable is removed from the environment (FN_NATIVE_HOST,
FN_RUN_*, the identity digests), so a module's image tests skip for the
reason they state and only the checks that need no image run.

Each module prints one line: OK with the tests run and skipped, or FAILED
with the failing tests named (a module that fails to import, collects nothing
or times out is FAILED with that cause: a source check that silently runs
nothing is the lie this step exists to refuse).  A module whose every test
skips is OK: all it has are image tests.  Exit 1 when any module failed.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
COPIED = ("tests", "tools")
EXCLUDED = ("build",)
IGNORED = shutil.ignore_patterns("__pycache__", "*.cert", "*.cert.out", "*.fasl",
                                 "*.port", "*.pcert0", "*.pcert1", "*.acl2x",
                                 "*.out", "*.time")
# Red at the first run (persvati, lane tooling-truth, 2026-09-29, at ec4d4d13c):
# real findings with owners owed, listed so the step lands green and can only
# shrink -- a module here that goes green, or one not here that goes red, fails.
KNOWN_RED = {
    "tests.test_native_app_journal": "collected no test",
    "tests.test_native_compression": "collected no test",
    "tests.test_native_log_damage": "collected no test",
    "tests.test_native_reader_clients": "collected no test",
    "tests.test_native_reader_freshness": "collected no test",
    "tests.test_native_served_differential": "collected no test",
    "tests.test_native_recovery": "a source-map test fails with no image",
    "tests.test_native_served_crash_model": "exits 5 with no image",
    "tests.test_native_tls_transport": "three TLS tests run and fail with no image",
}
RAN = re.compile(r"^Ran (\d+) tests? in ", re.M)
SKIPPED = re.compile(r"\bskipped=(\d+)")
SUMMARY = re.compile(r"^(?:OK|FAILED)(?: \(.*\))?$", re.M)
FAILED_TEST = re.compile(r"^(?:FAIL|ERROR): (\S+) \(([^)]+)\)", re.M)


def modules(root: Path = ROOT) -> list[str]:
    return sorted(f"tests.{p.stem}" for p in (root / "tests").glob("test_native_*.py"))


def image_free_root(root: Path, into: Path) -> Path:
    """A scratch copy of ROOT without build/: tests/ and tools/ copied,
    everything else linked."""
    for entry in sorted(root.iterdir()):
        if entry.name in EXCLUDED or entry.name.startswith("."):
            continue
        target = into / entry.name
        if entry.name in COPIED:
            shutil.copytree(entry, target, ignore=IGNORED, symlinks=True)
        else:
            target.symlink_to(entry)
    return into


def scrubbed_env(env: dict[str, str] | None = None) -> dict[str, str]:
    source = dict(os.environ if env is None else env)
    clean = {k: v for k, v in source.items() if not k.startswith("FN_")}
    clean["PYTHONDONTWRITEBYTECODE"] = "1"
    return clean


def verdict(module: str, status: int | None, output: str, seconds: float) -> tuple[bool, str]:
    """(ok, line) for one module's unittest OUTPUT and exit STATUS (None: timed out)."""
    if status is None:
        return False, (f"FAILED {module}: timed out after {seconds:.0f} s with no image "
                       "(an image-free run must not wait on an image)")
    ran = RAN.findall(output)
    if not ran:
        tail = " | ".join(line for line in output.strip().splitlines()[-3:])
        return False, f"FAILED {module}: no result line (exit {status}): {tail}"
    count = int(ran[-1])
    closing = SUMMARY.findall(output)
    skipped = sum(int(n) for n in SKIPPED.findall(closing[-1])) if closing else 0
    failing = sorted({(where if where.endswith("." + name) else f"{where}.{name}")
                      .split(".", 2)[-1] for name, where in FAILED_TEST.findall(output)})
    if status != 0 or failing:
        named = ", ".join(failing[:6]) or f"exit {status}"
        return False, f"FAILED {module}: {named}"
    if count == 0:
        return False, f"FAILED {module}: collected no test"
    return True, (f"OK     {module}: {count - skipped} run, {skipped} NOT RUN (need an image) "
                  f"({seconds:.1f} s)")


def run_one(module: str, root: Path, env: dict[str, str], timeout: int) -> tuple[bool, str]:
    start = time.monotonic()
    try:
        answer = subprocess.run([sys.executable, "-m", "unittest", module],
                                cwd=root, env=env, capture_output=True, text=True,
                                timeout=timeout)
    except subprocess.TimeoutExpired:
        return verdict(module, None, "", time.monotonic() - start)
    return verdict(module, answer.returncode, answer.stderr + answer.stdout,
                   time.monotonic() - start)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("modules", nargs="*")
    parser.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 1))
    parser.add_argument("--timeout", type=int, default=180,
                        help="seconds per module (tools/test_budget.py's module budget)")
    args = parser.parse_args(argv)
    chosen = args.modules or modules()
    env = scrubbed_env()
    failed: list[str] = []
    with tempfile.TemporaryDirectory(prefix="fn-native-source.") as scratch:
        root = image_free_root(ROOT, Path(scratch))
        with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
            results = list(pool.map(lambda m: run_one(m, root, env, args.timeout), chosen))
    known = 0
    for module, (ok, line) in zip(chosen, results):
        if not ok and module in KNOWN_RED:
            known += 1
            print(f"KNOWN  {line} [KNOWN_RED: {KNOWN_RED[module]}]")
            continue
        if ok and module in KNOWN_RED and not args.modules:
            line = f"FAILED {module}: green now; remove it from KNOWN_RED"
            ok = False
        print(line)
        if not ok:
            failed.append(line)
    print(f"native_source_check: {len(chosen) - len(failed)}/{len(chosen)} native modules "
          f"green with no image; {known} known red (KNOWN_RED); {len(failed)} failed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

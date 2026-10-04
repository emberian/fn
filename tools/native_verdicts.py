#!/usr/bin/env python3
"""Native module verdicts as content-addressed facts: key, record, look up.

planning/design/iteration-architecture-2026-10-04.md section 2.1 and slice 3.
A native module's verdict depends on exactly: the module's source and the
tests/ helpers it imports (transitively), tests/native_harness.py and
tools/test_budget.py, the identity of every image it reads (launcher, core
and runtime SHA-256 per tools/native_env.py image_identity; an overlay core
carries its OVERLAY.json beside it, whose plan digest and base set name it),
the values of the FN_* variables the module reads (tools/native_env.py
reads: images, opt-ins, fixtures), the SBCL and the Python that run it.  The
KEY is the SHA-256 of that list; two trees with the same bytes and the same
images ask for the same entry, and any change to any of it is a new key.

    python3 tools/native_verdicts.py key tests.test_native_owner
    python3 tools/native_verdicts.py lookup tests.test_native_owner   # exit 0 found, 1 absent
    python3 tools/native_verdicts.py record tests.test_native_owner --result LOG
    python3 tools/native_verdicts.py table

The store is FN_VERDICT_STORE (the same one tools/check_steps.py uses; on a
build box tools/hbox_native.sh sets BASE/.verdicts), else build/check-cache;
entries live at STORE/native-module/<key>.json.  `record` is what
tools/test_budget.py --one does at the end of a run (the FN_TEST_BUDGET_RESULT
line, with `cases`: every test's outcome); `lookup` is what
tools/hbox_native.sh's module step asks before it starts a module: a stored
verdict for the exact key is printed as the module's line, marked cached and
naming the run (box, time, log), and a stored red is replayed red -- the
reader opens the real failure through the named log.  A module whose stored
verdict is red re-runs ONLY its red cases (`lookup --red-cases`), and the
record of that run carries the green cases forward, marked `carried` with
the run they came from.  `--all` on hbox_native.sh (FN_NATIVE_ALL=1) runs
everything regardless.  A cached verdict satisfies no claim: a claim names
the run id of a live run (docs/testing.md).

Not keyed, by design: a tree's other files (a module that reads host/ or
books/ source for its image-free checks does so through tools/ and tests/
files that ARE keyed, and the image identity covers the built host); the
box's load; the clock.  A module that reads an environment variable the
scan does not see (through a helper outside tests/, or a computed name)
is keyed on fewer inputs than it depends on: name the variable with
`os.environ.get("FN_...")` in the module so the scan finds it.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import native_env  # noqa: E402

KIND = "native-module"
FIXED_INPUTS = ("tests/native_harness.py", "tools/test_budget.py", "tools/native_verdicts.py")
IMAGE_VARIABLE = "FN_NATIVE_"
# The image variables tools/hbox_native.sh exports (tools/native_env.py table)
# and the identity it computes: always in the key, read or not, since a
# helper outside the scan (tests/native_harness.py's deployed stack) may
# start any of them.
IMAGE_VARIABLES = ("FN_NATIVE_HOST", "FN_NATIVE_DEVELOPER_HOST", "FN_NATIVE_DTN_HOST",
                   "FN_NATIVE_DTN_DEVELOPER_HOST", "FN_NATIVE_BP_HOST", "FN_NATIVE_PROF_HOST",
                   "FN_NATIVE_IMAGE_SOURCE_SHA", "FN_NATIVE_CORE_SHA256",
                   "FN_NATIVE_LAUNCHER_SHA256", "FN_NATIVE_RUNTIME_SHA256",
                   "FN_SBCL", "FN_TEST_OPENSSL_BIN", "FN_TEST_OPENSSL")


def store_dir() -> Path:
    named = os.environ.get("FN_VERDICT_STORE")
    return Path(named) if named else ROOT / "build" / "check-cache"


def file_digest(path: Path) -> str:
    try:
        return native_env.sha256_file(path)
    except OSError:
        return "absent"


def helper_files(module: str) -> list[Path]:
    """The module's own file and every tests/ module it imports, transitively."""
    top = native_env.module_file(module)
    seen: list[Path] = []
    pending = [top]
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.append(path)
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        for helper in native_env.local_imports(text):
            try:
                pending.append(native_env.module_file(helper))
            except SystemExit:
                continue
    return sorted(seen)


def image_inputs(path: str) -> dict:
    """What identifies the image a variable names: its launcher, core and
    runtime digests, and an overlay record beside the core when there is one."""
    image = Path(path)
    found: dict = dict(native_env.image_identity(image))
    overlay = Path(str(image) + ".overlay.json")
    if not overlay.is_file():
        overlay = image.with_name("OVERLAY.json")
    if overlay.is_file():
        found["overlay"] = file_digest(overlay)
    if not found:
        found["absent"] = str(image)
    return found


def sbcl_identity() -> dict:
    path = os.environ.get("FN_SBCL") or ""
    if not path:
        from shutil import which  # noqa: PLC0415
        path = which("sbcl") or ""
    return {"path": path, "digest": file_digest(Path(path)) if path else "absent"}


def key_inputs(module: str, environ: dict | None = None) -> dict:
    env = os.environ if environ is None else environ
    files = {str(p.relative_to(ROOT)): file_digest(p) for p in helper_files(module)}
    for fixed in FIXED_INPUTS:
        files[fixed] = file_digest(ROOT / fixed)
    variables: dict[str, object] = {}
    for name in sorted({*native_env.reads(module), *IMAGE_VARIABLES}):
        value = env.get(name)
        if value is None:
            variables[name] = None
        elif name.startswith(IMAGE_VARIABLE) and name.endswith("_HOST"):
            variables[name] = image_inputs(value)
        else:
            variables[name] = value
    return {"module": module, "files": files, "env": variables,
            "sbcl": sbcl_identity(), "python": [sys.executable, sys.version]}


def key_of(inputs: dict) -> str:
    material = json.dumps(inputs, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(material.encode()).hexdigest()


def entry_path(key: str, store: Path | None = None) -> Path:
    return (store or store_dir()) / KIND / f"{key}.json"


def lookup(module: str, store: Path | None = None) -> tuple[str, dict | None]:
    inputs = key_inputs(module)
    key = key_of(inputs)
    path = entry_path(key, store)
    try:
        return key, json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return key, None


def box_name() -> str:
    try:
        return os.uname().nodename.split(".")[0]
    except (OSError, AttributeError):
        return "unknown"


def red_cases(entry: dict) -> list[str]:
    return [case for case, outcome in entry.get("cases", []) if outcome in ("FAIL", "ERROR")]


def record(module: str, result: dict, log: str = "", store: Path | None = None,
           carried_from: dict | None = None) -> tuple[str, Path]:
    """Store RESULT (a FN_TEST_BUDGET_RESULT record with `cases`) under the
    module's key now.  With CARRIED_FROM (the stored entry a red-cases-only run
    started from), every case that run did not execute keeps its stored
    outcome, marked carried."""
    inputs = key_inputs(module)
    key = key_of(inputs)
    cases = [[str(case), str(outcome)] for case, outcome in result.get("cases", [])]
    carried = []
    if carried_from is not None:
        ran = {case for case, _ in cases}
        for case, outcome in carried_from.get("cases", []):
            if case not in ran:
                cases.append([str(case), str(outcome)])
                carried.append(str(case))
    reds = [c for c, o in cases if o in ("FAIL", "ERROR")]
    entry = {"kind": KIND, "key": key, "module": module, "inputs": inputs,
             "cases": sorted(cases), "red": sorted(reds), "verdict": "FAILED" if reds else
             ("SKIPPED" if result.get("executed", 0) == 0 and not carried else "OK"),
             "tests": len(cases), "timings": result.get("timings", []),
             "skips": result.get("skips", []), "carried": sorted(carried),
             "carried_from": {"when": carried_from.get("when"), "box": carried_from.get("box"),
                              "log": carried_from.get("log")} if carried_from else None,
             "load_error": result.get("load_error"),
             "when": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "box": box_name(),
             "log": log, "source": os.environ.get("FN_NATIVE_IMAGE_SOURCE_SHA", "")}
    path = entry_path(key, store)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    temporary.write_text(json.dumps(entry, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, path)
    return key, path


def verdict_line(entry: dict) -> str:
    """The module's line as tools/test_budget.py --verdict prints one, plus
    where the verdict came from."""
    module = entry["module"]
    cases = entry.get("cases", [])
    reds = entry.get("red", [])
    skipped = sum(1 for _, o in cases if o == "skip")
    ran = len(cases) - skipped
    if entry.get("load_error"):
        text = f"{module}: FAILED (load error: {entry['load_error']})"
    elif reds:
        failures = sum(1 for _, o in cases if o == "FAIL")
        errors = sum(1 for _, o in cases if o == "ERROR")
        text = f"{module}: FAILED ({failures} failures, {errors} errors, {ran} ran, {skipped} skipped)"
    elif ran == 0:
        text = f"{module}: SKIPPED ({skipped} of {skipped})"
    else:
        text = f"{module}: OK ({ran} ran, {skipped} skipped)"
    carried = f", {len(entry['carried'])} carried" if entry.get("carried") else ""
    return (f"{text} [cached verdict {entry['key'][:12]}: run on {entry.get('box', '?')} "
            f"{entry.get('when', '?')}, log {entry.get('log') or '?'}{carried}]")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--store", default=None, help="default FN_VERDICT_STORE, else build/check-cache")
    sub = parser.add_subparsers(dest="action", required=True)
    p = sub.add_parser("key", help="print the module's key and its inputs")
    p.add_argument("module")
    p.add_argument("--inputs", action="store_true")
    p = sub.add_parser("lookup", help="print the stored verdict line; exit 1 when absent")
    p.add_argument("module")
    p.add_argument("--red-cases", action="store_true",
                   help="print the stored red case ids, one per line, instead of the line")
    p.add_argument("--json", action="store_true")
    p = sub.add_parser("record", help="store a FN_TEST_BUDGET_RESULT record from a --one log")
    p.add_argument("module")
    p.add_argument("--result", required=True, help="the --one log holding the result line")
    p.add_argument("--carry-from-key", default="")
    sub.add_parser("table", help="every stored module verdict")
    args = parser.parse_args(argv)
    store = Path(args.store) if args.store else None

    if args.action == "key":
        inputs = key_inputs(args.module)
        print(key_of(inputs))
        if args.inputs:
            print(json.dumps(inputs, indent=1, sort_keys=True))
        return 0
    if args.action == "lookup":
        key, entry = lookup(args.module, store)
        if entry is None:
            print(f"{args.module}: no stored verdict for key {key[:12]}", file=sys.stderr)
            return 1
        if args.red_cases:
            for case in red_cases(entry):
                print(case)
        elif args.json:
            print(json.dumps(entry, sort_keys=True))
        else:
            print(verdict_line(entry))
        return 0
    if args.action == "record":
        import test_budget  # noqa: PLC0415
        result = test_budget.read_result(Path(args.result))
        if result is None:
            print(f"native_verdicts: no {test_budget.RESULT_PREFIX.strip()} line in {args.result}",
                  file=sys.stderr)
            return 2
        carried = None
        if args.carry_from_key:
            try:
                carried = json.loads(entry_path(args.carry_from_key, store).read_text(encoding="utf-8"))
            except (OSError, ValueError):
                carried = None
        key, path = record(args.module, result, args.result, store, carried)
        print(f"{args.module}: verdict stored {key[:12]} -> {path}")
        return 0
    directory = (store or store_dir()) / KIND
    rows = []
    for path in sorted(directory.glob("*.json")):
        try:
            rows.append(json.loads(path.read_text(encoding="utf-8")))
        except (OSError, ValueError):
            continue
    rows.sort(key=lambda e: (e.get("module", ""), e.get("when", "")))
    for entry in rows:
        print(verdict_line(entry))
    print(f"{len(rows)} stored module verdict(s) under {directory}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

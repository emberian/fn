#!/usr/bin/env python3
"""The red set: every known red verdict, with what could flip it, as one file.

planning/design/iteration-architecture-2026-10-04.md section 2.2.  A lane
iterates on exactly the reds its change can reach, never the suite; for that
the reds have to exist as an object, each with an IMPACT SELECTOR (the paths
whose change could change the verdict).  This tool builds that object from
the runs' own records and answers which reds a diff reaches.

    python3 tools/reds.py collect [--check-steps build/check-steps] [--check-cache DIR]
                                  [--native LOG_OR_DIR ...] [--certify RUN_DIR ...]
                                  [--out build/reds.json]
    python3 tools/reds.py affected --since REV [--reds build/reds.json]
    python3 tools/reds.py delta OLD.json NEW.json
    python3 tools/reds.py table [--reds build/reds.json]

Three kinds, three sources, one record shape:

  check-step  a red row of tools/check_steps.py's results.jsonl (exit != 0,
              NOT RUN included: it is red for the gate).  Selector: the
              step's last traced inputs (build/check-cache/scope/<key>.json:
              files read or stat'ed, directories listed, git reads), exactly
              what `make check-lane CHECK_CHANGED_SINCE` scopes by.  A step
              never traced, or untraceable (ACL2, a shell), is reached by
              any change.
  test-case   a `... FAIL` / `... ERROR` line of a native module's log (the
              unittest -v transcript tools/test_budget.py --one keeps, as
              tools/hbox_native.sh files them under logs/).  Selector: the
              module file, tests/native_harness.py, and every repository
              path the module's source names (host/..., books/..., tools/...,
              tests/...).  An approximation until the world dump (section
              2.3) names the host functions a test drives; it errs wide.
  book        a `real` red of tools/certify_triage.py over a certify run
              directory (never a cascade).  Selector: the book's local
              include closure (tools/certs.py closure), what its certificate
              is keyed by.

`affected --since REV` takes the diff from REV (committed, uncommitted and
untracked, tools/check_steps.py changed_paths) and prints each red the diff
can reach with why, and the narrowest command that produces that kind of
verdict: the step's own command, the module under an overlay of the
published set, a lane certify of the book.  It runs nothing.  `delta` prints
the reds NEW has that OLD had not, the ones OLD had that NEW has not, and the
count unchanged, matched by kind and subject.

The red set is a lane's working object, never a gate: the batch's FORCE=1
pass and a READY stay live runs (docs/testing.md "What make check is").
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shlex
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import check_steps  # noqa: E402

DEFAULT_OUT = ROOT / "build" / "reds.json"
CASE_LINE = re.compile(r"^\s*(?:(?P<name>test_\w+) \((?P<id>[\w.]+)\))?.*? \.\.\. (?P<verdict>FAIL|ERROR)\s*$")
CASE_ID = re.compile(r"\((?P<id>tests\.[\w.]+)\)")
REPO_PATH = re.compile(r"\b((?:host|books|tools|tests|packaging|specs|planning)/[\w./-]+\.(?:lisp|py|sh|json|md|tsv))\b")
HARNESS = "tests/native_harness.py"


def rel(path: str | Path) -> str:
    """A repository-relative path, as the selectors and diffs name it."""
    text = str(path)
    found = check_steps.rel_path(text) if os.path.isabs(text) else text
    return found if found is not None else text


# ------------------------------------------------------------------ collect

def check_step_reds(steps_dir: Path, cache: Path) -> list[dict]:
    """One record per red row of the last `execute`, with its scope record."""
    found = []
    for row in check_steps.read_results(steps_dir):
        if row.get("exit", 0) == 0 or row.get("skipped"):
            continue
        command = shlex.split(row["command"])
        key = check_steps.step_key(command)
        scope = check_steps.load_json(cache / "scope" / f"{key}.json", None)
        selector = {"paths": [], "listed": [], "git": [], "untraced": True, "why": "never traced here"}
        if scope and scope.get("command") == command:
            selector = {"paths": sorted(scope.get("r", [])), "listed": sorted(scope.get("l", [])),
                        "git": scope.get("g", []), "untraced": bool(scope.get("x")),
                        "why": scope.get("x", "")}
        source = {"log": "", "when": "", "box": ""}
        cached = row.get("cached", "")
        match = re.search(r"run on (\S+) (\S+), log (\S+)", cached)
        if match:
            source = {"box": match.group(1), "when": match.group(2), "log": match.group(3)}
        found.append({"kind": "check-step", "subject": row["step"], "command": row["command"],
                      "exit": row["exit"], "finding": row.get("finding", ""),
                      "source": source, "selector": selector})
    return found


def native_red_cases(log: Path) -> list[tuple[str, str]]:
    """(case id, FAIL|ERROR) for every red case line of a module log; a
    subtest's line (indented, `(x='y')`) names its case once."""
    found: list[tuple[str, str]] = []
    previous = ""
    for line in log.read_text(encoding="utf-8", errors="replace").splitlines():
        match = CASE_LINE.match(line)
        if match:
            case = match.group("id")
            if not case:
                here = CASE_ID.search(line) or CASE_ID.search(previous)
                case = here.group("id") if here else ""
            if case and (case, match.group("verdict")) not in found:
                found.append((case, match.group("verdict")))
        if line.strip():
            previous = line
    return found


def module_selector(module: str) -> dict:
    """The module file, the harness, and every repository path its source names."""
    path = ROOT / (module.replace(".", "/") + ".py")
    paths = {rel(path), HARNESS}
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return {"paths": sorted(paths), "listed": [], "git": [], "untraced": False,
                "why": "module file absent"}
    for named in REPO_PATH.findall(text):
        if (ROOT / named).is_file():
            paths.add(named)
    return {"paths": sorted(paths), "listed": [], "git": [], "untraced": False, "why": ""}


def native_reds(logs: list[Path]) -> list[dict]:
    found = []
    for log in logs:
        for case, verdict in native_red_cases(log):
            module = ".".join(case.split(".")[:2]) if case.startswith("tests.") else case
            found.append({"kind": "test-case", "subject": case, "module": module,
                          "command": f"python3 -m unittest -v {case}", "exit": 1,
                          "finding": verdict, "source": {"log": str(log), "when": "", "box": ""},
                          "selector": module_selector(module)})
    return found


def module_logs(named: list[str]) -> list[Path]:
    """Module logs: each file named, or every `test-tests.*.log` under a directory."""
    logs: list[Path] = []
    for word in named:
        path = Path(word)
        if path.is_dir():
            logs.extend(sorted(path.glob("test-tests.*.log")))
        elif path.is_file():
            logs.append(path)
    return logs


def book_selector(book: str) -> dict:
    """The book's local include closure: what its certificate is keyed by."""
    import certs  # noqa: PLC0415  (beside this file)
    name = book[:-5] if book.endswith(".lisp") else book
    try:
        closure = certs.closure(ROOT, name)
    except Exception as error:  # noqa: BLE001  a book that does not read: reached by itself
        return {"paths": [f"{name}.lisp"], "listed": [], "git": [], "untraced": False,
                "why": f"closure unreadable: {error}"[:120]}
    paths = sorted({f"{n}.lisp" if not n.endswith(".lisp") else n for n in closure})
    return {"paths": paths, "listed": [], "git": [], "untraced": False, "why": ""}


def certify_reds(runs: list[Path]) -> list[dict]:
    import certify_triage  # noqa: PLC0415
    found = []
    for run in runs:
        for row in certify_triage.triage_run(run):
            if row.get("kind") != "real":
                continue
            book = row["book"]
            found.append({"kind": "book", "subject": book,
                          "command": f"python3 tools/farm.py submit auto --lane --affected-by {book}.lisp",
                          "exit": 1, "finding": (row.get("detail") or "")[:200],
                          "source": {"log": str(run), "when": "", "box": ""},
                          "selector": book_selector(book)})
    return found


def collect(steps_dir: Path | None, cache: Path, native: list[str], certify: list[str]) -> dict:
    reds: list[dict] = []
    if steps_dir is not None and (steps_dir / check_steps.RESULTS).is_file():
        reds += check_step_reds(steps_dir, cache)
    reds += native_reds(module_logs(native))
    reds += certify_reds([Path(r) for r in certify])
    return {"head": check_steps.head_sha(), "reds": reds}


# ----------------------------------------------------------------- affected

def reached(red: dict, changed: check_steps.Changes) -> str:
    """Why the change can flip this red, "" when it cannot."""
    selector = red["selector"]
    if red["kind"] == "check-step":
        record = None
        if not selector.get("why") == "never traced here":
            record = {"command": shlex.split(red["command"]), "x": selector.get("why", "") if
                      selector.get("untraced") else "", "r": selector["paths"],
                      "l": selector["listed"], "g": selector["git"]}
        return check_steps.reached_by(record, shlex.split(red["command"]), changed)
    if selector.get("untraced"):
        return f"untraceable ({selector.get('why', '')[:50]})"
    inputs = set(selector["paths"])
    for path in changed.paths:
        if path in inputs:
            return f"{path} changed"
    for where in sorted(set(selector["listed"]) & changed.listed):
        return f"{where}/ listing changed"
    return ""


def narrowest(red: dict, image_set: str) -> str:
    if red["kind"] == "test-case":
        module = red.get("module", red["subject"])
        if image_set:
            return f"tools/hbox_native.sh --image-set {image_set} --overlay . {module}"
        return f"tools/hbox_native.sh --image-set SHA --overlay . {module}   (or {red['command']} with an image)"
    return red["command"]


def affected(reds: dict, since: str, image_set: str = "") -> list[tuple[dict, str]]:
    changed = check_steps.changed_paths(since)
    found = []
    for red in reds["reds"]:
        why = reached(red, changed)
        if why:
            found.append((red, why))
    return found


# -------------------------------------------------------------------- delta

def identity(red: dict) -> tuple[str, str]:
    return (red["kind"], red["subject"])


def delta(old: dict, new: dict) -> tuple[list[dict], list[dict], int]:
    before = {identity(r): r for r in old["reds"]}
    after = {identity(r): r for r in new["reds"]}
    fixed = [before[k] for k in sorted(before.keys() - after.keys())]
    appeared = [after[k] for k in sorted(after.keys() - before.keys())]
    return appeared, fixed, len(before.keys() & after.keys())


# -------------------------------------------------------------------- print

def line_of(red: dict, extra: str = "") -> str:
    finding = (red.get("finding") or "").strip()
    text = f"  {red['kind']:10} {red['subject']}"
    if finding:
        text += f"  {finding[:90]}"
    if extra:
        text += f"  [{extra}]"
    return text


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="action", required=True)
    p = sub.add_parser("collect")
    p.add_argument("--check-steps", default=str(ROOT / "build" / "check-steps"))
    p.add_argument("--check-cache", default=os.environ.get("FN_VERDICT_STORE")
                   or str(check_steps.DEFAULT_CACHE))
    p.add_argument("--native", nargs="*", default=[], metavar="LOG_OR_DIR")
    p.add_argument("--certify", nargs="*", default=[], metavar="RUN_DIR")
    p.add_argument("--out", default=str(DEFAULT_OUT))
    p = sub.add_parser("affected")
    p.add_argument("--since", required=True, metavar="REV")
    p.add_argument("--reds", default=str(DEFAULT_OUT))
    p.add_argument("--image-set", default="", metavar="SHA")
    p = sub.add_parser("delta")
    p.add_argument("old")
    p.add_argument("new")
    p = sub.add_parser("table")
    p.add_argument("--reds", default=str(DEFAULT_OUT))
    args = parser.parse_args(argv)

    if args.action == "collect":
        reds = collect(Path(args.check_steps), Path(args.check_cache), args.native, args.certify)
        out = Path(args.out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(reds, indent=1, sort_keys=True) + "\n", encoding="utf-8")
        kinds = {}
        for red in reds["reds"]:
            kinds[red["kind"]] = kinds.get(red["kind"], 0) + 1
        print(f"reds: {len(reds['reds'])} at {reds['head']} -> {out} "
              f"({', '.join(f'{k} {v}' for k, v in sorted(kinds.items())) or 'none'})")
        return 0
    if args.action == "table":
        reds = json.loads(Path(args.reds).read_text(encoding="utf-8"))
        print(f"reds: {len(reds['reds'])} at {reds['head']}")
        for red in reds["reds"]:
            print(line_of(red))
        return 0
    if args.action == "delta":
        old = json.loads(Path(args.old).read_text(encoding="utf-8"))
        new = json.loads(Path(args.new).read_text(encoding="utf-8"))
        appeared, fixed, same = delta(old, new)
        print(f"reds delta {old['head']} -> {new['head']}: {len(appeared)} new, {len(fixed)} fixed, "
              f"{same} unchanged")
        for red in appeared:
            print("NEW" + line_of(red))
        for red in fixed:
            print("FIXED" + line_of(red))
        return 1 if appeared else 0
    reds = json.loads(Path(args.reds).read_text(encoding="utf-8"))
    hits = affected(reds, args.since, args.image_set)
    print(f"reds affected by the diff since {args.since}: {len(hits)} of {len(reds['reds'])}")
    for red, why in hits:
        print(line_of(red, why))
        print(f"      run: {narrowest(red, args.image_set)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

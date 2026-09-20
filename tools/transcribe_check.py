#!/usr/bin/env python3
"""Check the campaign's cuts against the byte model's programs.

`AGENTS.md`: "Every process-death cut is a model crash point.  A test that
kills the host at a boundary the model cannot express is a fidelity defect,
not a passing test."  Until now that was checked by reading a prose column of
`tests/campaign/cuts.py`.  This tool checks it mechanically, in both
directions, against `books/byte-store-programs.lisp`:

* every `faults.at("<name>")` site the campaign kills at is a `:cut` step of
  the model program that transcribes its host function -- otherwise it is a
  **fidelity defect** and this tool exits non-zero;
* every `:cut` step of a model program is a `faults.at` site of that host
  function -- otherwise it is a **missing host cut**, a boundary the model
  says the campaign should kill at and the host offers no way to (crash model
  v2 §2.3, packet P2's host half);
* the sequence of durable syscalls in the host function equals the sequence
  of syscall steps in the model program, so a moved host line fails the
  table (crash model v2 §2.3, second rule).  This last comparison is
  ADVISORY, not a gate, and `--strict` is what makes it one: the host
  sequence is read in source-line order over every branch of the function,
  while a model program is one path through it, so an `except` cleanup, a
  reconciliation branch or a helper call shows as drift that is not drift.
  Read each line before acting on it; the two that were real when this tool
  was written were `checkpoint:select`s stage unlink, which the model
  program had dropped, and `store:initialize`, whose three `mkdir`s and the
  staged files it publishes live in `_publish_initial_file`.

A host write path with no model program at all is listed under
UNMODELLED_PATHS with the reason, and is reported, not silently skipped.
"""
from __future__ import annotations

import argparse
import ast
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tests.campaign import cuts as cuts_module  # noqa: E402

PROGRAMS_BOOK = ROOT / "books" / "byte-store-programs.lisp"

# (component, host function) -> the model program that transcribes it.
TRANSCRIPTIONS = {
    ("store", "advance_frontier"): "fn-bs-frontier-program",
    ("store", "publish"): "fn-bs-record-program",
    ("store", "finish"): "fn-bs-finish-program",
    ("store", "recover"): "fn-bs-recover-program",
    ("store", "initialize"): "fn-bs-init-program",
    ("workflow", "publish"): "fn-bs-workflow-program",
    ("workflow", "stage_inbound"): "fn-bs-inbox-program",
    ("receipt", "publish"): "fn-bs-receipt-program",
    ("checkpoint", "publish"): "fn-bs-checkpoint-publish-program",
    ("checkpoint", "select"): "fn-bs-checkpoint-select-program",
}

# Cuts of a transcribed function that the program deliberately does not
# carry, each with the reason.  A name here is NOT a fidelity defect; a name
# missing from both here and the program IS one.
DECLARED_ELSEWHERE = {
    ("workflow", "inbound-reconciled"):
        "the reconciliation branch is fn-bs-inbox-reconcile-program",
    ("workflow", "inbound-deleted"):
        "the BPA delete is a transport side effect outside the storage model",
    ("workflow", "inbound-retry-deleted"):
        "retry_staged_delete issues no storage syscall; the delete is transport",
}

# Host write paths with no model program, each with the reason.
UNMODELLED_PATHS = {
    ("receive", "receive_bpa_request"):
        "composite receiver: its cuts are store and journal cuts in sequence, "
        "not a storage program of its own (crash model v2 §3.4 covers the "
        "journals it drives)",
    ("receive", "_durably_decide"):
        "receipt decision machine over the receipt journal; its storage "
        "boundary is receipt:publish",
    ("workflow", "retry_staged_delete"):
        "retry_staged_delete issues no storage syscall: its only boundary is "
        "the BPA delete, a transport side effect outside the storage model",
    ("receive", "_delete_after_decision"):
        "BPA delete only: a transport side effect outside the storage model",
}

SYSCALL_STEPS = {":create", ":write-all", ":fsync-file", ":fsync-dir",
                 ":link", ":rename", ":unlink", ":mkdir"}

# Host call -> the model step it is.  os.close is exempt by §2.3: it has no
# durability effect and the programs list no step for it.
HOST_SYSCALLS = {
    "link": ":link", "replace": ":rename", "unlink": ":unlink",
    "mkdir": ":mkdir", "durable_barrier": ":fsync-file",
    "fsync_file": ":fsync-file", "fsync_regular": ":fsync-file",
    "fsync_dir": ":fsync-dir", "write_all": ":write-all",
}


def program_steps(text: str) -> dict[str, list[tuple[str, str]]]:
    """(:cut "name") and syscall steps of each (defun fn-bs-*-program ...)."""
    programs: dict[str, list[tuple[str, str]]] = {}
    for match in re.finditer(r"^\(defun (fn-bs-[a-z-]*program) ", text, re.M):
        name = match.group(1)
        start = match.start()
        end = text.find("\n(", start + 1)
        body = text[start:end if end > 0 else len(text)]
        steps: list[tuple[str, str]] = []
        for step in re.finditer(r"\(list (:[a-z-]+)(?:\s+\"([^\"]*)\")?", body):
            kind = step.group(1)
            if kind == ":cut":
                steps.append((":cut", step.group(2) or ""))
            elif kind in SYSCALL_STEPS:
                steps.append((kind, ""))
        programs[name] = steps
    return programs


def host_functions() -> dict[tuple[str, str], list[tuple[str, str]]]:
    """(component, function) -> the ordered fault points and syscalls."""
    found: dict[tuple[str, str], list[tuple[str, str]]] = {}
    for component, module in cuts_module.COMPONENT_MODULES.items():
        tree = ast.parse(module.read_text(), filename=str(module))
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            events: list[tuple[int, str, str]] = []
            for inner in ast.walk(node):
                if not isinstance(inner, ast.Call):
                    continue
                call = inner.func
                if not isinstance(call, (ast.Attribute, ast.Name)):
                    continue
                name = call.attr if isinstance(call, ast.Attribute) else call.id
                if name == "at":
                    owner = call.value if isinstance(call, ast.Attribute) else None
                    owner_name = (owner.attr if isinstance(owner, ast.Attribute)
                                  else owner.id if isinstance(owner, ast.Name)
                                  else "")
                    if owner_name == "faults" and inner.args:
                        events.append((inner.lineno, ":cut", inner.args[0].value))
                elif name in HOST_SYSCALLS:
                    events.append((inner.lineno, HOST_SYSCALLS[name], ""))
                elif name == "open" and any(
                        isinstance(arg, ast.Attribute) and "O_CREAT" in arg.attr
                        for arg in ast.walk(inner)):
                    events.append((inner.lineno, ":create", ""))
            if events:
                key = (component, node.name)
                found[key] = [(kind, value)
                              for _, kind, value in sorted(events)]
    return found


def check() -> dict:
    programs = program_steps(PROGRAMS_BOOK.read_text())
    hosts = host_functions()
    report = {"fidelity_defects": [], "missing_host_cuts": [],
              "syscall_drift": [], "unmodelled": [], "checked": 0}

    for key, program_name in sorted(TRANSCRIPTIONS.items()):
        component, function = key
        steps = programs.get(program_name)
        if steps is None:
            report["fidelity_defects"].append(
                "{}:{} names {} and no such program exists".format(
                    component, function, program_name))
            continue
        model_cuts = [value for kind, value in steps if kind == ":cut"]
        host_events = hosts.get(key, [])
        host_cuts = [value for kind, value in host_events if kind == ":cut"]
        report["checked"] += 1
        for name in host_cuts:
            if name in model_cuts:
                continue
            if (component, name) in DECLARED_ELSEWHERE:
                continue
            report["fidelity_defects"].append(
                "{}:{} is killed at in {}() and is no :cut of {}".format(
                    component, name, function, program_name))
        for name in model_cuts:
            if name not in host_cuts:
                report["missing_host_cuts"].append(
                    "{}: {} is a :cut of {} and no faults.at of {}()".format(
                        component, name, program_name, function))
        model_calls = [kind for kind, _ in steps if kind in SYSCALL_STEPS]
        host_calls = [kind for kind, _ in host_events if kind in SYSCALL_STEPS]
        if model_calls != host_calls:
            report["syscall_drift"].append(
                "{}:{}() issues {} and {} has {}".format(
                    component, function, host_calls, program_name, model_calls))

    for key in sorted(hosts):
        component, function = key
        if key in TRANSCRIPTIONS:
            continue
        cut_names = [value for kind, value in hosts[key] if kind == ":cut"]
        if not cut_names:
            continue
        if key in UNMODELLED_PATHS:
            report["unmodelled"].append("{}:{}(): {} -- {}".format(
                component, function, ",".join(cut_names),
                UNMODELLED_PATHS[key]))
            continue
        report["fidelity_defects"].append(
            "{}:{}() is killed at ({}) and no model program transcribes "
            "it".format(component, function, ",".join(cut_names)))
    return report


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", type=Path, default=None)
    parser.add_argument("--strict", action="store_true",
                        help="also fail on missing host cuts and syscall drift")
    args = parser.parse_args(argv)
    report = check()
    for key in ("fidelity_defects", "missing_host_cuts", "syscall_drift",
                "unmodelled"):
        for line in report[key]:
            print("{}: {}".format(key.replace("_", "-"), line))
    print("transcriptions={} fidelity-defects={} missing-host-cuts={} "
          "syscall-drift={} unmodelled={}".format(
              report["checked"], len(report["fidelity_defects"]),
              len(report["missing_host_cuts"]), len(report["syscall_drift"]),
              len(report["unmodelled"])))
    if args.json:
        args.json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    if report["fidelity_defects"]:
        return 1
    if args.strict and (report["missing_host_cuts"] or report["syscall_drift"]):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Every tests/*.sh scenario witness is cited and has a runner (tooling-truth-2, 2026-09-29).

Nothing ran most tests/*.sh: tests/native_owner_publication.lisp, SCN-027's
witness, broke unseen (correctness-remainder-7), and on 2026-09-29 five of
the sbcl-only witnesses failed at load.  Each script now says what it is in a
header line `# witness: CLASS`, and this check holds it to that:

  raw          run by tests.test_native_raw_scripts (every run of the tooling
               tests), with no image: the module must list it.
  needs-image  needs a built image (FN_NATIVE_HOST ...): run ONCE in the
               prerelease convergence checklist, which must name it
               (planning/release-v6.6.0.md); never silently skipped.
  needs-acl2   needs the certified tree and an ACL2 (FN_ACL2): the same.
  module M     run by the test module M (tests/M.py names the script).
  helper       not a witness: a driver another test or tool names.

A witness (every class but helper) must be cited by a scenario-catalog row
(tests/scenarios/catalog.json names the script or a tests/*.lisp it drives).
KNOWN names an exception with why; it only shrinks (an entry that now
passes, or names a script that is gone, is red).  Mechanical; exit 0 or 1.
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MARK = re.compile(r"^# witness: (raw|needs-image|needs-acl2|helper|module (tests\.\S+))\s*$", re.M)
DRIVES = re.compile(r"tests/[A-Za-z0-9_.-]+\.lisp")
CHECKLIST = "planning/release-v6.6.0.md"

# script -> why it is allowed to fail a rule here.  Shrink-only.  The 17
# witnesses no catalog row cited at the first run (2026-09-29) are cited by
# the scenario each witnesses (tooling-truth-3); the list is empty.
KNOWN: dict[str, str] = {}


def findings(root: pathlib.Path = ROOT, known: dict[str, str] = KNOWN) -> list[str]:
    catalog = (root / "tests/scenarios/catalog.json").read_text(encoding="utf-8")
    checklist = (root / CHECKLIST).read_text(encoding="utf-8") if (root / CHECKLIST).is_file() else ""
    raw_runner = root / "tests/test_native_raw_scripts.py"
    raw_text = raw_runner.read_text(encoding="utf-8") if raw_runner.is_file() else ""
    others = {p: p.read_text(encoding="utf-8", errors="replace")
              for pattern in ("tests/*.py", "tests/*.mjs", "tools/*.py", "tools/*.sh", "packaging/*.sh")
              for p in root.glob(pattern)}
    out: list[str] = []
    scripts = sorted(root.glob("tests/*.sh"))
    for script in scripts:
        rel = str(script.relative_to(root))
        text = script.read_text(encoding="utf-8", errors="replace")
        problems = []
        mark = MARK.search(text)
        if not mark:
            problems.append("no `# witness: CLASS` header line (raw, needs-image, needs-acl2, "
                            "module tests.M, helper)")
        else:
            kind, module = mark.group(1).split()[0], mark.group(2)
            if kind == "raw" and 'RAW_MARK = "# witness: raw"' not in raw_text:
                problems.append("raw, but tests/test_native_raw_scripts.py no longer runs "
                                "the scripts marked raw")
            if kind in ("needs-image", "needs-acl2") and rel not in checklist:
                problems.append(f"{kind}, but the convergence checklist ({CHECKLIST}) does not name it")
            if kind == "module":
                path = root / (module.replace(".", "/") + ".py")
                if not path.is_file() or script.name not in path.read_text(encoding="utf-8"):
                    problems.append(f"module {module}, which does not name it")
            if kind == "helper" and not any(script.name in t for p, t in others.items()
                                            if p != script):
                problems.append("helper, but no test or tool names it")
            if kind != "helper" and rel not in catalog and \
                    not any(d in catalog for d in DRIVES.findall(text)):
                problems.append("no scenario-catalog row cites it or a tests/*.lisp it drives")
        if problems and rel not in known:
            out += [f"{rel}: {p}" for p in problems]
        if not problems and rel in known:
            out.append(f"{rel}: KNOWN but passes now: drop its KNOWN entry")
    present = {str(s.relative_to(root)) for s in scripts}
    out += [f"{k}: KNOWN but gone: drop its KNOWN entry" for k in sorted(known) if k not in present]
    return out


def main() -> int:
    found = findings()
    for line in found:
        print("witness_check: " + line)
    if not found:
        print(f"witness_check: {len(list(ROOT.glob('tests/*.sh')))} tests/*.sh witnesses, "
              f"each cited and run in its class ({len(KNOWN)} KNOWN)")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())

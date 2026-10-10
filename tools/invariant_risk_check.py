#!/usr/bin/env python3
"""tools/invariant_risk_check.py [--ir build/core/core.json] [--baseline FILE] [--list]

No host entry declared in the image's interface registry carries ACL2's
`invariant-risk' property in the image world while its *1* code runs its
body (any class but :common-lisp-compliant; see `interpreted').

Why.  A command-path adapter that uses `with-local-stobj' of a def-buffer
stobj makes ACL2 mark its :program caller `invariant-risk', and the whole chain
above runs through the *1* interpreter with a guard check per call instead of
as raw Lisp (Builder C's profile: POST 10.7 s, linear in the store, one guard
walking every catalog handle).  The host sets check-invariant-risk t
(host/native/io.lisp), so the cost is paid.

What it reads.  The declared entries come from tools/interface_emit.declarations
(the registry half of definterface, not planning/interfaces.json, which is a
generated file).  The image world's verdict is the extractor's own export,
build/core/core.json (tools/extract/core.sh, step 1 of the extraction gate):
tools/extract/frontend.lisp writes `invariant_risk' per :defun as
(getpropc fn 'invariant-risk nil (w state)) in the image world.  No ACL2 process
is started here.  Placement: the extraction gate's core step produces the IR in
the same invocation, so this belongs after it (gate.py is not wired yet: see
tools/invariant_risk_baseline.json).

Fail closed.  An absent, empty, unparseable or functionless IR is a FAIL with a
reason; so is a registry with no declarations.  A declared entry the IR does not
contain was not measured: it is counted and named in the summary (the IR holds
the extractor's closure, which need not cover every declaration) but is not a
verdict either way.

Baseline.  tools/invariant_risk_baseline.json "marked" maps an entry name to
"owner: why".  The list only shrinks: a marked entry not listed fails, a listed
entry no longer marked fails (remove it).  Exit 0 only when both hold.
"""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

IR = ROOT / "build" / "core" / "core.json"
BASELINE = ROOT / "tools" / "invariant_risk_baseline.json"


def short(name: str) -> str:
    """The symbol-name part of a package-qualified IR name, upcased."""
    return name.rsplit("::", 1)[-1].upper()


def load_ir(path: Path):
    """(functions-by-short-name, problems)."""
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as ex:
        return None, ["the image world's export {} is unreadable ({})".format(path, ex)]
    if not text.strip():
        return None, ["the image world's export {} is empty".format(path)]
    try:
        doc = json.loads(text)
    except ValueError as ex:
        return None, ["the image world's export {} does not parse ({})".format(path, ex)]
    fns = doc.get("functions") if isinstance(doc, dict) else None
    if not isinstance(fns, list) or not fns:
        return None, ["the image world's export {} lists no functions".format(path)]
    by_name: dict[str, list[dict]] = {}
    for f in fns:
        if not isinstance(f, dict) or not isinstance(f.get("name"), str):
            return None, ["the image world's export {} has a function row without a name".format(path)]
        by_name.setdefault(short(f["name"]), []).append(f)
    return by_name, []


def callees(term, out: set) -> None:
    if not isinstance(term, list) or not term:
        return
    if term[0] == "c":
        out.add(short(term[1]))
        for a in term[2]:
            callees(a, out)
    elif term[0] == "l":
        callees(term[2], out)
        for a in term[3]:
            callees(a, out)


def cause(rows: list[dict], by_name: dict) -> list[str]:
    """Direct callees of the marked entry that are stobj-using or marked
    themselves: where with-local-stobj / a stobj-updating function enters."""
    found: set = set()
    for row in rows:
        if "body" in row:
            callees(row["body"], found)
    out = []
    for c in sorted(found):
        for f in by_name.get(c, []):
            if f.get("invariant_risk"):
                out.append(c.lower() + " (itself invariant-risk)")
            elif any(f.get("stobjs_in") or []) or any(f.get("stobjs_out") or []):
                out.append(c.lower() + " (stobj: {})".format(
                    ",".join(sorted({s.lower() for s in (f.get("stobjs_in") or []) + (f.get("stobjs_out") or [])
                                     if s}))))
    return out


VERIFIED = "common-lisp-compliant"


def interpreted(row: dict) -> bool:
    """A marked row whose *1* runs its body: any class but guard-verified.
    ACL2 (defuns.lisp put-invariant-risk; translate.lisp, the **1*-as-raw*
    note): the *1* code of an invariant-risk :program function evaluates its
    callees as *1* with their guards checked, the cost C measured; a
    guard-verified entry's *1* checks its own guard and then runs raw Lisp
    (ACL2 marks one only when its guard is not t, remove-guard-t, so that the
    guard check is not skipped), so under guard-checking t the mark costs it
    nothing.  A row without a class is counted as interpreted (fail closed)."""
    return bool(row.get("invariant_risk")) and row.get("class") != VERIFIED


def verified_marked(decls: list[dict], by_name: dict) -> list[str]:
    """Declared entries marked in the world but guard-verified (reported, not failed)."""
    return sorted(d["name"] for d in decls
                  if any(r.get("invariant_risk") and r.get("class") == VERIFIED
                         for r in by_name.get(d["name"].upper(), [])))


def measure(decls: list[dict], by_name: dict) -> tuple[dict, list[str]]:
    """({entry: where-and-cause} for marked declared entries whose *1* is
    interpreted, unmeasured names)."""
    marked, unmeasured = {}, []
    for d in decls:
        rows = by_name.get(d["name"].upper())
        if not rows:
            unmeasured.append(d["name"])
            continue
        if any(interpreted(r) for r in rows):
            via = cause(rows, by_name)
            marked[d["name"]] = "{}:{}{}".format(
                d["source"], d["line"], "; via " + ", ".join(via) if via else "")
    return marked, unmeasured


def check(decls: list[dict], ir: Path, baseline: dict) -> tuple[list[str], dict, list[str]]:
    """(problems, marked, unmeasured)."""
    if not decls:
        return ["the interface registry declares no entries (tools/interface_emit.py read nothing)"], {}, []
    by_name, problems = load_ir(ir)
    if problems:
        return problems, {}, []
    marked, unmeasured = measure(decls, by_name)
    listed = baseline.get("marked", {})
    for name in sorted(marked):
        if name not in listed:
            problems.append(
                "{} ({}): a declared host entry carries invariant-risk in the image world, so the "
                "chain above it runs through *1* with a guard check per call; remove the "
                "with-local-stobj / stobj update from the entry's own body (move it below a "
                "guard-verified :logic function), or list it under \"marked\" in "
                "tools/invariant_risk_baseline.json with owner and why (that list only shrinks)"
                .format(name, marked[name]))
    for name in sorted(set(listed) - set(marked)):
        problems.append("{}: listed under \"marked\" in tools/invariant_risk_baseline.json but not a "
                        "marked declared entry now: remove its entry (the list only shrinks)".format(name))
    return problems, marked, unmeasured


def load_baseline(path: Path = BASELINE) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--ir", default=str(IR))
    p.add_argument("--baseline", default=str(BASELINE))
    p.add_argument("--list", action="store_true", help="print every marked declared entry")
    a = p.parse_args(argv)
    import interface_emit
    try:
        baseline = load_baseline(Path(a.baseline))
    except (OSError, ValueError) as ex:
        print("invariant-risk: FAIL: baseline {} unreadable ({})".format(a.baseline, ex))
        return 1
    decls = interface_emit.declarations()
    problems, marked, unmeasured = check(decls, Path(a.ir), baseline)
    if a.list:
        for name, where in sorted(marked.items()):
            print("MARKED {} {}".format(name, where))
    for line in problems:
        print("invariant-risk: " + line)
    if problems:
        print("invariant-risk: FAIL ({} problem(s))".format(len(problems)))
        return 1
    by_name, _ = load_ir(Path(a.ir))
    print("invariant-risk: PASS ({} declared, {} marked and baselined, {} marked but guard-verified, "
          "{} not in the IR, unmeasured)"
          .format(len(decls), len(marked), len(verified_marked(decls, by_name)), len(unmeasured)))
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""The gap report: every open obligation has exactly one disposition (SOP).

    python3 tools/coverage_gap.py [--check] [--root DIR] [--claims FILE]
        [--lanes DIR] [--acks FILE] [--json]

Spec: build/coordinator/COORDINATOR-SOP.md (the comprehensiveness loop).  Run
it at each integrator regen, after planning/repair/STATUS.md is regenerated.

Inputs, each read in the format its producer writes (nothing is guessed):

* planning/repair/items/*.json -- the repair ledger, one JSON object per item
  (planning/repair/repair.py writes them; its ``report`` writes STATUS.md).
  ``state`` is open | in-progress | ready (open obligations), landed, refuted,
  duplicate, or deferred.  The report also checks that STATUS.md's
  ``Items: N`` equals the item count, i.e. that the regen ran first.
* build/coordinator/claims.jsonl -- the workq registry
  (build/coordinator/workq.py): rows {"op": "claim"|"done"|"release", "id",
  "worker", ...}.  An id is held iff its last row is a ``claim``.  The file is
  coordinator-local and untracked, so it is found by walking up from --root
  (``<ancestor>/build/coordinator/claims.jsonl`` or
  ``<ancestor>/coordinator/claims.jsonl``) unless --claims names it.
* build/lanes/<lane>/ -- a live lane is a worktree directory there (lanes are
  reaped when they end, SOP close-out); found beside the coordinator dir
  unless --lanes names it.
* planning/repair/ACKS.md -- one line per deliberately-unfixed item:
  ``id <em dash> reason <em dash> who/what un-parks it``.
* tests/scenarios/catalog.json -- the scenario matrix; a scenario whose
  ``implementation`` declares ``"native": true`` is a declared native
  execution, recorded by ``implementation.log`` / ``implementation.record``.
* tests/scenarios/tiers.tsv -- the native modules per tier
  (``TIER<TAB>module<TAB>tests.MODULE[.Class]``); a module is recorded as run
  when a catalog scenario cites a log naming it.

Dispositions of an open item (state open | in-progress | ready), first match:
IN-FLIGHT (a live workq claim, or an in-progress/ready item whose owner is a
live lane), PARKED (an ACK line, or state ``deferred`` with a written note),
else UNOWNED.  state landed is LANDED; refuted/duplicate/closed are CLOSED.  Exit 1
under --check when any UNOWNED item or NEVER-RUN scenario/module has no ACK;
exit 1 always when an input is unreadable or malformed (a finding naming
file:line) -- nothing is silently skipped.
"""
import argparse
import json
import re
import sys
from pathlib import Path

OPEN = ("open", "in-progress", "ready")
CLOSED = ("refuted", "duplicate", "closed")
DASH = "—"


class Findings(list):
    def add(self, where, why):
        self.append(f"{where}: {why}")


def read_text(path, findings):
    try:
        return Path(path).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        findings.add(path, f"unreadable input ({e})")
        return None


def load_items(root, findings):
    d = Path(root) / "planning/repair/items"
    if not d.is_dir():
        findings.add(d, "ledger directory missing")
        return []
    items = []
    for f in sorted(d.glob("*.json")):
        text = read_text(f, findings)
        if text is None:
            continue
        try:
            item = json.loads(text)
            if not isinstance(item, dict):
                raise ValueError("not an object")
            for k in ("id", "state"):
                if not isinstance(item.get(k), str) or not item[k]:
                    raise ValueError(f"missing string field {k}")
        except ValueError as e:
            findings.add(f, f"malformed item ({e})")
            continue
        items.append(item)
    status = Path(root) / "planning/repair/STATUS.md"
    text = read_text(status, findings)
    if text is not None:
        m = re.search(r"^Generated .*Items: (\d+)\.", text, re.M)
        if not m:
            findings.add(status, "no 'Items: N' line (not a generated STATUS.md)")
        elif int(m.group(1)) != len(items):
            findings.add(status, f"stale: says {m.group(1)} items, ledger has {len(items)} "
                                 "(regenerate with repair.py report first)")
    return items


def load_acks(path, findings):
    """{id: (reason, unparker)}; every non-comment line must be well formed."""
    acks = {}
    text = read_text(path, findings)
    for n, line in enumerate((text or "").splitlines(), 1):
        if not line.strip() or line.lstrip().startswith(("#", "<!--")):
            continue
        parts = [p.strip() for p in line.split(DASH)]
        if len(parts) != 3 or not all(parts) or " " in parts[0]:
            findings.add(f"{path}:{n}", f"malformed ACK line (want 'id {DASH} reason {DASH} "
                                        f"who/what un-parks it'): {line.strip()[:80]}")
            continue
        if parts[0] in acks:
            findings.add(f"{path}:{n}", f"duplicate ACK for {parts[0]}")
            continue
        acks[parts[0]] = (parts[1], parts[2])
    return acks


def find_coordinator(root, claims, lanes):
    """(claims_path, lanes_dir) by walking up from root unless given."""
    if claims is None or lanes is None:
        for anc in [Path(root).resolve(), *Path(root).resolve().parents]:
            for c in (anc / "build/coordinator", anc / "coordinator"):
                if (c / "claims.jsonl").exists():
                    claims = claims or str(c / "claims.jsonl")
                    lanes = lanes or str(c.parent / "lanes")
                    break
            else:
                continue
            break
    return claims, lanes


def load_claims(path, findings):
    """{id: worker} for ids whose last workq row is a claim."""
    if not path:
        findings.add("claims.jsonl", "workq registry not found (pass --claims)")
        return {}
    text = read_text(path, findings)
    last = {}
    for n, line in enumerate((text or "").splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
            last[row["id"]] = (row["op"], row.get("worker", ""))
        except (ValueError, KeyError, TypeError):
            findings.add(f"{path}:{n}", "malformed workq row")
    return {i: w for i, (op, w) in last.items() if op == "claim"}


def load_lanes(path, findings):
    if not path or not Path(path).is_dir():
        findings.add(path or "lanes", "lanes directory not found (pass --lanes)")
        return set()
    return {p.name for p in Path(path).iterdir() if p.is_dir()}


def classify(item, claims, live_lanes, acks):
    """(disposition, evidence) for one item."""
    i, state = item["id"], item["state"]
    if state == "landed":
        return "LANDED", item.get("sha") or "state landed"
    if state in CLOSED:
        return "CLOSED", state
    if i in claims:
        return "IN-FLIGHT", f"workq claim by {claims[i]}"
    if state in ("in-progress", "ready") and item.get("owner") in live_lanes:
        return "IN-FLIGHT", f"live lane {item['owner']}"
    if i in acks:
        return "PARKED", f"ACK: {acks[i][0]}"
    if state == "deferred" and (item.get("note") or item.get("notes")):
        last = item.get("note") or item["notes"][-1]
        return "PARKED", "deferred: " + str(last.get("text") if isinstance(last, dict) else last)[:80]
    return "UNOWNED", state


def load_scenarios(root, findings):
    f = Path(root) / "tests/scenarios/catalog.json"
    text = read_text(f, findings)
    try:
        data = json.loads(text) if text is not None else {}
        return [s for s in data.get("scenarios", []) if isinstance(s, dict)]
    except (ValueError, AttributeError) as e:
        findings.add(f, f"malformed catalog ({e})")
        return []


def load_modules(root, findings):
    f = Path(root) / "tests/scenarios/tiers.tsv"
    text = read_text(f, findings)
    mods = {}
    for n, line in enumerate((text or "").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        cols = line.split("\t")
        if len(cols) < 3:
            findings.add(f"{f}:{n}", "malformed tiers row")
            continue
        if cols[1] == "module":
            m = re.match(r"tests\.(test_\w+)", cols[2])
            if not m:
                findings.add(f"{f}:{n}", f"module column is not tests.test_*: {cols[2]}")
                continue
            mods.setdefault("tests." + m.group(1), n)
    return mods


def names_module(path, stem):
    """Does an evidence path name the module test_native_X (stem native_X)?"""
    p = path.lower()
    if re.search(rf"(?<![a-z0-9_])test_{stem}(?![a-z0-9_])", p):
        return True
    return bool(re.search(rf"(?<![a-z0-9_]){stem.replace('_', '-')}"
                          r"(-[0-9a-f]{7,40})?\.(log|txt|json|md)$", p))


def never_run(root, scenarios, modules):
    """Scenarios declared native with no recorded log, modules with no record."""
    def recorded(p):
        # A log under the retired planning/evidence/ prefix lives on the box
        # that ran it; the catalog citation is its record.
        return p.startswith("planning/evidence/") or (Path(root) / p).exists()
    out = []
    cited = []
    for s in scenarios:
        impl = s.get("implementation")
        if not isinstance(impl, dict) or impl.get("native") is not True:
            continue
        logs = [impl[k] for k in ("log", "record") if isinstance(impl.get(k), str)]
        cited += logs
        if not any(recorded(p) for p in logs):
            out.append((s.get("id", "?"), "scenario " + str(impl.get("test", ""))))
    for mod in modules:
        stem = mod[len("tests.test_"):]
        if not any(names_module(p, stem) for p in cited):
            out.append((mod, "module"))
    return out


def report(root, claims=None, lanes=None, acks_path=None):
    findings = Findings()
    claims_path, lanes_dir = find_coordinator(root, claims, lanes)
    items = load_items(root, findings)
    acks = load_acks(acks_path or Path(root) / "planning/repair/ACKS.md", findings)
    claimed = load_claims(claims_path, findings)
    live = load_lanes(lanes_dir, findings)
    rows = [(it, *classify(it, claimed, live, acks)) for it in items]
    scenarios = load_scenarios(root, findings)
    modules = load_modules(root, findings)
    nr = never_run(root, scenarios, modules)
    known = {it["id"] for it in items} | {s.get("id") for s in scenarios} | set(modules)
    for a in sorted(acks):
        if a not in known and not a.startswith("ratchet:"):  # tools/ratchet.py reads those
            findings.add("ACKS.md", f"ACK names no item, scenario or module: {a}")
    by = {}
    for it, disp, ev in rows:
        by.setdefault(disp, []).append((it["id"], ev))
    stale = [a for a in acks if a in {it["id"] for it, d, _ in rows if d in ("LANDED", "CLOSED", "IN-FLIGHT")}]
    return {
        "dispositions": by,
        "unowned_unacked": sorted(i for i, _ in by.get("UNOWNED", [])),
        "never_run": [(i, k, i in acks) for i, k in nr],
        "never_run_unacked": sorted(i for i, _ in nr if i not in acks),
        "stale_acks": sorted(stale),
        "findings": list(findings),
    }


def render(r):
    out = []
    for d in ("LANDED", "IN-FLIGHT", "PARKED", "UNOWNED", "CLOSED"):
        out.append(f"{d}: {len(r['dispositions'].get(d, []))}")
    out.append(f"NEVER-RUN: {len(r['never_run'])} (unacked {len(r['never_run_unacked'])})")
    for i, ev in r["dispositions"].get("UNOWNED", []):
        out.append(f"  UNOWNED {i} [{ev}]")
    for i, k, acked in r["never_run"]:
        out.append(f"  NEVER-RUN {i} ({k}){' acked' if acked else ''}")
    for a in r["stale_acks"]:
        out.append(f"  STALE-ACK {a}: item is no longer open and unowned")
    for f in r["findings"]:
        out.append(f"  FINDING {f}")
    out.append(f"unacked-unowned={len(r['unowned_unacked'])} "
               f"never-run-unacked={len(r['never_run_unacked'])} findings={len(r['findings'])}")
    return "\n".join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--root", default=str(Path(__file__).resolve().parent.parent))
    ap.add_argument("--claims")
    ap.add_argument("--lanes")
    ap.add_argument("--acks")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args(argv)
    r = report(a.root, a.claims, a.lanes, a.acks)
    print(json.dumps(r, indent=1) if a.json else render(r))
    bad = bool(r["findings"]) or (a.check and (r["unowned_unacked"] or r["never_run_unacked"]))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

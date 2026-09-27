#!/usr/bin/env python3
"""Tally one or more configurations' cuts.jsonl (lane power-loss-openbsd-2):
cuts per kind, violations with their cycle, init-cut outcomes, import-cut
outcomes, reclaim reruns, and the oracle's acknowledged/refused totals.

  python3 power_loss_openbsd_tally.py DIR [DIR ...]
"""
import collections, json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import power_loss_openbsd as P

for d in map(Path, sys.argv[1:]):
    rows = [json.loads(l) for l in (d / "cuts.jsonl").read_text().splitlines()]
    kinds = collections.Counter()
    viol, inits, imports, reruns = [], collections.Counter(), collections.Counter(), collections.Counter()
    for r in rows:
        ph = r.get("phase")
        if r.get("phase_cut_t"):
            kinds[ph] += 1
        if r.get("cut_t") and not r.get("violations"):
            kinds["post" if ph in ("init", "recovery-interrupted") else (r.get("work") or ph)] += 1
        if r.get("violations"):
            viol.append((r["cycle"], r.get("ep"), ph, r["violations"][:3]))
        ic = r.get("init_cut")
        if ic:
            inits[(ic.get("store"), len(ic.get("stages") or []), "completed" if r.get("init_completed_before_cut") == 0 else "cut")] += 1
        if "import_completed_before_cut" in r:
            imports["completed-before-cut" if r["import_completed_before_cut"] == 0 else "cut-during"] += 1
        chk = r.get("import_check")
        if chk:
            imports["after: ROOT2 " + chk.get("store2", "?") + (" stage" if chk.get("stages") else "")] += 1
        if r.get("rerun"):
            reruns[(r["rerun"][0], r["rerun"][1])] += 1
    o = P.Oracle(d / "oracle.jsonl")
    acked = sum(len(e["ack"]) for e in o.eps.values())
    refused = sum(len(e["refuse"]) for e in o.eps.values())
    print("==", d.name, "cycles", len(rows), "cuts", sum(kinds.values()), dict(kinds))
    print("   acked", acked, "refused", refused, "epochs", len(o.eps))
    print("   init", dict(inits))
    print("   import", dict(imports))
    print("   reruns (verb, exit)", dict(reruns))
    for v in viol:
        print("   VIOLATION", v)

#!/usr/bin/env python3
"""Table of the campaign's checkpoint_cuts rows (both compaction entries), from campaign.json."""
import gzip, json, sys
p = sys.argv[1]
d = json.load(gzip.open(p) if p.endswith(".gz") else open(p))
rows = d.get("checkpoint_cuts", [])
print("| cut | entry | reached | killed step | recover rc | reread after cut | resume rcs | again | reread after resume | third POST rc | GROUP high before -> after | pass |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|")
n = ok = 0
for r in rows:
    for entry, e in r["entries"].items():
        n += 1; ok += bool(e.get("pass"))
        runs = e.get("cut_runs", [])
        step = next((i for i, x in enumerate(runs) if x.get("stopped")), None)
        again = e.get("again", {})
        gb, ga = e.get("group_before"), e.get("group_after")
        print("| `{}` | {} | {} | {} | {} | {} | {} | {} {} | {} | {} | {} -> {} | {} |".format(
            r["cut"], entry, e.get("reached"), step, e.get("recover_rc"),
            all((e.get("identical_after_cut") or {"x": False}).values()),
            ",".join(str(x.get("rc")) for x in e.get("resume", [])),
            again.get("rc"), "already-compact" if "already-compact" in again.get("stderr", "") else again.get("stderr", "")[:40],
            all((e.get("identical_after_resume") or {"x": False}).values()),
            (e.get("third_post") or {}).get("rc"), gb and gb[2], ga and ga[2],
            "PASS" if e.get("pass") else "FAIL"))
print()
print("checkpoint observations: {} of {} pass; cuts {}".format(ok, n, len(rows)))

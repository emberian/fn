# qual-dtn-c3420013: summarize app-receipt lab reports (per-step outcome, log sha16s).
import json, sys, hashlib, pathlib
def sha16(p):
    try: return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()[:16]
    except OSError: return "absent"
for d in sys.argv[1:]:
    d = pathlib.Path(d); rp = d / "report.json"
    out = d.parent / (d.name + ".out")
    print(f"== {d.name}  out {sha16(out)}  report {sha16(rp)}")
    if not rp.exists():
        print("   NO REPORT; tail:", out.read_text(errors="replace").splitlines()[-4:] if out.exists() else "")
        continue
    r = json.loads(rp.read_text())
    print("   a_releases", r.get("a_releases"), "b_trusts", (r.get("b_trusts") or {}).get("mode"), "native", r.get("native"),
          "| before:", r.get("a_pinned_before"), "| after:", r.get("a_pinned_after"))
    print("   processes", [(p.get("tag"), p.get("pid"), p.get("stopped")) for p in r.get("processes", [])])
    for k in ("signed_receipts", "control_obligation", "a_control_after"):
        if k in r: print("  ", k, json.dumps(r[k])[:300])
    for s in r["steps"]:
        extra = {k: v for k, v in s.items() if k not in ("step", "outcome", "logs", "log_detail") and not isinstance(v, (dict, list))}
        logs = s.get("logs") or {}
        shas = [f"{n}={(v or {}).get('sha256_16')}" for n, v in logs.items()]
        print(f"   [{s['step'][:60]}] -> {s.get('outcome')}  {extra}  {' '.join(shas)}")
    if "a_release_line" in r or True:
        for p in sorted(d.glob("a-serve*.log")):
            for line in p.read_text(errors="replace").splitlines():
                if "BP node release" in line or "receipt-" in line: print("   A:", line.strip()[:160]); 

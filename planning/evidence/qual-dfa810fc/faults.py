import json, sys, gzip
def load(p): return json.load(gzip.open(p) if p.endswith(".gz") else open(p))
def short(v):
    if isinstance(v, dict) and "rc" in v:
        return "rc={} {}".format(v["rc"], (v.get("stdout","").strip().splitlines() or [""])[-1][:70] + " | " + (v.get("stderr","").strip().splitlines() or [""])[-1][:90])
    if isinstance(v, dict) and isinstance(v.get("transactions"), dict):
        return "txns={} staging={}".format(len(v.get("transactions") or {}), sorted((v.get("staging") or {}).keys())[:3])
    if isinstance(v, list):
        return "[" + "; ".join(short(x) for x in v[:30]) + "]" + (" (+{})".format(len(v)-30) if len(v)>30 else "")
    if isinstance(v, dict):
        return "{" + ", ".join("{}: {}".format(k, short(x)) for k, x in v.items() if k not in ("argv","env")) + "}"
    return repr(v)[:120]
for f in load(sys.argv[1])["faults"]:
    print("##", f["name"], f.get("image"))
    for k, v in f.items():
        if k in ("name","image","init","seed_post","seed_owner_ready","seeded"): continue
        print("  ", k, ":", short(v)[:1500])

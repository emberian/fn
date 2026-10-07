#!/usr/bin/env python3
"""analyze.py RUNDIR... -> per-run row: latency overall / in-publication windows, publications, GC."""
import sys, json
from pathlib import Path
def pct(v, q):
    v = sorted(v); return v[min(len(v)-1, int(q*len(v)))] if v else float("nan")
for d in map(Path, sys.argv[1:]):
    o = json.load(open(d/"out.json"))
    posts = [tuple(map(float, l.split(","))) for l in (d/"posts.csv").read_text().split()]
    ev = [l.split() for l in (d/"events.log").read_text().splitlines()]
    starts = [int(x[1])/1e6 for x in ev if x[0]=="PUB-START"]; ends = [int(x[1])/1e6 for x in ev if x[0]=="PUB-END"]
    wins = list(zip(starts, ends)); gcs = [x for x in ev if x[0]=="GC"]
    inw = [l for s, l in posts if any(a <= s+l and s <= b for a, b in wins)]
    out = [l for s, l in posts if not any(a <= s+l and s <= b for a, b in wins)]
    al = [l for _, l in posts]; ms = lambda v, q: round(1000*pct(v, q), 1)
    gct = int(gcs[-1][2])/1e3 if gcs else 0
    print(json.dumps({"run": d.name, "setting": o["setting"], "n": len(al), "errs": len(o["errors"]), "load1": round(o["load1"],1),
      "all_ms": [ms(al,.5), ms(al,.95), ms(al,.99), round(1000*max(al),1)], "inpub_n": len(inw),
      "inpub_ms": [ms(inw,.5), ms(inw,.95), ms(inw,.99), round(1000*max(inw),1) if inw else None],
      "pubs": len(wins), "pub_ms": [round((b-a)*1000) for a, b in wins], "gcs": len(gcs), "gc_total_ms": round(gct),
      "hwm_mb": round(o["hwm_kb"]/1024,1), "steady_mb": round(o["steady_rss_kb"]/1024,1), "wall_s": o["wall_s"]}))

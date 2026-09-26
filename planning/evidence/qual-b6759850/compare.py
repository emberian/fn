import re, hashlib
from pathlib import Path
N = Path("/tank/fn/scratch/qual-bbf52159/logs"); O = Path("/tank/fn/scratch/qual-e747dbcc/logs")
def parse(p):
    if not p.exists(): return None
    t = p.read_text("utf-8", "replace")
    ran = re.search(r"^Ran (\d+) tests? in ([\d.]+)s", t, re.M)
    fails = sorted(set(re.findall(r"^(?:FAIL|ERROR): (\S+) \(", t, re.M)))
    sk = sum(int(x) for x in re.findall(r"skipped=(\d+)", " ".join(re.findall(r"^(?:OK|FAILED) \(([^)]*)\)", t, re.M))))
    w = re.search(r"# rc=(-?\d+) wall=([\d.]+)", t)
    return dict(n=int(ran.group(1)) if ran else 0, fails=fails, skip=sk, wall=w.group(2) if w else "-", rc=w.group(1) if w else "?", sha=hashlib.sha256(p.read_bytes()).hexdigest()[:16])
for p in sorted(N.glob("*.log")):
    a = parse(p); b = parse(O / p.name)
    same = "new" if b is None else ("same" if (a["fails"] == b["fails"] and a["n"] == b["n"]) else "CHANGED")
    print("| {} | {} | {} | {} | {} | {} | `{}` | {} | e747: {} |".format(p.name[:-4], a["n"], a["n"]-len(a["fails"])-a["skip"], len(a["fails"]), a["skip"], a["wall"], a["sha"], same,
        "-" if b is None else "{}/{} fail {}".format(b["n"], len(b["fails"]), b["wall"])))
    if same == "CHANGED":
        print("    now-failing:", [f for f in a["fails"] if f not in b["fails"]], " now-passing:", [f for f in b["fails"] if f not in a["fails"]])
    if a["fails"] and same != "same":
        print("    fails:", a["fails"])

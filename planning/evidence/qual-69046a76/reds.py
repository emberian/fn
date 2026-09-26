#!/usr/bin/env python3
"""qual-69046a76: per module and label, the FAIL/ERROR test names here vs qual-dfa810fc's same-label logs."""
import re, sys
from pathlib import Path
N = Path("/tank/fn/scratch/qual-69046a76/blogs"); O = Path("/tank/fn/scratch/qual-dfa810fc/blogs")
def reds(p):
    if not p.exists(): return None
    t = p.read_text("utf-8", "replace")
    return sorted(set(re.findall(r"^(?:FAIL|ERROR): (\S+) \(", t, re.M)))
for lab in sys.argv[1:]:
    for p in sorted((N / lab).glob("*.log")):
        if p.name.endswith(".whole.log"): continue
        a = reds(p); b = reds(O / lab / p.name)
        w = N / lab / (p.stem + ".whole.log")
        if w.exists(): a = reds(w); b = reds(O / lab / w.name) if (O / lab / w.name).exists() else b
        if a:
            new = sorted(set(a) - set(b or [])); gone = sorted(set(b or []) - set(a))
            print("%-7s %-45s reds=%d new=%s" % (lab, p.stem.replace("tests.",""), len(a), new or "-"))
        elif b:
            print("%-7s %-45s GREEN now (was %d red: %s)" % (lab, p.stem.replace("tests.",""), len(b), b[:3]))

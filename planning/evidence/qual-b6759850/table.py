#!/usr/bin/env python3
"""qual-b6759850: one Markdown table of every module run (tools/test_budget.py
reports), per image label, with the log's SHA-256 (16 hex) and any whole rerun."""
import hashlib, json, re, sys
from pathlib import Path
S = Path("/tank/fn/scratch/qual-b6759850")
rows = []
for label in ("prod", "dev", "dtn", "dtndev"):
    rep = S / ("breport-%s.json" % label)
    if not rep.exists():
        continue
    for r in json.load(open(rep)):
        mod = r["module"]
        log = S / "blogs" / label / (mod + ".log")
        sha = hashlib.sha256(log.read_bytes()).hexdigest()[:16] if log.exists() else "-"
        text = log.read_text("utf-8", "replace") if log.exists() else ""
        m = re.search(r"^Ran (\d+) tests? in", text, re.M)
        ran = m.group(1) if m else "?"
        fail = re.search(r"^FAILED \((.*)\)", text, re.M)
        skip = re.search(r"skipped=(\d+)", text)
        verdict = "OK" if re.search(r"^OK", text, re.M) else ("FAILED " + fail.group(1) if fail else ("terminated" if r.get("terminated") else "?"))
        whole = S / "blogs" / label / (mod + ".whole.log")
        if whole.exists():
            wt = whole.read_text("utf-8", "replace")
            wv = re.findall(r"^(OK.*|FAILED.*)$", wt, re.M)
            verdict += "; whole: %s (%s)" % (wv[-1] if wv else "stopped", hashlib.sha256(whole.read_bytes()).hexdigest()[:16])
        over = "over" if r.get("over_budget") else ""
        rows.append("| %s | %s | %s | %s | %.1f %s | %s |" % (label, mod.replace("tests.", ""), ran, verdict, r["seconds"], over, sha))
print("| image | module | tests | result | s (budget) | log (16) |\n| --- | --- | --- | --- | --- | --- |")
print("\n".join(rows))

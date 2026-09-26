#!/usr/bin/env python3
"""cont.py SESSION BOOK START-NAME [END-NAME]: send the book forms from the first whose head names START-NAME, stopping at the first refusal."""
import subprocess, sys
sys.path.insert(0, "tools")
import proof_repl
session, book, start = sys.argv[1], sys.argv[2], sys.argv[3]
end = sys.argv[4] if len(sys.argv) > 4 else None
fs = proof_repl.forms(open(book).read())
heads = [" ".join(f.split("\n")[:2])[:160] for f in fs]
i0 = next(i for i, h in enumerate(heads) if start in h)
i1 = next((i for i, h in enumerate(heads) if end and end in h and i >= i0), len(fs) - 1) if end else len(fs) - 1
for i in range(i0, i1 + 1):
    r = subprocess.run(["python3", "tools/proof_repl.py", "send", session, fs[i]], capture_output=True, text=True)
    out = r.stdout + r.stderr
    bad = any(m in out for m in ("ACL2 Error", "HARD ACL2 ERROR", "FAILED", "Halted"))
    print("[%d] %s %s" % (i, "FAIL" if bad else "ok", heads[i]))
    if bad:
        print(out[-6000:])
        sys.exit(1)
print("ALL-SENT through", i1)

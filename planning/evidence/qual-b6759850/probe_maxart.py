#!/usr/bin/env python3
"""qual-b6759850 fact 1a, step 1: the largest article the scale profile admits
over a served POST (the owner decides; this only searches).  A fresh scale
store, the production owner, one POST per candidate size (rep_measure's
article shape, a fresh Message-ID each), bisection on the 240/441 answer."""
import os, subprocess, sys, json
from pathlib import Path
T = Path("/tank/fn/scratch/qual-b6759850/tree")
sys.path.insert(0, str(T / "tools")); sys.path.insert(0, str(T))
import rep_measure as rm, msgid_measure as m
image, work = sys.argv[1], Path(sys.argv[2])
work.mkdir(parents=True, exist_ok=False)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE"); env.pop("ACL2_SYSTEM_BOOKS", None)
port = m.free_port()
cfg = work / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (work / "store", port, work / "control.sock"))
r = subprocess.run([image, "--fn", "operator", str(cfg), "init", "--profile", "scale", "fn.test"], env=env, capture_output=True)
print("init rc", r.returncode, r.stdout.decode()[-300:])
proc, t, err = rm.start_owner(image, cfg, env, work / "owner.stderr")
answers = {}
def try_size(n, i):
    c = m.Conn(port)
    a = rm.article(100000 + i, n)
    r = c.line("POST")
    c.stream.write(a + b".\r\n"); rep = c.readline(); c.close()
    answers[n] = (len(a), rep.decode().strip())
    print("size", n, "article octets", len(a), "->", rep.decode().strip(), flush=True)
    return rep.startswith(b"240")
lo, hi, i = 1000, 70000, 0
assert try_size(lo, i)
i += 1
assert not try_size(hi, i)
while hi - lo > 1:
    i += 1
    mid = (lo + hi) // 2
    if try_size(mid, i): lo = mid
    else: hi = mid
print("LARGEST-ADMITTED", lo, "REFUSED-AT", hi, json.dumps({str(k): v for k, v in sorted(answers.items())}))
rm.stop_owner(proc, err)
r = subprocess.run([image, "--fn", "operator", str(cfg), "status"], env=env, capture_output=True)
print(r.stdout.decode())

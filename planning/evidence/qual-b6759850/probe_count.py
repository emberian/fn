#!/usr/bin/env python3
"""qual-b6759850: transaction-COUNT exhaustion, separate from history-byte
exhaustion (the tight store).  Development profile (T=128, H=24 MiB, so bytes
never bind): 127 POSTs accepted (the maintenance reservation keeps one
transaction for a release record: the contract), the 128th refused by name,
the owner stays up; then with retention released-by-all-holders, `store
compact` and `store reclaim` on the count-full store, `status` before and
after (reclaiming bodies lowers byte use, not the transaction count), and one
more POST.  Production image; every decision is the image's."""
import os, subprocess, socket, sys
from pathlib import Path
I = "/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host"
D = Path("/tank/fn/scratch/qual-b6759850/probe-count")
subprocess.run(["rm", "-rf", str(D)]); D.mkdir(parents=True)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE"); env.pop("ACL2_SYSTEM_BOOKS", None)
s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
cfg = D / "fn.toml"
cfg.write_text('[store]\npath = "%s/store"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s/control.sock"\n' % (D, port, D))
def native(*a):
    r = subprocess.run([I, "--fn", *map(str, a)], env=env, capture_output=True)
    out = (r.stdout + r.stderr).decode("utf-8", "replace")
    print("RUN %s rc=%d" % (" ".join(map(str, a[2:5])), r.returncode))
    for l in out.splitlines():
        if l.startswith(("headroom", "maintenance-reserve", "transactions=", "reclaim", "compacted", "reclaimed=", "refused", "accepted", "dry-run")):
            print("  | " + l[:220])
    return r.returncode
native("operator", cfg, "init", "--profile", "development", "fn.test")
def start():
    o = subprocess.Popen([I, "--fn", "operator", str(cfg), "run"], env=env, stdout=subprocess.PIPE, stderr=open(D / "owner.err", "ab"))
    while True:
        l = o.stdout.readline()
        if not l or l.startswith(b"LISTENING"): return o
def post(i):
    art = (b"From: a@example.invalid\r\nNewsgroups: fn.test\r\nSubject: s%d\r\nMessage-ID: <cnt%d@example.invalid>\r\nDate: Sat, 26 Sep 2026 07:00:00 +0000\r\n\r\nbody\r\n" % (i, i))
    c = socket.create_connection(("127.0.0.1", port), 60); f = c.makefile("rwb", buffering=0); f.readline()
    f.write(b"POST\r\n"); f.readline(); f.write(art + b".\r\n"); rep = f.readline().decode().strip(); c.close(); return rep
o = start()
reps = [post(i) for i in range(130)]
acc = sum(1 for r in reps if r.startswith("240"))
first_refused = next((i + 1 for i, r in enumerate(reps) if not r.startswith("240")), None)
print("COUNT accepted=%d first-refused-post=%s reply=%r owner-alive=%s" % (acc, first_refused, reps[first_refused - 1] if first_refused else None, o.poll() is None))
o.terminate(); o.wait(60); print("owner exit", o.returncode)
native("operator", cfg, "status")
native("operator", cfg, "retention", "set", "released-by-all-holders")
native("operator", cfg, "store", "compact")
native("operator", cfg, "store", "reclaim")
native("operator", cfg, "status")
o = start()
print("POST after reclaim on the count-full store:", post(999))
o.terminate(); o.wait(60); print("owner exit", o.returncode)
native("operator", cfg, "status")

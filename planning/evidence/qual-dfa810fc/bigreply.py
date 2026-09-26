#!/usr/bin/env python3
"""qual-dfa810fc: does one served step with a multi-MiB reply fault the owner (the
public-exposure observation over fn-served-reply-octets)?  A copy of the kept
20,000-record chain fixture (never opened in place), the given image's owner,
then on one reader connection: LIST ACTIVE, GROUP, OVER 1-N, and a STAT after.
Usage: bigreply.py IMAGE WORK"""
import os, shutil, signal, socket, subprocess, sys, time
from pathlib import Path
img, W = sys.argv[1], Path(sys.argv[2])
FX = Path("/tank/fn/scratch/fixtures/chain-20000-8cc3cd4c")
W.mkdir(parents=True, exist_ok=False)
shutil.copytree(FX / "store", W / "store", symlinks=True)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
for k in [k for k in env if k.startswith("FN_NATIVE_")]:
    env.pop(k)
with socket.socket() as s:
    s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]
cfg = W / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (W / "store", port, W / "c.sock"))
err = open(W / "owner.err", "wb")
t0 = time.time()
o = subprocess.Popen([img, "--fn", "operator", str(cfg), "run"], env=env, stdout=subprocess.PIPE, stderr=err)
while not o.stdout.readline().startswith(b"LISTENING"):
    pass
print("listening after %.1f s" % (time.time() - t0), flush=True)
c = socket.create_connection(("127.0.0.1", port), 600); f = c.makefile("rwb", buffering=0)
print("greeting", f.readline().strip())
def multi():
    n, octets = 0, 0
    while True:
        l = f.readline()
        if not l:
            return n, octets, "EOF"
        if l == b".\r\n":
            return n, octets, "end"
        n += 1; octets += len(l)
f.write(b"LIST ACTIVE\r\n"); print("LIST", f.readline().strip()); n, oc, how = multi(); print("  groups", n, how)
f.write(b"GROUP fn.test\r\n"); g = f.readline().strip(); print("GROUP", g)
for rng in ("1-2000", "1-10000", "1-20000"):
    t0 = time.time()
    f.write(("OVER %s\r\n" % rng).encode()); st = f.readline().strip()
    n, oc, how = multi() if st.startswith(b"224") else (0, 0, "none")
    print("OVER %s -> %s lines=%d octets=%d %s %.2f s; owner alive=%s" % (rng, st[:40], n, oc, how, time.time() - t0, o.poll() is None), flush=True)
    if how != "end":
        break
time.sleep(1)
print("owner alive after:", o.poll() is None, "exit", o.returncode)
if o.poll() is None:
    o.send_signal(signal.SIGTERM); o.wait(120)
print("owner exit", o.returncode, "| stderr tail:", " / ".join((W / "owner.err").read_bytes().decode("utf-8", "replace").strip().splitlines()[-4:])[:400])

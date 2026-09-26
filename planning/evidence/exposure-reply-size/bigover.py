#!/usr/bin/env python3
"""exposure-reply-size: a multi-MiB OVER reply in one served step.
A fresh 4 MiB-profile store, one owner, K articles each with a References
header folded over many lines (R octets of message-ids), then OVER over the
whole group on one connection, then STAT on a new connection, then SIGTERM.
Usage (tree root as cwd): bigover.py WORK IMAGE K R [refs|subject]
(subject: an R-octet run on the Subject line instead of the folded References)"""
import os, signal, socket, subprocess, sys, time, hashlib
from pathlib import Path
work, img, K, R = Path(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
MODE = sys.argv[5] if len(sys.argv) > 5 else "refs"
work.mkdir(parents=True, exist_ok=False)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
for k in [k for k in env if k.startswith("FN_NATIVE_")]:
    env.pop(k)
with socket.socket() as s:
    s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]
cfg = work / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (work / "store", port, work / "c.sock"))
r = subprocess.run([img, "--fn", "operator", str(cfg), "init", "--max-article-octets", "4194304", "fn.test"], env=env, capture_output=True)
print("init", r.returncode, r.stdout.decode()[-200:].strip(), r.stderr.decode()[-200:].strip(), flush=True)
err = open(work / "owner.err", "wb")
o = subprocess.Popen([img, "--fn", "operator", str(cfg), "run"], env=env, stdout=subprocess.PIPE, stderr=err)
while not o.stdout.readline().startswith(b"LISTENING"):
    pass
def refs(i):
    if MODE == "subject":
        return b""
    ids, n, j = [], 0, 0
    while n < R:
        m = "<r%d-%d@example.invalid>" % (i, j); ids.append(m); n += len(m) + 3; j += 1
    return b"References: " + "\r\n ".join(ids).encode() + b"\r\n"
c = socket.create_connection(("127.0.0.1", port), 600); f = c.makefile("rwb", buffering=0)
f.readline()
t0 = time.time(); bad = 0
for i in range(K):
    f.write(b"POST\r\n"); assert f.readline().startswith(b"340")
    f.write(b"From: over@example.invalid\r\nNewsgroups: fn.test\r\nSubject: big over " + str(i).encode() +
            b"\r\nMessage-ID: <over-%d@example.invalid>\r\n" % i + refs(i) + b"\r\nbody\r\n.\r\n")
    rep = f.readline()
    if not rep.startswith(b"240"):
        bad += 1; print("POST", i, rep.strip(), flush=True)
        if bad > 3: break
print("posted %d (%d refused) in %.1f s" % (K, bad, time.time() - t0), flush=True)
f.write(b"GROUP fn.test\r\n"); g = f.readline().strip(); print("GROUP", g, flush=True)
lo, hi = g.split()[2:4]
t0 = time.time(); f.write(b"OVER %s-%s\r\n" % (lo, hi)); st = f.readline().strip()
n, octets, h, how = 0, 0, hashlib.sha256(), "none"
if st.startswith(b"224"):
    while True:
        l = f.readline()
        if not l: how = "EOF"; break
        if l == b".\r\n": how = "end"; break
        n += 1; octets += len(l); h.update(l)
print("OVER -> %s lines=%d octets=%d %s sha256=%s %.2f s" % (st[:40].decode(), n, octets, how, h.hexdigest()[:16], time.time() - t0), flush=True)
c.close()
time.sleep(0.5)
try:
    c2 = socket.create_connection(("127.0.0.1", port), 30); f2 = c2.makefile("rwb", buffering=0); f2.readline()
    f2.write(b"STAT <over-0@example.invalid>\r\n"); print("STAT", f2.readline().strip(), flush=True); c2.close()
except Exception as e:
    print("STAT EXC", repr(e))
alive = o.poll() is None
if alive:
    o.send_signal(signal.SIGTERM)
try:
    o.wait(120)
except subprocess.TimeoutExpired:
    o.kill(); o.wait()
tail = (work / "owner.err").read_bytes().decode("utf-8", "replace").strip().splitlines()[-3:]
print("owner alive after OVER=%s exit=%s | %s" % (alive, o.returncode, " / ".join(tail)[:300]), flush=True)

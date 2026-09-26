#!/usr/bin/env python3
"""qual-69046a76 item 1 (c), reshaped (D34, the coordinator 2026-09-26): the node is REINSTALLED
from the release, not upgraded in place.  The release tarball built from the gate's frozen image
(friends/release, 1a2a61e9...) is unpacked into a fresh prefix exactly as a stranger would; every
FN_NATIVE_* variable is removed from the children's environment and `fn --version` proves which
image answered.  Then (A) a fresh node: init, run, POST, ARTICLE, stop, recover; (B) the test
store imported: 69046a76 has no `store export/import` verb (D34 names it for later), so the import
is the only form the release has: a `cp -a` of the stopped live store's copy placed at the new
node's [store] path; status (below H), run, GROUP/ARTICLE of an article the live node accepted,
POST, stop, recover, status.  Never touches /tank/fn/node beyond a read-only cp -a."""
import hashlib, os, shutil, signal, socket, subprocess, sys, tarfile, time
from pathlib import Path
S = Path("/tank/fn/scratch/qual-69046a76"); R = S / "reinstall"
TAR = S / "friends/release/fn-69046a76798b-linux-x86_64.tar.gz"
if R.exists(): shutil.rmtree(R)
R.mkdir()
ENV = {k: v for k, v in os.environ.items() if not k.startswith("FN_NATIVE_") and k not in ("FN_OLD_IMAGE", "FN_FORMAT7_IMAGE", "LD_LIBRARY_PATH", "SBCL_HOME")}
ENV["ACL2_CUSTOMIZATION"] = "NONE"
def say(*a): print(*a, flush=True)
def sh(label, argv, **kw):
    r = subprocess.run([str(x) for x in argv], env=ENV, capture_output=True, **kw)
    out = (r.stdout + r.stderr).decode("utf-8", "replace").strip()
    say("STEP %s rc=%d" % (label, r.returncode))
    for l in out.splitlines()[-14:]: say("  | " + l[:220])
    return r.returncode, out
say("tarball sha256", hashlib.sha256(TAR.read_bytes()).hexdigest())
sh("verify tarball .sha256", ["sh", "-c", "cd %s && sha256sum -c %s.sha256" % (TAR.parent, TAR.name)])
with tarfile.open(TAR) as t: t.extractall(R / "opt")
top = next((R / "opt").iterdir()); FN = top / "bin" / "fn"
sh("SHA256SUMS of the unpacked release", ["sh", "-c", "cd %s && sha256sum -c --quiet SHA256SUMS && echo SUMS-OK" % top])
sh("fn --version (which image answers)", [FN, "--version"])
say("ENV FN_NATIVE_* in children:", sorted(k for k in ENV if k.startswith("FN_NATIVE_")))
def port():
    with socket.socket() as s: s.bind(("127.0.0.1", 0)); return s.getsockname()[1]
def cfg(d, p):
    c = d / "fn.toml"
    c.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (d / "store", p, d / "control.sock"))
    return c
def nntp(p, lines, post=None):
    s = socket.create_connection(("127.0.0.1", p), 60); f = s.makefile("rb"); out = [f.readline().strip()]
    for l in lines:
        s.sendall(l.encode() + b"\r\n"); r = f.readline().strip(); out.append((l, r))
        if r[:3] in (b"220", b"224", b"215", b"221"):
            n = 0
            while f.readline() != b".\r\n": n += 1
            out.append(("  lines", n))
    if post:
        s.sendall(b"POST\r\n"); out.append(("POST", f.readline().strip())); s.sendall(post + b".\r\n"); out.append(("POST body", f.readline().strip()))
    s.sendall(b"QUIT\r\n"); s.close(); return out
def owner(c):
    err = open(c.parent / "owner.err", "ab")
    o = subprocess.Popen([str(FN), "operator", str(c), "run"], env=ENV, stdout=subprocess.PIPE, stderr=err)
    t0 = time.time()
    while True:
        l = o.stdout.readline()
        if not l: say("OWNER exited before LISTENING rc", o.wait()); return None
        if l.startswith(b"LISTENING"): say("OWNER LISTENING after %.2f s" % (time.time() - t0)); return o
def stop(o):
    o.send_signal(signal.SIGTERM); say("OWNER exit", o.wait(120))
art = lambda mid: ("From: q <q@example.invalid>\r\nNewsgroups: %s\r\nSubject: reinstall\r\nMessage-ID: %s\r\n\r\nbody\r\n" % ("{G}", mid))
# (A) fresh node
A = R / "fresh"; A.mkdir(); pa = port(); ca = cfg(A, pa)
sh("A init fn.test", [FN, "operator", ca, "init", "fn.test"])
o = owner(ca)
for x in nntp(pa, ["GROUP fn.test", "ARTICLE <reinstall-a@qual.invalid>"], post=art("<reinstall-a@qual.invalid>").replace("{G}", "fn.test").encode()): say("  A", x)
for x in nntp(pa, ["GROUP fn.test", "ARTICLE <reinstall-a@qual.invalid>"]): say("  A reread", x)
stop(o); sh("A recover", [FN, "operator", ca, "recover"]); sh("A status", [FN, "operator", ca, "status"])
# (B) the test store imported
B = R / "import"; B.mkdir(); pb = port()
sh("cp -a the live store (read-only source)", ["cp", "-a", "/tank/fn/node/store", B / "store"])
for p in (B / "store").glob("control.sock*"): p.unlink()
cb = cfg(B, pb)
rc, st = sh("B status on the imported store", [FN, "operator", cb, "status"])
groups = [l.split()[1] for l in st.splitlines() if l.startswith("group ")] or ["fn.agents"]
sh("B health offline", [FN, "operator", cb, "health"])
o = owner(cb)
g = "fn.agents"
first = nntp(pb, ["LIST ACTIVE", "GROUP %s" % g, "ARTICLE"], post=art("<reinstall-b@qual.invalid>").replace("{G}", g).encode())
for x in first: say("  B", x)
for x in nntp(pb, ["GROUP %s" % g, "ARTICLE <reinstall-b@qual.invalid>"]): say("  B reread", x)
stop(o); sh("B recover", [FN, "operator", cb, "recover"]); sh("B status after", [FN, "operator", cb, "status"])
say("DONE")

#!/usr/bin/env python3
"""qual-b6759850 web pass, node side (hbox): a scratch node on the PRODUCTION
image with STARTTLS (a certificate for 127.0.0.1) and [auth] required, logins
`ember` (bound to principal E by `principal bind`, posting-policy bound-logins, enrolled) and `guest` (unbound), seeded as reader-daily's
walk was: ember's signed root and signed reply (hybrid-sign + hybrid-author
over the control socket), guest's tin-shaped follow-up to the reply (supplied
Path, both References), guest's `notes` post, then ember's signed cancel of the
reply (so number 2 is withdrawn).  The owner then keeps serving until the file
STOP appears; only PIDs started here are stopped.  Prints PORT and the
certificate path for the laptop's fn_web.py + Playwright walk."""
import os, socket, ssl, subprocess, sys, time
from pathlib import Path
S = Path("/tank/fn/scratch/qual-b6759850")
T = S / "tree"
I = Path("/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80")
IMG, DEV = I / "fn-host", I / "fn-host-developer"
OPENSSL = str(S / "bin" / "test-openssl")
W = S / "webnode"
EMBER_PW, GUEST_PW = "web-ember-b6759850", "web-guest-b6759850"
E = bytes([0xEE]) * 32
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE"); env.pop("ACL2_SYSTEM_BOOKS", None); env.pop("LD_LIBRARY_PATH", None)
def run(*a, stdin=None, image=IMG):
    r = subprocess.run([str(image), "--fn", *map(str, a)], cwd=T, env=env, input=stdin, capture_output=True, timeout=300)
    print("RUN", " ".join(map(str, a[:4])), "rc", r.returncode, (r.stdout + r.stderr).decode("utf-8", "replace").strip()[-300:], flush=True)
    return r
subprocess.run(["rm", "-rf", str(W)], check=True); W.mkdir(parents=True)
store, cert, key, cfg, control = W / "store", W / "cert.pem", W / "key.pem", W / "fn.toml", W / "control.sock"
subprocess.run([OPENSSL, "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key), "-out", str(cert), "-sha256", "-days", "2",
                "-nodes", "-subj", "/CN=localhost", "-addext", "subjectAltName=IP:127.0.0.1,DNS:localhost"], check=True, capture_output=True)
with socket.socket() as p:
    p.bind(("127.0.0.1", 0)); port = p.getsockname()[1]
cfg.write_text('[store]\npath = "%s"\n\n[listener]\nhost = "127.0.0.1"\nport = %d\ntls_cert = "%s"\ntls_key = "%s"\n\n'
               '[auth]\nrequired = true\nprotected_only = true\npath = "%s"\n\n[posting]\nenabled = true\n\n[control]\npath = "%s"\n\n[log]\npath = "%s"\n'
               % (store, port, cert, key, store / "auth.toml", control, W / "fn.log"))
run("operator", cfg, "init", "fn.agents")
run("operator", cfg, "group", "create", "control.cancel")
run("operator", cfg, "principal", "set-password", "ember", "--principal", E.hex(), "--posting", stdin=(EMBER_PW + "\n" + EMBER_PW + "\n").encode())
run("operator", cfg, "principal", "set-password", "guest", "--posting", stdin=(GUEST_PW + "\n" + GUEST_PW + "\n").encode())
run("operator", cfg, "principal", "bind", "ember", E.hex())
run("operator", cfg, "policy", "set", "posting-policy", "bound-logins")
run("operator", cfg, "principal", "list")
keys = W / "keys"; keys.mkdir()
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric import ed25519
k = ed25519.Ed25519PrivateKey.generate()
seed = k.private_bytes(serialization.Encoding.Raw, serialization.PrivateFormat.Raw, serialization.NoEncryption())
pub = k.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
(keys / "principal.bin").write_bytes(E); (keys / "ed-public.bin").write_bytes(pub); (keys / "ed-secret.bin").write_bytes(seed + pub)
subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(keys / "ml-private.pem")], check=True, capture_output=True)
subprocess.run([OPENSSL, "pkey", "-in", str(keys / "ml-private.pem"), "-pubout", "-out", str(keys / "ml-public.pem")], check=True, capture_output=True)
err = open(W / "owner.err", "ab")
owner = subprocess.Popen([str(IMG), "--fn", "operator", str(cfg), "run"], cwd=T, env=env, stdout=subprocess.PIPE, stderr=err)
while True:
    l = owner.stdout.readline()
    if not l or l.startswith(b"LISTENING"):
        print("OWNER", owner.pid, l.decode().strip(), flush=True); break
r = run("hybrid-enroll", control, "1", keys / "principal.bin", keys / "ed-public.bin", keys / "ml-public.pem")
if r.returncode != 0:
    run("hybrid-enroll", control, "1", keys / "principal.bin", keys / "ed-public.bin", keys / "ml-public.pem", image=DEV)
Q = bytes([0x51]) * 32
qk = W / "keys-q"; qk.mkdir()
k2 = ed25519.Ed25519PrivateKey.generate()
seed2 = k2.private_bytes(serialization.Encoding.Raw, serialization.PrivateFormat.Raw, serialization.NoEncryption())
pub2 = k2.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
(qk / "principal.bin").write_bytes(Q); (qk / "ed-public.bin").write_bytes(pub2); (qk / "ed-secret.bin").write_bytes(seed2 + pub2)
subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(qk / "ml-private.pem")], check=True, capture_output=True)
subprocess.run([OPENSSL, "pkey", "-in", str(qk / "ml-private.pem"), "-pubout", "-out", str(qk / "ml-public.pem")], check=True, capture_output=True)
r = run("hybrid-enroll", control, "2", qk / "principal.bin", qk / "ed-public.bin", qk / "ml-public.pem")
if r.returncode != 0:
    run("hybrid-enroll", control, "2", qk / "principal.bin", qk / "ed-public.bin", qk / "ml-public.pem", image=DEV)
def signed(stem, msgid, subject, refs="", cancel=""):
    lines = ["From: ember <ember@fn.example.invalid>", "Newsgroups: " + ("control.cancel" if cancel else "fn.agents"),
             "Subject: " + subject, "Date: Sat, 26 Sep 2026 06:30:00 +0000", "Message-ID: " + msgid]
    if refs: lines.append("References: " + refs)
    if cancel: lines.append("Control: cancel " + cancel)
    src = W / (stem + ".eml")
    src.write_bytes(("\r\n".join(lines) + "\r\n\r\n" + ("cancel\r\n" if cancel else "Signed by ember for the qualification walk.\r\n")).encode())
    s = subprocess.run([str(IMG), "--fn", "hybrid-sign", keys / "principal.bin", keys / "ed-public.bin", keys / "ed-secret.bin",
                        keys / "ml-public.pem", keys / "ml-private.pem", src], cwd=T, env=env, capture_output=True, timeout=180)
    if s.returncode != 0:
        s = subprocess.run([str(DEV), "--fn", "hybrid-sign", keys / "principal.bin", keys / "ed-public.bin", keys / "ed-secret.bin",
                            keys / "ml-public.pem", keys / "ml-private.pem", src], cwd=T, env=env, capture_output=True, timeout=180)
    parts = dict(x.split() for x in s.stdout.decode().splitlines() if " " in x)
    (W / (stem + ".ed")).write_bytes(bytes.fromhex(parts["ed25519"])); (W / (stem + ".ml")).write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
    run("hybrid-author", control, "1", src, W / (stem + ".ed"), W / (stem + ".ml"), keys / "ml-public.pem")
def nntp_post(user, pw, article):
    raw = socket.create_connection(("127.0.0.1", port), 30); f = raw.makefile("rb"); f.readline()
    raw.sendall(b"STARTTLS\r\n"); f.readline()
    ctx = ssl.create_default_context(cafile=str(cert)); t = ctx.wrap_socket(raw, server_hostname="127.0.0.1"); tf = t.makefile("rb")
    for l in ("AUTHINFO USER " + user, "AUTHINFO PASS " + pw, "POST"):
        t.sendall(l.encode() + b"\r\n"); rep = tf.readline()
    t.sendall(article + b".\r\n"); rep = tf.readline().decode().strip()
    print("POST as", user, "->", rep, flush=True); t.close()
ROOT, MID = "<walk-root.b675@fn.example.invalid>", "<walk-mid.b675@fn.example.invalid>"
signed("root", ROOT, "Daily walk")
signed("mid", MID, "Re: Daily walk", refs=ROOT)
nntp_post("guest", GUEST_PW, ("Path: not-for-mail\r\nFrom: guest <guest@fn.example.invalid>\r\nNewsgroups: fn.agents\r\nSubject: Re: Daily walk\r\n"
          "Message-ID: <walk-tin.b675@fn.example.invalid>\r\nReferences: %s %s\r\nDate: Sat, 26 Sep 2026 06:31:00 +0000\r\n"
          "User-Agent: TIN/2.6.2-20221225 (UNIX) (Linux/6)\r\n\r\nguest follows up to the reply\r\n" % (ROOT, MID)).encode())
nntp_post("guest", GUEST_PW, (b"From: guest <guest@fn.example.invalid>\r\nNewsgroups: fn.agents\r\nSubject: walk notes\r\n"
          b"Message-ID: <walk-notes.b675@fn.example.invalid>\r\nDate: Sat, 26 Sep 2026 06:32:00 +0000\r\n\r\nnotes for the search\r\n"))
signed("cancel", "<walk-cancel.b675@fn.example.invalid>", "cmsg cancel " + MID, cancel=MID)
(W / "cred-ember").write_text("ember %s\n" % EMBER_PW); (W / "cred-ember").chmod(0o600)
(W / "cred-guest").write_text("guest %s\n" % GUEST_PW); (W / "cred-guest").chmod(0o600)
print("READY PORT %d CERT %s" % (port, cert), flush=True)
(W / "READY").write_text("%d\n" % port)
while not (W / "STOP").exists() and owner.poll() is None:
    time.sleep(2)
owner.terminate()
try: owner.wait(60)
except subprocess.TimeoutExpired: owner.kill(); owner.wait()
print("owner exit", owner.returncode, "stdout after LISTENING:", owner.stdout.read().decode()[-500:], flush=True)
r = run("operator", cfg, "status")

#!/usr/bin/env python3
"""qual-b6759850 section 15 "Protected ordinary use", against the running
webnode (production image, STARTTLS with a certificate for 127.0.0.1, [auth]
required, `ember` bound to E under posting-policy bound-logins, `guest`
unbound).  A real client (tools/fn_client.py) posts, reads, replies and
resumes; then the wrong-channel and wrong-principal cases, each by its own
answer.  Only the node's lines are reported."""
import os, socket, ssl, subprocess, sys
from pathlib import Path
S = Path("/tank/fn/scratch/qual-b6759850"); T = S / "tree"; W = S / "webnode"
I = Path("/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80")
port = int((W / "READY").read_text()); cert = W / "cert.pem"
env = dict(os.environ); env.pop("LD_LIBRARY_PATH", None)
def say(*a): print(*a, flush=True)
def client(cred, *args, stdin=None, state="state-guest.json"):
    argv = [sys.executable, str(T / "tools" / "fn_client.py"), *map(str, args), "--node", "127.0.0.1:%d" % port,
            "--cafile", str(cert), "--credentials", str(W / cred), "--state", str(S / "protected" / state)]
    r = subprocess.run(argv, cwd=T, env=dict(env, FN_CLIENT_FROM="guest <guest@fn.example.invalid>"), input=stdin, capture_output=True, timeout=120)
    say("CLIENT %s %s rc=%d" % (cred, " ".join(map(str, args[:4])), r.returncode))
    for l in (r.stdout + r.stderr).decode("utf-8", "replace").strip().splitlines()[-12:]:
        say("  | " + l[:220])
    return r.returncode
(S / "protected").mkdir(exist_ok=True)
say("== the real client as guest: post, read, reply, resume")
client("cred-guest", "groups")
client("cred-guest", "read", "fn.agents", "--all")
client("cred-guest", "post", "fn.agents", "--subject", "protected ordinary", "--message-id", "<prot-1@qual.invalid>",
       "--draft", S / "protected" / "draft-1.json", stdin=b"posted over STARTTLS as guest\n")
client("cred-guest", "show", "<prot-1@qual.invalid>")
client("cred-guest", "post", "fn.agents", "--subject", "Re: protected ordinary", "--message-id", "<prot-2@qual.invalid>",
       "--references", "<prot-1@qual.invalid>", stdin=b"a reply\n")
client("cred-guest", "read", "fn.agents", "--new")
client("cred-guest", "post", "fn.agents", "--subject", "after the watermark", "--message-id", "<prot-3@qual.invalid>", stdin=b"later\n")
say("== resume: --new again lists only what came after the watermark")
client("cred-guest", "read", "fn.agents", "--new")
client("cred-guest", "read", "fn.agents", "--new")
say("== reconcile the first post's frozen draft (already stored, no new number)")
client("cred-guest", "reconcile", S / "protected" / "draft-1.json")
say("== wrong channel")
raw = socket.create_connection(("127.0.0.1", port), 30); f = raw.makefile("rb"); say("  greeting", f.readline().decode().strip())
for l in ("GROUP fn.agents", "AUTHINFO USER guest", "POST", "QUIT"):
    raw.sendall(l.encode() + b"\r\n"); say("  (clear) %s -> %s" % (l, f.readline().decode().strip()))
raw.close()
client("cred-guest", "read", "fn.agents", "--all", "--plain")
say("== wrong secret (TLS)")
(W / "cred-wrong").write_text("guest not-the-password\n"); (W / "cred-wrong").chmod(0o600)
client("cred-wrong", "read", "fn.agents", "--all")
say("== wrong principal: ember is bound to E (posting-policy bound-logins)")
client("cred-ember", "post", "fn.agents", "--subject", "ember unsigned", "--message-id", "<prot-ember-unsigned@qual.invalid>",
       stdin=b"unsigned from a bound login\n", state="state-ember.json")
def carrier(keys, msgid, subject):
    src = S / "protected" / (subject.replace(" ", "-") + ".src"); out = src.with_suffix(".carrier")
    src.write_bytes(("From: ember <ember@fn.example.invalid>\r\nDate: Sat, 26 Sep 2026 07:00:00 +0000\r\nNewsgroups: fn.agents\r\n"
                     "Subject: %s\r\nMessage-ID: %s\r\n\r\nsigned\r\n" % (subject, msgid)).encode())
    for img in (I / "fn-host", I / "fn-host-developer"):
        r = subprocess.run([str(img), "--fn", "hybrid-sign-carrier", keys / "principal.bin", keys / "ed-public.bin", keys / "ed-secret.bin",
                            keys / "ml-public.pem", keys / "ml-private.pem", src, out], cwd=T, env=env, capture_output=True, timeout=180)
        if r.returncode == 0:
            return out.read_bytes()
    raise SystemExit("hybrid-sign-carrier failed: %r" % r.stderr[-300:])
def tls_post(user, pw, article):
    raw = socket.create_connection(("127.0.0.1", port), 30); f = raw.makefile("rb"); f.readline()
    raw.sendall(b"STARTTLS\r\n"); f.readline()
    t = ssl.create_default_context(cafile=str(cert)).wrap_socket(raw, server_hostname="127.0.0.1"); tf = t.makefile("rb")
    for l in ("AUTHINFO USER " + user, "AUTHINFO PASS " + pw, "POST"):
        t.sendall(l.encode() + b"\r\n"); rep = tf.readline().decode().strip()
    for line in article.splitlines(keepends=True):
        t.sendall(b"." + line if line.startswith(b".") else line)
    t.sendall(b".\r\n"); rep = tf.readline().decode().strip(); t.close(); return rep
pw = (W / "cred-ember").read_text().split()[1]
say("  ember POSTs a carrier signed by Q (another enrolled principal): %s" % tls_post("ember", pw, carrier(W / "keys-q", "<prot-ember-q@qual.invalid>", "signed by Q")))
say("  ember POSTs a carrier signed by E (its bound principal): %s" % tls_post("ember", pw, carrier(W / "keys", "<prot-ember-e@qual.invalid>", "signed by E")))
gpw = (W / "cred-guest").read_text().split()[1]
say("  guest (unbound) POSTs the carrier signed by Q: %s" % tls_post("guest", gpw, carrier(W / "keys-q", "<prot-guest-q@qual.invalid>", "guest carries Q")))
say("== service log decisions")
for l in (W / "fn.log").read_text("utf-8", "replace").splitlines():
    if "post login=" in l:
        say("  log| " + l[:220])

#!/usr/bin/env python3
"""qual-69046a76 item 2: on the node installed from the release tarball (its bin/fn),
a friend redeems an invitation code, is bound live to a signing principal, and posts
a SIGNED article as that principal (240); the served HDR :fn-verified and
:fn-enrollment (`active`) are read back; a session opened before a live rebind keeps
its binding (keys-and-accounts-2's case).  Usage: friends_signed.py FN WORK DEVIMG OPENSSL"""
import os, re, signal, socket, ssl, subprocess, sys, time
from pathlib import Path

FN, WORK, DEVIMG, OPENSSL = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]), sys.argv[4]
WORK.mkdir(parents=True, exist_ok=False)
ENV = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
ENV.pop("ACL2_SYSTEM_BOOKS", None)
P, Q = bytes([85]) * 32, bytes([86]) * 32
ED = {"A": ("833fe62409237b9d62ec77587520911e9a759cec1d19755b7da901b96dca3d42",
            "ec172b93ad5e563bf4932c70e1245034c35467ef2efd4d64ebf819683467e2bf"),
      "P": ("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"),
      "Q": ("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
            "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")}


def say(*a):
    print(*a, flush=True)


def run(name, argv, expect=None, stdin=None, show=True):
    r = subprocess.run([str(a) for a in argv], env=ENV, input=stdin, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, timeout=300)
    out = (r.stdout + r.stderr).decode("utf-8", "replace").strip()
    tag = "" if expect is None else (" OK" if r.returncode == expect else " UNEXPECTED(want %s)" % expect)
    say("STEP %s rc=%d%s" % (name, r.returncode, tag))
    if show:
        for l in out.splitlines()[-10:]:
            say("  | " + l[:220])
    return r.returncode, out


def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


port, tls_port = free_port(), free_port()
cert, key = WORK / "cert.pem", WORK / "key.pem"
subprocess.run([OPENSSL, "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key), "-out", str(cert), "-days", "2",
                "-nodes", "-subj", "/CN=127.0.0.1"], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=ENV)
control = WORK / "control.sock"
cfg = WORK / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\ntls_port = %d\ntls_cert = "%s"\ntls_key = "%s"\n'
               '[control]\npath = "%s"\n[log]\npath = "%s"\n[auth]\nprotected_only = true\n'
               % (WORK / "store", port, tls_port, cert, key, control, WORK / "fn.log"))
run("fn --version (the tarball's bin/fn)", [FN, "--version"])
run("init local.general", [FN, "operator", cfg, "init", "local.general"], expect=0)
run("policy set posting-policy bound-logins", [FN, "operator", cfg, "policy", "set", "posting-policy", "bound-logins"], expect=0)
run("principal set-password alice --posting (before the start: passwords are read at start)", [FN, "operator", cfg, "principal", "set-password", "alice", "--posting"],
    stdin=b"alice-secret\nalice-secret\n")
owner = subprocess.Popen([str(FN), "operator", str(cfg), "run"], env=ENV, stdout=subprocess.PIPE, stderr=open(WORK / "owner.err", "ab"))
seen = 0
t0 = time.time()
while seen < 2 and time.time() - t0 < 240:
    if owner.stdout.readline().startswith(b"LISTENING"):
        seen += 1
say("OWNER pid=%d LISTENING lines=%d after %.1f s" % (owner.pid, seen, time.time() - t0))


def tls():
    ctx = ssl.create_default_context(cafile=str(cert))
    ctx.check_hostname = False
    raw = socket.create_connection(("127.0.0.1", tls_port), timeout=60)
    s = ctx.wrap_socket(raw, server_hostname="127.0.0.1").makefile("rwb", buffering=0)
    s.readline()
    return s


def cmd(s, line, shown=None):
    s.write(line.encode() + b"\r\n")
    rep = s.readline().decode("utf-8", "replace").strip()
    say("  > %s -> %s" % (shown or line, rep))
    return rep


def multi(s):
    out = []
    while True:
        l = s.readline().decode("utf-8", "replace").rstrip("\r\n")
        if l == "." or not l and False:
            return out
        out.append(l)


def post(s, octets):
    if not cmd(s, "POST").startswith("340"):
        return "no 340"
    s.write(octets + b".\r\n")
    rep = s.readline().decode("utf-8", "replace").strip()
    say("  > POST <%d octets> -> %s" % (len(octets), rep))
    return rep


def login(user, pw):
    s = tls()
    cmd(s, "AUTHINFO USER " + user)
    cmd(s, "AUTHINFO PASS " + pw, "AUTHINFO PASS ***")
    return s


try:
    rc, out = run("account invite", [FN, "operator", cfg, "account", "invite", "--expires", "3600"], show=False)
    code = re.search(r"^([0-9a-f]{32})$", out, re.M).group(1)
    s = tls()
    cmd(s, "XREDEEM %s robin" % code, "XREDEEM <code> robin")
    cmd(s, "XREDEEM PASS correct-horse", "XREDEEM PASS ***")
    rc, listed = run("account list", [FN, "operator", cfg, "account", "list"])
    A = bytes.fromhex(re.search(r"redeemed robin ([0-9a-f]{64})", listed).group(1))
    say("  robin's account principal (bound at redemption): %s" % A.hex())
    keys = WORK / "keys"
    keys.mkdir()
    kk = {}
    for who, principal in (("A", A), ("P", P), ("Q", Q)):
        (keys / (who + ".bin")).write_bytes(principal)
        (keys / (who + "-ed.pub")).write_bytes(bytes.fromhex(ED[who][1]))
        (keys / (who + "-ed.sec")).write_bytes(bytes.fromhex(ED[who][0] + ED[who][1]))
        subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(keys / (who + "-ml.pem"))], check=True, env=ENV)
        subprocess.run([OPENSSL, "pkey", "-in", str(keys / (who + "-ml.pem")), "-pubout", "-out", str(keys / (who + "-ml.pub"))], check=True, env=ENV)
        kk[who] = [keys / (who + ".bin"), keys / (who + "-ed.pub"), keys / (who + "-ed.sec"), keys / (who + "-ml.pub"), keys / (who + "-ml.pem")]
    for gen, who in (("1", "P"), ("2", "Q"), ("3", "A")):
        run("hybrid-enroll %s generation %s (tarball bin/fn)" % (who, gen), [FN, "hybrid-enroll", control, gen, kk[who][0], kk[who][1], kk[who][3]], expect=0)

    def carrier(who, mid, subject):
        src, out = keys / (mid.strip("<>") + ".src"), keys / (mid.strip("<>") + ".carrier")
        src.write_bytes(("From: robin <robin@friend.example>\r\nDate: Sat, 26 Sep 2026 14:00:00 +0000\r\nNewsgroups: local.general\r\n"
                         "Subject: %s\r\nMessage-ID: %s\r\n\r\nsigned by %s\r\n" % (subject, mid, who)).encode())
        rc, _ = run("hybrid-sign-carrier %s (tarball bin/fn)" % mid, [FN, "hybrid-sign-carrier", *kk[who], src, out], show=False)
        if rc != 0:
            run("hybrid-sign-carrier %s (developer image as the client)" % mid, [DEVIMG, "--fn", "hybrid-sign-carrier", *kk[who], src, out], expect=0)
        return out.read_bytes()

    # the redeemed friend posts an article signed by its own account principal A
    s2 = login("robin", "correct-horse")
    cmd(s2, "GROUP local.general")
    rA = post(s2, carrier("A", "<robin-signed-a@friend.example>", "signed by robin's account principal"))
    say("RESULT redeemed-login-signed-as-its-account-principal=%s" % rA.startswith("240"))
    run("principal bind robin A (a redeemed account's login; live)", [FN, "operator", cfg, "principal", "bind", "robin", A.hex()])
    # keys-and-accounts-2's case on the tarball node, with an auth.toml login
    run("principal bind alice P (live)", [FN, "operator", cfg, "principal", "bind", "alice", P.hex()])
    a = login("alice", "alice-secret")
    say("  session A opened while alice is bound to P")
    cmd(a, "GROUP local.general")
    run("principal bind alice Q (live rebind)", [FN, "operator", cfg, "principal", "bind", "alice", Q.hex()])
    ra = post(a, carrier("P", "<alice-signed-p@friend.example>", "signed as P in the session opened before the rebind"))
    b = login("alice", "alice-secret")
    rb = post(b, carrier("P", "<alice-signed-p2@friend.example>", "signed as P after the rebind"))
    rq = post(b, carrier("Q", "<alice-signed-q@friend.example>", "signed as Q, the bound principal"))
    ru = post(b, b"From: alice <alice@friend.example>\r\nNewsgroups: local.general\r\nSubject: unsigned\r\n"
                 b"Message-ID: <alice-unsigned@friend.example>\r\n\r\nunsigned\r\n")
    say("RESULT session-A-keeps-P=%s new-session-P-refused=%s bound-Q-accepted=%s unsigned-refused=%s" % (
        ra.startswith("240"), rb.startswith("441"), rq.startswith("240"), ru.startswith("441")))
    r = tls()
    cmd(r, "GROUP local.general")
    for h in (":fn-verified", ":fn-enrollment"):
        for mid in ("<robin-signed-a@friend.example>", "<alice-signed-q@friend.example>", "<alice-signed-p@friend.example>"):
            rep = cmd(r, "HDR %s %s" % (h, mid))
            if rep.startswith("225"):
                for l in multi(r):
                    say("    " + l[:200])
    rep = cmd(r, "ARTICLE <robin-signed-a@friend.example>")
    if rep.startswith("220"):
        body = multi(r)
        say("    headers: %s" % [l[:100] for l in body[:12] if l.split(":")[0] in ("Path", "From", "Newsgroups", "Message-ID", "Injection-Info")])
    for x in (s2, a, b, r):
        try:
            cmd(x, "QUIT")
        except Exception:
            pass
finally:
    owner.send_signal(signal.SIGTERM)
    try:
        owner.wait(60)
    except subprocess.TimeoutExpired:
        owner.kill(); owner.wait()
    say("OWNER exit %s" % owner.returncode)
    log = (WORK / "fn.log").read_text(errors="replace") if (WORK / "fn.log").exists() else ""
    for l in log.splitlines():
        if "login=" in l or "account" in l or "bind" in l:
            say("  fn.log| " + l[:200])

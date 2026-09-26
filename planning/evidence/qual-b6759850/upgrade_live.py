#!/usr/bin/env python3
"""qual-b6759850 upgrade rehearsal on COPIES of the live node's store and fn.toml.

The live directory /tank/fn/node is only read (cp -a of store/, fn.toml, tls/ and
the fn-bbf52159 install).  Every step prints `STEP name rc=N` and the command's
output.  Only processes started here are stopped (by PID).  Secrets (auth.toml,
tls keys) stay on hbox; the log prints no password.
"""
import hashlib, json, os, re, shutil, socket, ssl, subprocess, sys, time
from pathlib import Path

S = Path("/tank/fn/scratch/qual-b6759850/upgrade-live")
T = Path("/tank/fn/scratch/qual-b6759850/tree")
I = Path("/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80")
LIVE = Path("/tank/fn/node")
OPENSSL = "/tank/fn/scratch/qual-b6759850/bin/test-openssl"
LOGIN, SECRET = "qual", "qual-b6759850-rehearsal"
P = bytes([85]) * 32
ED_OLD = ("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
          "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
ED_NEW = ("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
          "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")
POP_TAG = b"fn-key-succession-pop-v1"

ENV = dict(os.environ, ACL2_CUSTOMIZATION="NONE",
           FN_OPENSSL_PREFIX="/tank/fn/toolchains/openssl-3.5.8")
ENV.pop("ACL2_SYSTEM_BOOKS", None)
ENV.pop("LD_LIBRARY_PATH", None)
started = []


def say(*a):
    print(*a, flush=True)


def sh(name, argv, expect=None, stdin=None, env=None, quiet=False):
    r = subprocess.run([str(a) for a in argv], cwd=T, env=env or ENV, input=stdin,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600)
    out = (r.stdout + r.stderr).decode("utf-8", "replace").strip()
    tag = "" if expect is None else (" OK" if r.returncode == expect else " UNEXPECTED(want %s)" % expect)
    say("STEP %s rc=%d%s" % (name, r.returncode, tag))
    if not quiet:
        for line in out.splitlines()[-25:]:
            say("  | " + line)
    return r.returncode, out


def tree_digest(root):
    rows = []
    for p in sorted(Path(root).rglob("*")):
        if p.is_file() and not p.is_symlink() and p.name not in ("auth.toml",):
            rows.append("%s  %s" % (hashlib.sha256(p.read_bytes()).hexdigest(), p.relative_to(root)))
    return rows


def copytree(src, dst):
    if dst.exists():
        shutil.rmtree(dst)
    subprocess.run(["cp", "-a", str(src), str(dst)], check=True)
    for sock in ("control.sock",):
        q = dst / sock
        if q.exists() and not q.is_file():
            q.unlink()


def free_port():
    with socket.socket() as p:
        p.bind(("127.0.0.1", 0))
        return p.getsockname()[1]


def config_for(work, port):
    text = (LIVE / "fn.toml").read_text()
    text = text.replace(str(LIVE), str(work))
    text = re.sub(r'host = "[^"]*"', 'host = "127.0.0.1"', text, count=1)
    text = re.sub(r"port = \d+", "port = %d" % port, text, count=1)
    (work / "log").mkdir(exist_ok=True)
    cfg = work / "fn.toml"
    cfg.write_text(text)
    return cfg


def start(image_argv, cfg, name):
    err = open(S / (name + ".err"), "ab")
    p = subprocess.Popen([str(a) for a in image_argv] + ["operator", str(cfg), "run"], cwd=T,
                         env=ENV, stdout=subprocess.PIPE, stderr=err)
    started.append(p)
    line = b""
    deadline = time.time() + 180
    while time.time() < deadline:
        line = p.stdout.readline()
        if not line or line.startswith(b"LISTENING"):
            break
    say("OWNER %s pid=%d announce=%r" % (name, p.pid, line.decode().strip()))
    return p


def stop(p, name):
    p.terminate()
    try:
        p.wait(120)
    except subprocess.TimeoutExpired:
        p.kill()
        p.wait()
    rest = p.stdout.read().decode("utf-8", "replace") if p.stdout else ""
    risk = [l for l in rest.splitlines() if "invariant-risk" in l.lower()]
    blank = sum(1 for l in rest.splitlines() if not l.strip())
    say("OWNER %s pid=%d exit=%s stdout-lines-after-LISTENING=%d blank=%d invariant-risk-lines=%d" % (
        name, p.pid, p.returncode, len(rest.splitlines()), blank, len(risk)))
    for l in rest.splitlines()[:12]:
        say("  stdout| " + l[:200])


class Nntp:
    def __init__(self, port, cert, login=True):
        raw = socket.create_connection(("127.0.0.1", port), 60)
        f = raw.makefile("rb")
        self.greeting = f.readline().decode().rstrip()
        raw.sendall(b"STARTTLS\r\n")
        self.starttls = f.readline().decode().rstrip()
        ctx = ssl.create_default_context(cafile=str(cert))
        ctx.check_hostname = False
        self.s = ctx.wrap_socket(raw, server_hostname="127.0.0.1")
        self.f = self.s.makefile("rb")
        if login:
            self.cmd("AUTHINFO USER " + LOGIN)
            self.auth = self.cmd("AUTHINFO PASS " + SECRET, show=False)

    def cmd(self, line, show=True):
        self.s.sendall(line.encode() + b"\r\n")
        rep = self.f.readline().decode("utf-8", "replace").rstrip()
        if show:
            say("  > %s  -> %s" % (line, rep))
        return rep

    def cmdm(self, line):
        rep = self.cmd(line)
        if rep[:3] in ("211", "215", "220", "221", "224", "225", "230", "231", "282") and not (
                rep.startswith("211") and not line.upper().startswith("LISTGROUP")):
            body = self.multi()
            say("    %s" % body[:40])
            return rep, body
        return rep, []

    def multi(self):
        out = []
        while True:
            raw = self.f.readline()
            l = raw.decode("utf-8", "replace").rstrip("\r\n")
            if l == "." or raw == b"":
                return out
            out.append(l)

    def post(self, octets):
        first = self.cmd("POST")
        if not first.startswith("340"):
            return first
        for line in octets.splitlines(keepends=True):
            self.s.sendall(b"." + line if line.startswith(b".") else line)
        self.s.sendall(b".\r\n")
        rep = self.f.readline().decode("utf-8", "replace").rstrip()
        say("  > POST <%d octets>  -> %s" % (len(octets), rep))
        return rep

    def article(self, msgid):
        rep = self.cmd("ARTICLE " + msgid)
        body = self.multi() if rep.startswith("220") else []
        return rep, body

    def close(self):
        try:
            self.cmd("QUIT")
        except Exception:
            pass
        self.s.close()


def hex_lines(name, octets):
    text = octets.hex()
    return b"".join("{}: {}\r\n".format(name, text[i:i + 64]).encode("ascii")
                    for i in range(0, len(text), 64))


Q = bytes([102]) * 32   # a second principal, enrolled, never bound to the login


def status_fields(out):
    f = {}
    for line in out.splitlines():
        for w in line.split():
            if "=" in w:
                k, v = w.split("=", 1)
                f.setdefault(k, v)
    return f


def plain(port, lines):
    """One clear connection: send each line, print each reply (wrong-channel probes)."""
    raw = socket.create_connection(("127.0.0.1", port), 60)
    f = raw.makefile("rb")
    say("  (clear) greeting %s" % f.readline().decode().rstrip())
    reps = []
    for l in lines:
        raw.sendall(l.encode() + b"\r\n")
        rep = f.readline().decode("utf-8", "replace").rstrip()
        say("  (clear) > %s  -> %s" % (l if not l.startswith("AUTHINFO PASS") else "AUTHINFO PASS ***", rep))
        reps.append(rep)
    raw.close()
    return reps


def client(port, cert, *args, stdin=None, state=None):
    """tools/fn_client.py over STARTTLS as the bound login (credentials by env, never argv)."""
    env = dict(ENV, FN_CLIENT_USER=LOGIN, FN_CLIENT_PASSWORD=SECRET, FN_CLIENT_FROM="Qual <qual@example.invalid>")
    argv = [sys.executable, str(T / "tools" / "fn_client.py")] + [str(a) for a in args] + [
        "--node", "127.0.0.1:%d" % port, "--cafile", str(cert), "--state", str(state or (S / "client-state.json"))]
    r = subprocess.run(argv, cwd=T, env=env, input=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
    out = (r.stdout + r.stderr).decode("utf-8", "replace").strip()
    say("STEP fn_client %s rc=%d" % (" ".join(str(a) for a in args[:3]), r.returncode))
    for line in out.splitlines()[-14:]:
        say("  | " + line[:220])
    return r.returncode, out


def main():
    NEW = S / "fn-b6759850" / "bin" / "fn"
    OLD = S / "fn-bbf52159" / "bin" / "fn"
    DEV = I / "fn-host-developer"
    if S.exists():
        shutil.rmtree(S)
    S.mkdir(parents=True)
    say("# rehearsal start %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))

    # 0. copies ---------------------------------------------------------------
    live_before = tree_digest(LIVE / "store")
    pristine = S / "pristine"
    pristine.mkdir()
    subprocess.run(["cp", "-a", str(LIVE / "store"), str(pristine / "store")], check=True)
    subprocess.run(["cp", "-a", str(LIVE / "tls"), str(pristine / "tls")], check=True)
    subprocess.run(["cp", "-a", str(LIVE / "fn-bbf52159"), str(S / "fn-bbf52159")], check=True)
    q = pristine / "store" / "control.sock"
    if q.exists() and not q.is_file():
        q.unlink()
    live_rows = tree_digest(pristine / "store")
    (S / "pristine-store.sha256").write_text("\n".join(live_rows) + "\n")
    say("STEP copy-live-store files=%d (auth.toml excluded from the digest list)" % len(live_rows))
    for r in live_rows:
        say("  | " + r)
    say("  frontier file (pristine): %r" % (pristine / "store" / "allocation-frontier.json").read_bytes())
    rc, out = sh("install-native b6759850", ["env", "PREFIX=%s" % (S / "fn-b6759850"),
                                             "FN_NATIVE_HOST=%s" % (I / "fn-host"),
                                             "FN_NATIVE_SOURCE_REVISION=b675985074cf14b009204f6eb3e5409f4a025a80",
                                             "sh", "packaging/install-native.sh"], expect=0)
    say("  installed bin/fn sha256 %s; bbf52159 bin/fn sha256 %s" % (
        hashlib.sha256(NEW.read_bytes()).hexdigest(), hashlib.sha256(OLD.read_bytes()).hexdigest()))

    work = S / "w"
    copytree(pristine, work)
    port = free_port()
    cfg = config_for(work, port)
    say("CONFIG %s:\n%s" % (cfg, cfg.read_text()))
    store = work / "store"
    cert = work / "tls" / "cert.pem"

    # 1b. the live copy under the new per-article accounting -------------------
    rc, old_status = sh("bbf52159 status offline (the deployed accounting)", [OLD, "operator", cfg, "status"], expect=0)
    rc, new_status = sh("b6759850 status offline (per-article accounting)", [NEW, "operator", cfg, "status"], expect=0)
    fo, fn_ = status_fields(old_status), status_fields(new_status)
    for k in ("transactions", "articles", "transactions-used", "transactions-budget", "bytes-used", "history-bound",
              "charge-reserved", "charge-capacity", "max-transactions", "max-history-octets", "max-article-octets",
              "max-open-suffix", "history-marker", "format"):
        say("  1b %-22s bbf52159=%s b6759850=%s" % (k, fo.get(k), fn_.get(k)))
    try:
        used, bound = int(fn_["bytes-used"]), int(fn_["history-bound"])
        tu, tb = int(fn_["transactions-used"]), int(fn_["transactions-budget"])
        say("FACT-1b opens=%s bytes-used=%d history-bound=%d below-H=%s headroom-octets=%d transactions=%d/%d headroom-transactions=%d" % (
            rc == 0, used, bound, used < bound, bound - used, tu, tb, tb - tu))
    except (KeyError, ValueError) as e:
        say("FACT-1b could not parse status: %r" % e)
    for line in new_status.splitlines():
        if line.startswith(("maintenance-reserve", "headroom", "profile", "open")):
            say("  1b line| " + line)
    sh("b6759850 health offline", [NEW, "operator", cfg, "health"])
    sh("b6759850 store needs-upgrade (format 8 unmarked)", [NEW, "operator", cfg, "store", "needs-upgrade"])
    sh("b6759850 store rollback-check KEPT format-7 config (in the live store)",
       [NEW, "operator", cfg, "store", "rollback-check", store / "config.json.format-7"])
    sh("b6759850 store rollback-check --snapshot of itself (nothing lost)",
       [NEW, "operator", cfg, "store", "rollback-check", "--snapshot", pristine / "store"])

    # 1c-i. does an open alone (no commit) change the frontier? ----------------
    o0 = S / "open-only"
    copytree(pristine, o0)
    cfg_o0 = config_for(o0, free_port())
    ow = start([NEW], cfg_o0, "b675-open-only")
    stop(ow, "b675-open-only")
    say("  frontier after an open with no commit: %r (pristine %r)" % (
        (o0 / "store" / "allocation-frontier.json").read_bytes(), (pristine / "store" / "allocation-frontier.json").read_bytes()))
    sh("bbf52159 status after b6759850 opened with no commit", [OLD, "operator", cfg_o0, "status"])

    # 1c-ii. snapshot before the deploy ---------------------------------------
    snap = S / "snapshot-pre-deploy"
    copytree(work, snap)
    say("STEP snapshot-pre-deploy (cp -a of the stopped store copy)")

    # 2. protected ordinary use on the new owner -------------------------------
    sh("principal set-password qual --principal P --posting",
       [NEW, "operator", cfg, "principal", "set-password", LOGIN, "--principal", P.hex(), "--posting"],
       stdin=(SECRET + "\n" + SECRET + "\n").encode(), quiet=False)
    sh("group create control.cancel", [NEW, "operator", cfg, "group", "create", "control.cancel"])
    owner = start([NEW], cfg, "b675-deploy")
    rc, live_status = sh("status live (owner running)", [NEW, "operator", cfg, "status"], expect=0)
    rc, off_status = (None, None)
    sh("health live", [NEW, "operator", cfg, "health"])
    say("  wrong channel: AUTHINFO on the clear connection")
    plain(port, ["GROUP fn.agents", "AUTHINFO USER " + LOGIN, "QUIT"])
    say("  wrong secret over TLS:")
    cbad = Nntp(port, cert, login=False)
    cbad.cmd("AUTHINFO USER " + LOGIN)
    say("  > AUTHINFO PASS (wrong)  -> %s" % cbad.cmd("AUTHINFO PASS not-the-secret", show=False))
    cbad.close()
    # the real client: post, read, reply, resume
    rc, out = client(port, cert, "groups")
    rc, out = client(port, cert, "read", "fn.agents", "--all")
    body1 = b"qual-b6759850 protected ordinary use: first post\n"
    rc, out = client(port, cert, "post", "fn.agents", "--subject", "qual b675 ordinary", "--message-id",
                     "<qual-b675-ordinary@example.invalid>", "--draft", S / "draft-ordinary.json", stdin=body1)
    rc, out = client(port, cert, "show", "<qual-b675-ordinary@example.invalid>")
    rc, out = client(port, cert, "post", "fn.agents", "--subject", "Re: qual b675 ordinary", "--message-id",
                     "<qual-b675-reply@example.invalid>", "--references", "<qual-b675-ordinary@example.invalid>",
                     stdin=b"a reply over the same protected session kind\n")
    rc, out = client(port, cert, "read", "fn.agents", "--new")
    rc, out = client(port, cert, "post", "fn.agents", "--subject", "qual b675 after resume", "--message-id",
                     "<qual-b675-later@example.invalid>", stdin=b"posted after the watermark\n")
    rc, out = client(port, cert, "read", "fn.agents", "--new")
    say("  resume: the second --new read lists only what came after the first")
    rc, out = client(port, cert, "reconcile", S / "draft-ordinary.json")
    # tin-shaped supplied Path (D32), the resend, signed as P, signed as Q (wrong principal), XPAT, cancel
    keys = S / "keys"
    keys.mkdir()
    (keys / "p.bin").write_bytes(P)
    (keys / "q.bin").write_bytes(Q)
    kset = {}
    for name, (seed, public) in (("old", ED_OLD), ("new", ED_NEW)):
        (keys / (name + "-ed.pub")).write_bytes(bytes.fromhex(public))
        (keys / (name + "-ed.sec")).write_bytes(bytes.fromhex(seed + public))
        subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(keys / (name + "-ml.pem"))], check=True)
        subprocess.run([OPENSSL, "pkey", "-in", str(keys / (name + "-ml.pem")), "-pubout", "-out",
                        str(keys / (name + "-ml.pub.pem"))], check=True)
        kset[name] = {"edp": keys / (name + "-ed.pub"), "eds": keys / (name + "-ed.sec"),
                      "mlp": keys / (name + "-ml.pub.pem"), "mls": keys / (name + "-ml.pem")}
    control = store / "control.sock"
    for gen, who, k in (("1", "p.bin", "old"), ("2", "q.bin", "new")):
        rc, _ = sh("hybrid-enroll %s gen %s (production image)" % (who, gen),
                   [NEW, "hybrid-enroll", control, gen, keys / who, kset[k]["edp"], kset[k]["mlp"]])
        if rc != 0:
            sh("hybrid-enroll %s gen %s (developer image as the client)" % (who, gen),
               [DEV, "--fn", "hybrid-enroll", control, gen, keys / who, kset[k]["edp"], kset[k]["mlp"]], expect=0)

    def carrier(who, k, source, stem):
        src = keys / (stem + ".src")
        src.write_bytes(source)
        out = keys / (stem + ".carrier")
        rc, _ = sh("hybrid-sign-carrier %s" % stem, [NEW, "hybrid-sign-carrier", keys / who, k["edp"], k["eds"],
                                                     k["mlp"], k["mls"], src, out], quiet=True)
        if rc != 0:
            sh("hybrid-sign-carrier %s (developer image as the client)" % stem,
               [DEV, "--fn", "hybrid-sign-carrier", keys / who, k["edp"], k["eds"], k["mlp"], k["mls"], src, out],
               expect=0, quiet=True)
        return out.read_bytes()

    def header(msgid, group, subject, extra=b""):
        return ("From: Qual <qual@example.invalid>\r\nDate: Sat, 26 Sep 2026 06:00:00 +0000\r\n"
                "Newsgroups: {}\r\nSubject: {}\r\nMessage-ID: {}\r\n".format(group, subject, msgid)).encode() + extra + b"\r\n"

    c = Nntp(port, cert)
    say("  greeting %s / STARTTLS %s / AUTHINFO %s" % (c.greeting, c.starttls, c.auth))
    c.cmd("GROUP fn.agents")
    tin_id = "<qual-b675-tin@example.invalid>"
    tin = (b"Path: not-for-mail\r\nFrom: Qual <qual@example.invalid>\r\nNewsgroups: fn.agents\r\n"
           b"Subject: qual rehearsal tin-shaped\r\nMessage-ID: " + tin_id.encode() +
           b"\r\nDate: Sat, 26 Sep 2026 06:00:00 +0000\r\nUser-Agent: TIN/2.6.2-20221225 (UNIX) (Linux/6)\r\n"
           b"\r\nsupplied Path, as tin sends it\r\n")
    c.post(tin)
    rep, art = c.article(tin_id)
    say("  tin article Path: %s" % [l for l in art if l.lower().startswith("path:")])
    say("  tin resend: %s" % c.post(tin))
    changed = tin.replace(b"as tin sends it", b"as tin sends it, one byte changed!")
    say("  tin changed source, same Message-ID: %s" % c.post(changed))
    signed_id = "<qual-b675-signed@example.invalid>"
    signed = carrier("p.bin", kset["old"], header(signed_id, "fn.agents", "qual rehearsal signed") + b"signed body\r\n", "signed")
    c.post(signed)
    c.cmdm("HDR :fn-verified " + signed_id)
    say("  signed resend: %s" % c.post(signed))
    qid = "<qual-b675-wrong-principal@example.invalid>"
    say("  WRONG PRINCIPAL (signed by Q, login bound to P): %s" % c.post(
        carrier("q.bin", kset["new"], header(qid, "fn.agents", "qual rehearsal signed by Q") + b"q body\r\n", "qsigned")))
    c.cmd("GROUP fn.agents")
    c.cmdm("XPAT Subject 1- *qual rehearsal*")
    cancel_id = "<qual-b675-cancel@example.invalid>"
    c.post(carrier("p.bin", kset["old"], header(cancel_id, "fn.agents", "cmsg cancel " + signed_id,
                                                b"Control: cancel " + signed_id.encode() + b"\r\n") + b"cancel\r\n", "cancel"))
    c.close()
    time.sleep(1)
    c = Nntp(port, cert)
    say("  fresh reader after the cancel:")
    c.article(signed_id)
    c.cmdm("LISTGROUP control.cancel")
    c.close()
    stop(owner, "b675-deploy")
    rc, off_status = sh("status offline after the deploy owner", [NEW, "operator", cfg, "status"], expect=0)
    say("  frontier after commits: %r" % (store / "allocation-frontier.json").read_bytes())
    sh("recover after the deploy owner", [NEW, "operator", cfg, "recover"], expect=0)

    # 1c-iii. bbf52159 against the written store (format-3 frontier) ------------
    r0 = S / "old-on-written"
    copytree(work, r0)
    cfg_r0 = config_for(r0, free_port())
    sh("bbf52159 status on the store b6759850 wrote (expected refusal)", [OLD, "operator", cfg_r0, "status"])
    sh("bbf52159 recover on the store b6759850 wrote (expected refusal)", [OLD, "operator", cfg_r0, "recover"])
    sh("b6759850 store rollback-check KEPT format-7 config after the writes",
       [NEW, "operator", cfg, "store", "rollback-check", store / "config.json.format-7"])
    rc, out = sh("b6759850 store rollback-check --snapshot SNAPSHOT (the loss count)",
                 [NEW, "operator", cfg, "store", "rollback-check", "--snapshot", snap / "store"])
    say("QUOTE-VERB " + " / ".join(out.splitlines()))
    doc = (T / "docs" / "operator.md").read_text()
    i = doc.find("Restoring a pre-migration snapshot loses")
    say("QUOTE-DOC " + " ".join(doc[i:i + 90].split()))
    say("  docs/operator.md mentions frontier format 3 / bbf52159 unreadable: %s" % (
        "format 3" in doc or "format-3" in doc))
    sh("rollback-check --snapshot of an unrelated store (expected refusal snapshot-not-a-prefix)",
       [NEW, "operator", cfg, "store", "rollback-check", "--snapshot", o0 / "store"])

    # 1c-iv. rollback by the snapshot ----------------------------------------
    r2 = S / "rollback-snapshot"
    copytree(snap, r2)
    cfg_r2 = config_for(r2, free_port())
    sh("bbf52159 recover on the restored snapshot", [OLD, "operator", cfg_r2, "recover"], expect=0)
    sh("bbf52159 status on the restored snapshot", [OLD, "operator", cfg_r2, "status"], expect=0)
    o = start([OLD], cfg_r2, "bbf5-rollback-snapshot")
    c = Nntp(int(re.search(r"port = (\d+)", cfg_r2.read_text()).group(1)), r2 / "tls" / "cert.pem", login=False)
    c.cmd("GROUP fn.agents")
    c.close()
    stop(o, "bbf5-rollback-snapshot")
    same = sorted(x for x in tree_digest(r2 / "store") if x.split("  ")[1].startswith("transactions/"))
    say("  restored snapshot transactions equal the pristine ones: %s" % (
        same == sorted(x for x in live_rows if x.split("  ")[1].startswith("transactions/"))))

    # 1c-v. the marker two-step on a copy of the deployed store -----------------
    mk = S / "marker"
    copytree(work, mk)
    cfg_mk = config_for(mk, free_port())
    msnap = S / "snapshot-pre-marker"
    copytree(mk, msnap)
    sh("store upgrade-profile --history-marker required", [NEW, "operator", cfg_mk, "store",
                                                          "upgrade-profile", "--history-marker", "required"], expect=0)
    sh("status after required", [NEW, "operator", cfg_mk, "status"], expect=0)
    sh("store needs-upgrade (required)", [NEW, "operator", cfg_mk, "store", "needs-upgrade"])
    sh("rollback-check KEPT format-7 config after required (expected refused)",
       [NEW, "operator", cfg_mk, "store", "rollback-check", mk / "store" / "config.json.format-7"])
    rc, out = sh("rollback-check --snapshot pre-marker", [NEW, "operator", cfg_mk, "store", "rollback-check", "--snapshot", msnap / "store"])
    rc, out = sh("rollback-check --snapshot pre-deploy", [NEW, "operator", cfg_mk, "store", "rollback-check", "--snapshot", snap / "store"])
    sh("downgrade --history-marker unmarked (expected refusal)", [NEW, "operator", cfg_mk, "store",
                                                                 "upgrade-profile", "--history-marker", "unmarked"])
    sh("bbf52159 status on the required store (expected refusal: frontier)", [OLD, "operator", cfg_mk, "status"])
    mport = int(re.search(r"port = (\d+)", cfg_mk.read_text()).group(1))
    o = start([NEW], cfg_mk, "b675-required")
    c = Nntp(mport, mk / "tls" / "cert.pem")
    c.cmd("GROUP fn.agents")
    c.post(header("<qual-b675-required@example.invalid>", "fn.agents", "qual rehearsal required") + b"after required\r\n")
    c.close()
    stop(o, "b675-required")
    sh("recover after a commit on the required store", [NEW, "operator", cfg_mk, "recover"], expect=0)
    for label, action in (("newest transaction file removed", "txn"), ("marker removed", "marker")):
        cc = S / ("marker-cut-" + action)
        copytree(mk, cc)
        cfg_cc = config_for(cc, free_port())
        if action == "txn":
            newest = sorted((cc / "store" / "transactions").iterdir())[-1]
            newest.unlink()
        else:
            (cc / "store" / "committed-history.json").unlink()
        sh("required: %s, recover (expected refusal)" % label, [NEW, "operator", cfg_cc, "recover"])
        sh("required: %s, status (expected refusal)" % label, [NEW, "operator", cfg_cc, "status"])
    live_after = tree_digest(LIVE / "store")
    say("  live store digest unchanged by this run (read before/after, auth.toml excluded): %s" % (live_before == live_after))
    say("# rehearsal end %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))


if __name__ == "__main__":
    try:
        main()
    finally:
        for p in started:
            if p.poll() is None:
                p.kill()
                p.wait()

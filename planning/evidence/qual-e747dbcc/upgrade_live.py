#!/usr/bin/env python3
"""qual-e747dbcc upgrade rehearsal on COPIES of the live node's store and fn.toml.

The live directory /tank/fn/node is only read (cp -a of store/, fn.toml, tls/ and
the fn-c3420013 install).  Every step prints `STEP name rc=N` and the command's
output.  Only processes started here are stopped (by PID).  Secrets (auth.toml,
tls keys) stay on hbox; the log prints no password.
"""
import hashlib, json, os, re, shutil, socket, ssl, subprocess, sys, time
from pathlib import Path

S = Path("/tank/fn/scratch/qual-e747dbcc/upgrade-live")
T = Path("/tank/fn/scratch/qual-e747dbcc/tree")
I = Path("/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6")
LIVE = Path("/tank/fn/node")
OPENSSL = "/tank/fn/scratch/qual-e747dbcc/bin/test-openssl"
LOGIN, SECRET = "qual", "qual-e747dbcc-rehearsal"
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
    say("OWNER %s pid=%d exit=%s" % (name, p.pid, p.returncode))


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


def main():
    NEW = S / "fn-e747dbcc" / "bin" / "fn"
    OLD = S / "fn-c3420013" / "bin" / "fn"
    DEV = I / "fn-host-developer"
    if S.exists():
        shutil.rmtree(S)
    S.mkdir(parents=True)
    say("# rehearsal start %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))

    # 0. copies ---------------------------------------------------------------
    pristine = S / "pristine"
    pristine.mkdir()
    subprocess.run(["cp", "-a", str(LIVE / "store"), str(pristine / "store")], check=True)
    subprocess.run(["cp", "-a", str(LIVE / "tls"), str(pristine / "tls")], check=True)
    subprocess.run(["cp", "-a", str(LIVE / "fn-c3420013"), str(S / "fn-c3420013")], check=True)
    q = pristine / "store" / "control.sock"
    if q.exists() and not q.is_file():
        q.unlink()
    live_rows = tree_digest(pristine / "store")
    (S / "pristine-store.sha256").write_text("\n".join(live_rows) + "\n")
    say("STEP copy-live-store files=%d (auth.toml excluded from the digest list)" % len(live_rows))
    for r in live_rows:
        say("  | " + r)
    # install the candidate as a deploy would
    rc, out = sh("install-native e747dbcc", ["env", "PREFIX=%s" % (S / "fn-e747dbcc"),
                                             "FN_NATIVE_HOST=%s" % (I / "fn-host"),
                                             "FN_NATIVE_SOURCE_REVISION=e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6",
                                             "sh", "packaging/install-native.sh"], expect=0)

    work = S / "w"
    copytree(pristine, work)
    port = free_port()
    cfg = config_for(work, port)
    say("CONFIG %s:\n%s" % (cfg, cfg.read_text()))
    store = work / "store"
    cert = work / "tls" / "cert.pem"

    # 1. baseline under c3420013 and the new image offline --------------------
    sh("c3420013 status (format 7, offline)", [OLD, "operator", cfg, "status"], expect=0)
    sh("e747dbcc status offline on the format-7 store", [NEW, "operator", cfg, "status"], expect=0)
    sh("e747dbcc store needs-upgrade (format 7)", [NEW, "operator", cfg, "store", "needs-upgrade"])

    # 2. the new owner on the format-7 store (deploy step 1), live status ----
    owner = start([NEW], cfg, "e747-format7")
    sh("e747dbcc status live (owner running, format 7)", [NEW, "operator", cfg, "status"], expect=0)
    c = Nntp(port, cert, login=False)
    say("  greeting %s / STARTTLS %s" % (c.greeting, c.starttls))
    c.cmd("GROUP fn.agents")
    c.close()
    stop(owner, "e747-format7")
    sh("e747dbcc status offline after the first owner", [NEW, "operator", cfg, "status"], expect=0)
    say("  marker after first owner: %s" % hashlib.sha256((store / "committed-history.json").read_bytes()).hexdigest())

    # 3. snapshot before migration (the rollback for the marker step) ---------
    snap = S / "snapshot-pre-migration"
    copytree(work, snap)
    say("STEP snapshot-pre-migration (cp -a of the stopped store)")

    # 4. format 7 -> 8, keeping config.json --------------------------------
    subprocess.run(["cp", "-p", str(store / "config.json"), str(store / "config.json.format-7")], check=True)
    say("  kept config.json sha256 %s" % hashlib.sha256((store / "config.json").read_bytes()).hexdigest())
    sh("store upgrade-profile (7 to 8, no flag)", [NEW, "operator", cfg, "store", "upgrade-profile"], expect=0)
    sh("status after 7-to-8", [NEW, "operator", cfg, "status"], expect=0)
    sh("store needs-upgrade (format 8)", [NEW, "operator", cfg, "store", "needs-upgrade"])
    sh("store rollback-check KEPT-CONFIG", [NEW, "operator", cfg, "store", "rollback-check",
                                            store / "config.json.format-7"], expect=0)

    # 4a. rollback of the 7-to-8 step on a copy --------------------------------
    r1 = S / "rollback-78"
    copytree(work, r1)
    cfg_r1 = config_for(r1, free_port())
    sh("c3420013 status on the format-8 copy (expected refusal)", [OLD, "operator", cfg_r1, "status"])
    subprocess.run(["cp", "-p", str(r1 / "store" / "config.json.format-7"), str(r1 / "store" / "config.json")], check=True)
    sh("c3420013 status after restoring the kept config.json", [OLD, "operator", cfg_r1, "status"], expect=0)
    o = start([OLD], cfg_r1, "c342-rollback-78")
    c = Nntp(int(re.search(r"port = (\d+)", cfg_r1.read_text()).group(1)), r1 / "tls" / "cert.pem", login=False)
    c.cmd("GROUP fn.agents")
    c.close()
    stop(o, "c342-rollback-78")

    # 5. the marker requirement ---------------------------------------------
    sh("store upgrade-profile --history-marker required", [NEW, "operator", cfg, "store",
                                                          "upgrade-profile", "--history-marker", "required"], expect=0)
    sh("status after required", [NEW, "operator", cfg, "status"], expect=0)
    sh("store needs-upgrade (required)", [NEW, "operator", cfg, "store", "needs-upgrade"])
    sh("store rollback-check KEPT-CONFIG after required", [NEW, "operator", cfg, "store", "rollback-check",
                                                          store / "config.json.format-7"])
    sh("c3420013 status on the required store (expected refusal)", [OLD, "operator", cfg, "status"])
    sh("downgrade --history-marker unmarked (expected refusal)", [NEW, "operator", cfg, "store",
                                                                 "upgrade-profile", "--history-marker", "unmarked"])

    # 5a'. what the kept format-7 config.json does to a required store (a copy)
    r3 = S / "rollback-kept-after-required"
    copytree(work, r3)
    cfg_r3 = config_for(r3, free_port())
    subprocess.run(["cp", "-p", str(r3 / "store" / "config.json.format-7"), str(r3 / "store" / "config.json")], check=True)
    sh("kept format-7 config.json restored over the required store: c3420013 status", [OLD, "operator", cfg_r3, "status"])
    sh("same: c3420013 recover", [OLD, "operator", cfg_r3, "recover"])
    sh("same: e747dbcc status (the requirement is gone?)", [NEW, "operator", cfg_r3, "status"])
    os.rename(r3 / "store" / "committed-history.json", S / "r3-marker")
    sh("same, marker removed: e747dbcc recover (legacy open admits?)", [NEW, "operator", cfg_r3, "recover"])

    # 5a. rollback by the snapshot ------------------------------------------
    r2 = S / "rollback-snapshot"
    copytree(snap, r2)
    cfg_r2 = config_for(r2, free_port())
    sh("c3420013 recover on the restored snapshot", [OLD, "operator", cfg_r2, "recover"], expect=0)
    sh("c3420013 status on the restored snapshot", [OLD, "operator", cfg_r2, "status"], expect=0)
    o = start([OLD], cfg_r2, "c342-rollback-snapshot")
    c = Nntp(int(re.search(r"port = (\d+)", cfg_r2.read_text()).group(1)), r2 / "tls" / "cert.pem", login=False)
    c.cmd("GROUP fn.agents")
    c.cmd("GROUP fn.announce")
    c.close()
    stop(o, "c342-rollback-snapshot")
    same = [x for x in tree_digest(r2 / "store") if "/transactions/" in "/" + x.split("  ")[1] or x.split("  ")[1].startswith("transactions/")]
    say("  restored snapshot transactions equal the pristine ones: %s" % (
        sorted(same) == sorted(x for x in live_rows if x.split("  ")[1].startswith("transactions/"))))

    # 5b. the one-command variant (format 7 straight to required) -------------
    one = S / "one-step"
    copytree(pristine, one)
    cfg_one = config_for(one, free_port())
    sh("one-step: upgrade-profile --history-marker required from format 7",
       [NEW, "operator", cfg_one, "store", "upgrade-profile", "--history-marker", "required"], expect=0)
    sh("one-step: status", [NEW, "operator", cfg_one, "status"], expect=0)
    txns = sorted((one / "store" / "transactions").iterdir())
    newest = txns[-1]
    os.rename(newest, S / "one-step-newest.txn")
    sh("one-step: newest transaction file removed, recover (expected refusal)", [NEW, "operator", cfg_one, "recover"])
    os.rename(S / "one-step-newest.txn", newest)
    os.rename(one / "store" / "committed-history.json", S / "one-step-marker")
    sh("one-step: marker removed, recover (expected marker-missing)", [NEW, "operator", cfg_one, "recover"])
    os.rename(S / "one-step-marker", one / "store" / "committed-history.json")
    sh("one-step: restored, recover", [NEW, "operator", cfg_one, "recover"], expect=0)

    # 6. served surface on the migrated copy (format 8, required) -------------
    sh("principal set-password qual --principal P --posting",
       [NEW, "operator", cfg, "principal", "set-password", LOGIN, "--principal", P.hex(), "--posting"],
       stdin=(SECRET + "\n" + SECRET + "\n").encode(), quiet=False)
    sh("group create control.cancel", [NEW, "operator", cfg, "group", "create", "control.cancel"])
    sh("group create fn.keys", [NEW, "operator", cfg, "group", "create", "fn.keys"])
    owner = start([NEW], cfg, "e747-required")
    sh("status live (required)", [NEW, "operator", cfg, "status"], expect=0)
    keys = S / "keys"
    keys.mkdir()
    (keys / "p.bin").write_bytes(P)
    kset = {}
    for name, (seed, public) in (("old", ED_OLD), ("new", ED_NEW)):
        (keys / (name + "-ed.pub")).write_bytes(bytes.fromhex(public))
        (keys / (name + "-ed.sec")).write_bytes(bytes.fromhex(seed + public))
        subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(keys / (name + "-ml.pem"))], check=True)
        subprocess.run([OPENSSL, "pkey", "-in", str(keys / (name + "-ml.pem")), "-pubout", "-out",
                        str(keys / (name + "-ml.pub.pem"))], check=True)
        der = subprocess.run([OPENSSL, "pkey", "-pubin", "-in", str(keys / (name + "-ml.pub.pem")),
                              "-outform", "DER"], check=True, stdout=subprocess.PIPE).stdout
        kset[name] = {"edp": keys / (name + "-ed.pub"), "eds": keys / (name + "-ed.sec"),
                      "mlp": keys / (name + "-ml.pub.pem"), "mls": keys / (name + "-ml.pem"),
                      "ed_raw": bytes.fromhex(public), "ml_raw": der[-1952:]}
    control = store / "control.sock"
    rc, _ = sh("hybrid-enroll P (production image)", [NEW, "hybrid-enroll", control, "1", keys / "p.bin",
                                                      kset["old"]["edp"], kset["old"]["mlp"]])
    signer = NEW
    if rc != 0:
        sh("hybrid-enroll P (developer image as the client)", [DEV, "--fn", "hybrid-enroll", control, "1",
                                                               keys / "p.bin", kset["old"]["edp"],
                                                               kset["old"]["mlp"]], expect=0)

    def carrier(k, source, stem):
        src = keys / (stem + ".src")
        src.write_bytes(source)
        out = keys / (stem + ".carrier")
        rc, _ = sh("hybrid-sign-carrier %s" % stem, [NEW, "hybrid-sign-carrier", keys / "p.bin", k["edp"], k["eds"],
                                                     k["mlp"], k["mls"], src, out], quiet=False)
        if rc != 0:
            sh("hybrid-sign-carrier %s (developer image as the client)" % stem,
               [DEV, "--fn", "hybrid-sign-carrier", keys / "p.bin", k["edp"], k["eds"], k["mlp"], k["mls"], src, out],
               expect=0, quiet=True)
        return out.read_bytes()

    def header(msgid, group, subject, extra=b""):
        return ("From: Qual <qual@example.invalid>\r\nDate: Fri, 25 Sep 2026 21:00:00 +0000\r\n"
                "Newsgroups: {}\r\nSubject: {}\r\nMessage-ID: {}\r\n".format(group, subject, msgid)).encode() + extra + b"\r\n"

    c = Nntp(port, cert)
    say("  greeting %s / STARTTLS %s / AUTHINFO %s" % (c.greeting, c.starttls, c.auth))
    c.cmd("GROUP fn.agents")
    # tin-shaped article with a supplied Path
    tin_id = "<qual-e747-tin@example.invalid>"
    tin = (b"Path: not-for-mail\r\nFrom: Qual <qual@example.invalid>\r\nNewsgroups: fn.agents\r\n"
           b"Subject: qual rehearsal tin-shaped\r\nMessage-ID: " + tin_id.encode() +
           b"\r\nDate: Fri, 25 Sep 2026 21:00:00 +0000\r\nUser-Agent: TIN/2.6.2-20221225 (UNIX) (Linux/6)\r\n"
           b"\r\nsupplied Path, as tin sends it\r\n")
    c.post(tin)
    rep, art = c.article(tin_id)
    say("  tin article Path: %s" % [l for l in art if l.lower().startswith("path:")])
    say("  tin resend: %s" % c.post(tin))
    # signed article (served POST of a carrier)
    signed_id = "<qual-e747-signed@example.invalid>"
    c.post(carrier(kset["old"], header(signed_id, "fn.agents", "qual rehearsal signed") + b"signed body\r\n", "signed"))
    rep, art = c.article(signed_id)
    c.cmdm("HDR :fn-verified " + signed_id)
    # XPAT
    c.cmd("GROUP fn.agents")
    c.cmdm("XPAT Subject 1- *qual rehearsal*")
    c.cmdm("XPAT Message-ID " + signed_id + " *")
    # cancel by the author (signed by the same principal)
    cancel_id = "<qual-e747-cancel@example.invalid>"
    c.post(carrier(kset["old"], header(cancel_id, "fn.agents", "cmsg cancel " + signed_id,
                                       b"Control: cancel " + signed_id.encode() + b"\r\n") + b"cancel\r\n", "cancel"))
    c.close()
    time.sleep(1)
    c = Nntp(port, cert)
    say("  fresh reader after the cancel:")
    c.article(signed_id)
    c.cmdm("LISTGROUP control.cancel")
    c.close()
    # key statement: succession under a grant
    sh("control grant P keys fn.keys", [NEW, "operator", cfg, "control", "grant", P.hex(), "keys", "fn.keys"])
    succ_id = "<qual-e747-succession@example.invalid>"
    pop_src = keys / "pop.src"
    pop_src.write_bytes(POP_TAG + b"\n" + succ_id.encode() + b"\n" + kset["old"]["ed_raw"])
    rc, out = sh("hybrid-sign PoP", [NEW, "hybrid-sign", keys / "p.bin", kset["new"]["edp"], kset["new"]["eds"],
                                     kset["new"]["mlp"], kset["new"]["mls"], pop_src], quiet=True)
    if rc != 0:
        rc, out = sh("hybrid-sign PoP (developer)", [DEV, "--fn", "hybrid-sign", keys / "p.bin", kset["new"]["edp"],
                                                    kset["new"]["eds"], kset["new"]["mlp"], kset["new"]["mls"], pop_src],
                     quiet=True)
    sigs = dict(l.split() for l in out.splitlines() if len(l.split()) == 2)
    statement = (header(succ_id, "fn.keys", "fn-key-statement") + (b"FN-Key-Statement: succession-v1\r\n"
                        + hex_lines("FN-Key-Principal", P) + hex_lines("FN-Key-Old-Ed25519", kset["old"]["ed_raw"])
                        + hex_lines("FN-Key-New-Ed25519", kset["new"]["ed_raw"])
                        + hex_lines("FN-Key-New-ML-DSA-65", kset["new"]["ml_raw"])
                        + hex_lines("FN-Key-PoP-Ed25519", bytes.fromhex(sigs.get("ed25519", "00")))
                        + hex_lines("FN-Key-PoP-ML-DSA-65", bytes.fromhex(sigs.get("ml-dsa-65", "00")))))
    c = Nntp(port, cert)
    c.post(carrier(kset["old"], statement, "succession"))
    c.post(carrier(kset["old"], header("<qual-e747-oldkey@example.invalid>", "fn.agents", "old key") + b"x\r\n", "oldkey"))
    c.post(carrier(kset["new"], header("<qual-e747-newkey@example.invalid>", "fn.agents", "new key") + b"x\r\n", "newkey"))
    c.close()
    stop(owner, "e747-required")
    log = (work / "log" / "fn.log")
    if log.exists():
        say("  service log key-statement / cancel / refused lines:")
        for line in log.read_text("utf-8", "replace").splitlines():
            if any(w in line for w in ("key-statement", "cancel", "refused", "withdraw")):
                say("  | " + line[:300])
    sh("hybrid-key-history (owner stopped)", [NEW, "hybrid-key-history", store])
    sh("status offline (required, after the served cases)", [NEW, "operator", cfg, "status"], expect=0)
    # restart: everything still served
    owner = start([NEW], cfg, "e747-required-restart")
    c = Nntp(port, cert)
    c.cmd("GROUP fn.agents")
    for m in (tin_id, signed_id, cancel_id, "<qual-e747-newkey@example.invalid>"):
        c.article(m)
    c.close()
    stop(owner, "e747-required-restart")
    sh("recover after restart", [NEW, "operator", cfg, "recover"], expect=0)
    # the live originals: unchanged by this run (compared with the copy's digest)
    now_rows = tree_digest(LIVE / "store") if os.access(LIVE / "store", os.R_OK) else []
    say("STEP live store digest unchanged since the copy: %s" % (now_rows == live_rows))
    say("# rehearsal end %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))


try:
    main()
finally:
    for p in started:
        if p.poll() is None:
            p.terminate()
            try:
                p.wait(60)
            except subprocess.TimeoutExpired:
                p.kill()

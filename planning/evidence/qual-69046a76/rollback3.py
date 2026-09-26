#!/usr/bin/env python3
"""qual-69046a76 fact 1c, the three NEW rollback consequences, on COPIES only
(after upgrade_live.py made S/pristine, the 69046a76 install and the bbf52159 copy).
 (i)   an account code issued/redeemed (delta 15/16) and a login binding applied
       live (delta 17) on a copy of the live store: bbf52159 then refuses the
       store; the pre-upgrade snapshot restores (PKT-440, PKT-391's class);
 (ii)  a pull journal holding :pull-unavailable (a scripted peer listing an id it
       answers 430): a pre-today image refuses; deleting pull/ restores, the
       cursor restarting one day back (PKT-432);
 (iii) the pre-C1 witness store: every open refused BY NAME at exit 1, and
       store repair-control refuses "repair semantics undecided (PKT-444)".
/tank/fn/node is read by nothing here except upgrade_live's pristine copy."""
import os, re, shutil, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, "/tank/fn/scratch/qual-69046a76")
import upgrade_live as U

S = U.S / "rollback3"
NEW = U.S / "fn-69046a76" / "bin" / "fn"
OLD = U.S / "fn-bbf52159" / "bin" / "fn"
NEWIMG = U.I / "fn-host"
OLDIMG = Path("/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host")
B67IMG = Path("/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host")
pristine = U.S / "pristine"
say, sh = U.say, U.sh


def port_of(cfg):
    return int(re.search(r"port = (\d+)", cfg.read_text()).group(1))


def fresh(name):
    w = S / name
    U.copytree(pristine, w)
    return w, U.config_for(w, U.free_port())


def part_accounts():
    say("## (i-a) an account code on a copy of the live store")
    w, cfg = fresh("acct")
    snap = S / "acct-snapshot"
    U.copytree(w, snap)
    say("STEP snapshot-pre-upgrade (cp -a of the stopped copy)")
    # issued only (offline), on a side copy: does issuing alone (delta 15) bar bbf52159?
    wi, cfgi = fresh("acct-issued-only")
    rc, out = sh("69046a76 account invite OFFLINE on a side copy", [NEW, "operator", cfgi, "account", "invite", "--expires", "3600"], quiet=True)
    say("  invite rc=%d printed-a-code=%s" % (rc, bool(re.search(r"^[0-9a-f]{32}$", out, re.M))))
    sh("bbf52159 status on the issued-only copy", [OLD, "operator", cfgi, "status"])
    o = U.start([NEW], cfg, "dfa8-acct")
    rc, out = sh("69046a76 account invite (live)", [NEW, "operator", cfg, "account", "invite", "--expires", "3600"], quiet=True)
    code = re.search(r"^([0-9a-f]{32})$", out, re.M).group(1)
    say("  a code was printed once (not logged here)")
    port, cert = port_of(cfg), w / "tls" / "cert.pem"
    U.plain(port, ["XREDEEM %s friend1" % code, "QUIT"])
    c = U.Nntp(port, cert, login=False)
    r1 = c.cmd("XREDEEM %s friend1" % code, show=False)
    r2 = c.cmd("XREDEEM PASS qual-69046a76-friend", show=False)
    say("  XREDEEM over STARTTLS -> %s / PASS -> %s" % (r1[:40], r2[:40]))
    c.close()
    c = U.Nntp(port, cert, login=False)
    say("  AUTHINFO USER friend1 -> %s" % c.cmd("AUTHINFO USER friend1", show=False)[:40])
    say("  AUTHINFO PASS -> %s" % c.cmd("AUTHINFO PASS qual-69046a76-friend", show=False)[:40])
    c.cmd("GROUP fn.agents")
    say("  POST as friend1 -> %s" % c.post(b"From: friend1 <friend1@example.invalid>\r\nNewsgroups: fn.agents\r\n"
                                          b"Subject: qual dfa8 redeemed friend\r\nMessage-ID: <qual-dfa8-friend1@example.invalid>\r\n\r\nhello\r\n"))
    c.close()
    c = U.Nntp(port, cert, login=False)
    say("  same code, another login -> %s" % c.cmd("XREDEEM %s friend2" % code, show=False)[:40])
    c.close()
    U.stop(o, "dfa8-acct")
    rc, out = sh("69046a76 account list", [NEW, "operator", cfg, "account", "list"])
    say("  the code is absent from account list: %s" % (code not in out))
    sh("69046a76 status after the redeem", [NEW, "operator", cfg, "status"], expect=0)
    rc, out = sh("ROLLBACK: bbf52159 status on the redeemed store (want 4)", [OLD, "operator", cfg, "status"], expect=4)
    sh("ROLLBACK: bbf52159 recover on the redeemed store (want 4)", [OLD, "operator", cfg, "recover"], expect=4)
    o = U.start([OLD], cfg, "bbf5-on-redeemed")
    U.stop(o, "bbf5-on-redeemed")
    r, cfgr = S / "acct-restored", None
    U.copytree(snap, r)
    cfgr = U.config_for(r, U.free_port())
    sh("RESTORE: bbf52159 recover on the pre-upgrade snapshot", [OLD, "operator", cfgr, "recover"], expect=0)
    sh("RESTORE: bbf52159 status on the pre-upgrade snapshot", [OLD, "operator", cfgr, "status"], expect=0)
    o = U.start([OLD], cfgr, "bbf5-restored-acct")
    c = U.Nntp(port_of(cfgr), r / "tls" / "cert.pem", login=False)
    c.cmd("GROUP fn.agents")
    c.close()
    U.stop(o, "bbf5-restored-acct")


def part_binding():
    say("## (i-b) a login binding applied live on a copy of the live store")
    w, cfg = fresh("bind")
    sh("principal set-password qual (no signing binding)", [NEW, "operator", cfg, "principal", "set-password", U.LOGIN,
                                                            "--principal", U.P.hex(), "--posting"],
       stdin=(U.SECRET + "\n" + U.SECRET + "\n").encode())
    o = U.start([NEW], cfg, "dfa8-bind")
    c = U.Nntp(port_of(cfg), w / "tls" / "cert.pem")
    say("  session open before the bind: AUTHINFO -> %s" % c.auth)
    snap = S / "bind-snapshot-note"
    rc, out = sh("69046a76 principal bind qual P (live)", [NEW, "operator", cfg, "principal", "bind", U.LOGIN, U.P.hex()])
    say("  bind's last word: %s" % (out.split()[-1] if out.split() else ""))
    c.cmd("GROUP fn.agents")
    c.close()
    U.stop(o, "dfa8-bind")
    sh("principal list", [NEW, "operator", cfg, "principal", "list"])
    sh("ROLLBACK: bbf52159 status on the store with a published binding (want 4)", [OLD, "operator", cfg, "status"], expect=4)
    sh("ROLLBACK: bbf52159 recover (want 4)", [OLD, "operator", cfg, "recover"], expect=4)
    # the control: the same copy with an owner run and NO bind is opened by bbf52159
    wc, cfgc = fresh("bind-control")
    sh("principal set-password qual (control copy)", [NEW, "operator", cfgc, "principal", "set-password", U.LOGIN,
                                                     "--principal", U.P.hex(), "--posting"],
       stdin=(U.SECRET + "\n" + U.SECRET + "\n").encode())
    o = U.start([NEW], cfgc, "dfa8-bind-control")
    U.stop(o, "dfa8-bind-control")
    sh("CONTROL: bbf52159 status after a 69046a76 owner ran with no binding (want 0)", [OLD, "operator", cfgc, "status"], expect=0)
    r = S / "bind-restored"
    U.copytree(pristine, r)
    cfgr = U.config_for(r, U.free_port())
    sh("RESTORE: bbf52159 status on the pre-upgrade snapshot (the pristine copy)", [OLD, "operator", cfgr, "status"], expect=0)


def part_pull():
    say("## (ii) the pull journal's :pull-unavailable record")
    sys.path.insert(0, str(U.T))
    os.environ["FN_NATIVE_HOST"] = str(NEWIMG)
    from tests import test_native_peer_pull as PP
    ghost = "<ghost-qual@example.invalid>"
    real = ["<real-qual-%d@example.invalid>" % k for k in range(2)]
    peer = PP.ScriptedPeer([real[0], ghost, real[1]],
                           {m: PP.article(m, "real-" + m[6:12], path="scripted!not-for-mail") for m in real})
    root = S / "pull"
    if root.exists():
        shutil.rmtree(root)
    root.mkdir(parents=True)
    store, log = root / "store", root / "fn.log"
    port = U.free_port()
    cfg = root / "fn.toml"
    cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n[log]\npath = "%s"\n'
                   % (store, port, root / "control.sock", log))
    sh("bbf52159 image: store init fn.test (the node as deployed)", [OLDIMG, "--fn", "store", store, "init", "fn.test"], expect=0)
    sh("bbf52159 image: policy set path-identity", [OLDIMG, "--fn", "operator", cfg, "policy", "set", "path-identity", "b.pull.example.invalid"], expect=0)
    sh("bbf52159 image: peer add S", [OLDIMG, "--fn", "operator", cfg, "peer", "add", "S", "s.pull.example.invalid", "127.0.0.1",
                                      str(peer.port), "fn.*", "-", "127.0.0.9", "true"], expect=0)
    sh("bbf52159 image: peer pull S 2 (its grammar: no ROUNDS)", [OLDIMG, "--fn", "operator", cfg, "peer", "pull", "S", "2"], expect=0)
    sh("bbf52159 status before the upgrade", [OLDIMG, "--fn", "operator", cfg, "status"], expect=0)
    o = U.start([NEWIMG, "--fn"], cfg, "dfa8-pull")
    deadline = time.time() + 180
    while time.time() < deadline:
        t = log.read_text(errors="replace") if log.exists() else ""
        if "cursor=held unavailable=1" in t:
            break
        time.sleep(1)
    time.sleep(3)
    U.stop(o, "dfa8-pull")
    lines = [l for l in log.read_text(errors="replace").splitlines() if l.startswith("pull peer=")]
    for l in lines[:6]:
        say("  log| " + l[:220])
    say("  pull journal files: %s" % sorted(str(p.relative_to(store)) for p in (store / "pull").rglob("*") if p.is_file()))
    raw = b"".join(p.read_bytes() for p in (store / "pull").rglob("*") if p.is_file())
    say("  journal octets %d; contains 'pull-unavailable': %s" % (len(raw), b"pull-unavailable" in raw.lower() or b"PULL-UNAVAILABLE" in raw))
    keep = S / "pull-with-unavailable"
    U.copytree(root, keep)
    for label, img in (("bbf52159", OLDIMG), ("b6759850", B67IMG)):
        sh("ROLLBACK: %s status with the :pull-unavailable journal" % label, [img, "--fn", "operator", cfg, "status"])
        sh("ROLLBACK: %s recover with the journal" % label, [img, "--fn", "operator", cfg, "recover"])
        p = subprocess.Popen([str(img), "--fn", "operator", str(cfg), "run"], cwd=U.T, env=U.ENV,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            out, err = p.communicate(timeout=60)
            say("STEP ROLLBACK: %s owner with the journal exited rc=%d" % (label, p.returncode))
            for l in (out + err).decode("utf-8", "replace").strip().splitlines()[-8:]:
                say("  | " + l[:220])
        except subprocess.TimeoutExpired:
            p.terminate(); p.communicate(timeout=60)
            say("STEP ROLLBACK: %s owner with the journal STAYED UP 60 s (terminated) rc=%s" % (label, p.returncode))
        t = log.read_text(errors="replace").splitlines()
        for l in t[-4:]:
            say("  fn.log| " + l[:220])
    before = len(peer.newnews())
    shutil.rmtree(store / "pull")
    say("STEP delete pull/ (the documented rollback step)")
    o = U.start([OLDIMG, "--fn"], cfg, "bbf5-pull-deleted")
    deadline = time.time() + 60
    while time.time() < deadline and len(peer.newnews()) <= before:
        time.sleep(0.5)
    time.sleep(2)
    U.stop(o, "bbf5-pull-deleted")
    nn = peer.newnews()
    say("  NEWNEWS asked by the upgraded image: %s" % nn[:2])
    say("  NEWNEWS asked by bbf52159 after pull/ was deleted: %s" % nn[before:before + 2])
    say("  wall clock now (UTC): %s" % time.strftime("%Y%m%d %H%M%S", time.gmtime()))
    sh("bbf52159 status after the rollback", [OLDIMG, "--fn", "operator", cfg, "status"], expect=0)
    peer.close()


def part_prec1():
    say("## (iii) the pre-C1 witness store")
    fx = U.T / "tests" / "fixtures" / "pre-c1-control-store"
    say("  fixture files: %s" % sorted(str(p.relative_to(fx)) for p in fx.rglob("*") if p.is_file())[:12])
    for name in ("witness", "ordinary"):
        w = S / ("prec1-" + name)
        if w.exists():
            shutil.rmtree(w)
        shutil.copytree(fx / name, w)
        (w / "staging").mkdir()
        (w / "writer.lock").touch()
        for q in [w, *w.rglob("*")]:
            q.chmod(0o700 if q.is_dir() else 0o600)
        for verb in (["recover"], ["inspect", "<prec1-target@example.invalid>"], ["checkpoint"]):
            sh("69046a76 store %s %s" % (name, " ".join(verb)), [NEWIMG, "--fn", "store", w, *verb],
               expect=(1 if name == "witness" else None))
        if name == "witness":
            sh("69046a76 store witness repair-control (want refusal)", [NEWIMG, "--fn", "store", w, "repair-control"])
            cfg = S / "prec1.toml"
            cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n' % (w, U.free_port()))
            sh("69046a76 operator health (offline) on the witness", [NEWIMG, "--fn", "operator", cfg, "health"])
            sh("69046a76 operator run on the witness (want refusal, exit 1)", [NEWIMG, "--fn", "operator", cfg, "run"], expect=1)
            sh("bbf52159 (deployed) store witness recover", [OLDIMG, "--fn", "store", w, "recover"])
    doc = (U.T / "docs" / "operator.md").read_text()
    i = doc.find("A store written by a release before 2026-09-25 (C1)")
    say("QUOTE-DOC-iii " + " ".join(doc[i:i + 620].split()))


def main():
    if S.exists():
        shutil.rmtree(S)
    S.mkdir(parents=True)
    say("ENV FN_NATIVE_HOST in the children's environment: %r" % U.ENV.get("FN_NATIVE_HOST"))
    rc, out = sh("OLD bin/fn --version", [OLD, "--version"])
    rc, out = sh("NEW bin/fn --version", [NEW, "--version"])
    say("# rollback3 start %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    doc = (U.T / "docs" / "operator.md").read_text()
    for needle in ("Once an account code is redeemed", "The same rule covers the login-binding rows", "**The pull journals**"):
        i = doc.find(needle)
        say("QUOTE-DOC " + " ".join(doc[i:i + 480].split()))
    for part in (part_accounts, part_binding, part_pull, part_prec1):
        try:
            part()
        except Exception as e:
            say("PART-ERROR %s %r" % (part.__name__, e))
    say("# rollback3 end %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))


if __name__ == "__main__":
    try:
        main()
    finally:
        for p in U.started:
            if p.poll() is None:
                p.kill()
                p.wait()

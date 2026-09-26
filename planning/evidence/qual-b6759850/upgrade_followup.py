#!/usr/bin/env python3
"""qual-b6759850 rehearsal follow-up (after upgrade_live.py): the rollback to
bbf52159 WITHOUT a snapshot, which the rehearsal showed is possible on this
image (b6759850 writes the frontier in the format-2 bytes for every txid below
2^32, fn-bs-frontier-encode-impl), exercised end to end on copies:
  (a) bbf52159's owner on the store b6759850 wrote: serve what b6759850
      accepted, accept a new article; then b6759850 reopens and serves it;
  (b) the same on the marker-required copy;
  (c) rollback-check --snapshot against a store that is not an earlier state
      of this one (a fresh init), which must refuse snapshot-not-a-prefix.
Copies only; /tank/fn/node is read by nothing here."""
import re, subprocess, time
from pathlib import Path
import upgrade_live as U

S = U.S
NEW = S / "fn-b6759850" / "bin" / "fn"
OLD = S / "fn-bbf52159" / "bin" / "fn"


def port_of(cfg):
    return int(re.search(r"port = (\d+)", cfg.read_text()).group(1))


def serve_and_post(image, name, work, cfg, tag, read_ids):
    o = U.start([image], cfg, name)
    c = U.Nntp(port_of(cfg), work / "tls" / "cert.pem")
    U.say("  AUTHINFO -> %s" % c.auth)
    c.cmd("GROUP fn.agents")
    for mid in read_ids:
        c.cmd("STAT " + mid)
    msgid = "<qual-b675-%s@example.invalid>" % tag
    art = ("From: Qual <qual@example.invalid>\r\nDate: Sat, 26 Sep 2026 06:40:00 +0000\r\nNewsgroups: fn.agents\r\n"
           "Subject: qual rollback %s\r\nMessage-ID: %s\r\n\r\nwritten by %s\r\n" % (tag, msgid, name)).encode()
    c.post(art)
    c.close()
    U.stop(o, name)
    return msgid


def main():
    U.say("# follow-up start %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    seen = ["<qual-b675-tin@example.invalid>", "<qual-b675-signed@example.invalid>",
            "<qual-b675-cancel@example.invalid>", "<qual-b675-wrong-principal@example.invalid>"]
    # (a) plain deployed store (unmarked), written by b6759850
    a = S / "rollback-binary"
    U.copytree(S / "w", a)
    cfg_a = U.config_for(a, U.free_port())
    U.sh("bbf52159 recover on the store b6759850 wrote", [OLD, "operator", cfg_a, "recover"], expect=0)
    old_id = serve_and_post(OLD, "bbf5-on-b675-store", a, cfg_a, "by-bbf5", seen)
    U.sh("bbf52159 status after its own commit", [OLD, "operator", cfg_a, "status"], expect=0)
    U.sh("b6759850 recover after bbf52159 wrote (roll forward again)", [NEW, "operator", cfg_a, "recover"], expect=0)
    serve_and_post(NEW, "b675-after-bbf5", a, cfg_a, "by-b675-again", seen + [old_id])
    U.sh("b6759850 status (roll forward)", [NEW, "operator", cfg_a, "status"], expect=0)
    U.sh("bbf52159 recover once more", [OLD, "operator", cfg_a, "recover"], expect=0)
    # (b) the marker-required copy
    b = S / "rollback-binary-required"
    U.copytree(S / "marker", b)
    cfg_b = U.config_for(b, U.free_port())
    U.sh("bbf52159 recover on the required store b6759850 wrote", [OLD, "operator", cfg_b, "recover"], expect=0)
    old_b = serve_and_post(OLD, "bbf5-on-required", b, cfg_b, "by-bbf5-required", ["<qual-b675-required@example.invalid>"])
    U.sh("b6759850 recover after bbf52159 wrote the required store", [NEW, "operator", cfg_b, "recover"], expect=0)
    U.sh("b6759850 status (required, after bbf52159)", [NEW, "operator", cfg_b, "status"], expect=0)
    # (c) snapshot-not-a-prefix
    f = S / "unrelated"
    f.mkdir(exist_ok=True)
    fcfg = f / "fn.toml"
    fcfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n' % (f / "store", U.free_port()))
    U.sh("init an unrelated store", [NEW, "operator", fcfg, "init", "fn.agents"], expect=0)
    U.sh("rollback-check --snapshot UNRELATED (expected refused snapshot-not-a-prefix)",
         [NEW, "operator", U.config_for(S / "w", U.free_port()), "store", "rollback-check", "--snapshot", f / "store"])
    U.say("# follow-up end %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))


if __name__ == "__main__":
    try:
        main()
    finally:
        for p in U.started:
            if p.poll() is None:
                p.kill(); p.wait()

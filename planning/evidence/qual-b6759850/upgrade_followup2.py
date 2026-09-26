#!/usr/bin/env python3
"""qual-b6759850 rehearsal follow-up 2: rollback-check --snapshot against a
snapshot that is NOT an earlier state of the store (a fork: the pre-deploy
snapshot plus one different article), and an unrelated store with one article.
(An empty store is a prefix of every store, so follow-up 1's fresh init was
correctly counted, not refused.)  Copies only."""
import re, time
import upgrade_live as U
S = U.S
NEW = S / "fn-b6759850" / "bin" / "fn"


def commit_one(work, tag, login=True):
    cfg = U.config_for(work, U.free_port())
    o = U.start([NEW], cfg, "b675-" + tag)
    c = U.Nntp(int(re.search(r"port = (\d+)", cfg.read_text()).group(1)), work / "tls" / "cert.pem", login=login)
    c.post(("From: Qual <qual@example.invalid>\r\nDate: Sat, 26 Sep 2026 06:50:00 +0000\r\nNewsgroups: fn.agents\r\n"
            "Subject: fork %s\r\nMessage-ID: <qual-b675-fork-%s@example.invalid>\r\n\r\nfork\r\n" % (tag, tag)).encode())
    c.close()
    U.stop(o, "b675-" + tag)


def main():
    U.say("# follow-up 2 start %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    fork = S / "fork"
    U.copytree(S / "snapshot-pre-deploy", fork)
    # the fork's login: the pre-deploy snapshot has no qual password; set one on the copy
    cfg_f = U.config_for(fork, U.free_port())
    U.sh("fork: principal set-password", [NEW, "operator", cfg_f, "principal", "set-password", U.LOGIN, "--posting"],
         stdin=(U.SECRET + "\n" + U.SECRET + "\n").encode())
    commit_one(fork, "a")
    U.sh("fork status", [NEW, "operator", cfg_f, "status"], expect=0)
    cfg_w = U.config_for(S / "w", U.free_port())
    U.sh("rollback-check --snapshot FORK (13 shared + 1 different; expected refused snapshot-not-a-prefix)",
         [NEW, "operator", cfg_w, "store", "rollback-check", "--snapshot", fork / "store"])
    U.say("# follow-up 2 end %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))


if __name__ == "__main__":
    try:
        main()
    finally:
        for p in U.started:
            if p.poll() is None:
                p.kill(); p.wait()

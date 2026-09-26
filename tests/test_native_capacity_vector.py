"""The full-store lifecycle on the native image (SCN-081, STO-020, PRF-138).

A client and harness only: every decision is the image's (ACL2's).  One
store, in order:

  1. an accepted promise: a BP forwarding obligation is undertaken (the
     Store's :undertake record; `status' shows debt=1);
  2. fill: NNTP POST until ordinary admission refuses by name (441);
  3. complete the outstanding work: the BP exchange delivers the article and
     its receipt, and `bp-obligation receipt' writes the release record into
     the full store (debt=0, pinned=no);
  4. release eligible content: `retention set released-by-all-holders' (a
     configuration record, the generation the vector keeps for it);
  5. maintain across crashes: `store compact' and `store reclaim', each at
     every publication, selection and retirement cut (SIGSTOP then SIGKILL)
     on a copy, and reclaim's kill and EIO faults; each copy reopens
     (`status' exit 0) and its rerun converges to the clean run's pack;
  6. recover and use the reclaimed capacity: the clean run, `status', and
     the next POST is 240.

It prints one JSON line per observation (and appends it to $FN_CV_LOG).
"""

import hashlib
import json
import os
import shutil
import signal
import subprocess
import time
import unittest
from pathlib import Path

import tests.test_bp_app_native as base
from tests.native_process import wait_for_announcement
from tools import msgid_measure as m

HIST = int(os.environ.get("FN_CV_HIST", "300000"))
FLAGS = ["--max-history-octets", str(HIST), "--max-record-octets", "262144",
         "--max-article-octets", "131072", "--max-groups-per-article", "16"]
LOG = os.environ.get("FN_CV_LOG")
GROUP = "fn.test"
STOP_CUTS = ["candidate-file", "candidate-link", "candidate-directory",
             "selection-file", "selection-replace", "selection-directory",
             "pack-retire-unlink", "pack-retire-directory"]
RECLAIM_FAULTS = [(a, c) for c in ("reclaim-state-checkpoint-unlink",
                                   "reclaim-state-checkpoint-directory",
                                   "reclaim-pack-published",
                                   "reclaim-pack-selected", "reclaim-retired")
                  for a in ("kill", "eio")]


class _Bp(base.NativeBpApplicationTests):
    pass


# Reuse the BP fixture (receiver Store, boundary, request ADU), not its tests.
for _name in dir(base.NativeBpApplicationTests):
    if _name.startswith("test_"):
        setattr(_Bp, _name, None)


def msgid(i):
    return "<cv-%06d@capacity.example.invalid>" % i


def article(i, body=1024):
    head = ("From: cv@example.invalid\r\nNewsgroups: %s\r\nSubject: capacity %d\r\n"
            "Date: Sat, 26 Sep 2026 12:00:00 +0000\r\nMessage-ID: %s\r\n\r\n"
            % (GROUP, i, msgid(i))).encode()
    return head + (b"z" * 62 + b"\r\n") * max(1, body // 64)


def footprint(store):
    files = octets = 0
    for d, _, fs in os.walk(store):
        for f in fs:
            files += 1
            octets += os.lstat(os.path.join(d, f)).st_size
    du = subprocess.run(["du", "-sB1", str(store)], stdout=subprocess.PIPE,
                        check=False).stdout.split()
    return {"inodes": files, "octets": octets, "du": int(du[0]) if du else -1}


def selected_pack(store):
    packs = Path(store) / "packs"
    if not packs.exists():
        return []
    files = [p for p in packs.iterdir() if p.is_file()]
    sizes = sorted((p.stat().st_size, p) for p in files)
    marker = sizes[0][1] if len(sizes) > 1 else None
    return sorted(hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in files if p != marker)


class NativeCapacityVectorTests(_Bp):

    def out(self, **rec):
        line = json.dumps(rec)
        print(line, flush=True)
        if LOG:
            with open(LOG, "a", encoding="utf-8") as f:
                f.write(line + "\n")

    def config(self, store, name):
        port = m.free_port()
        cfg = self.temp / (name + ".toml")
        cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\n'
                       'port = %d\n[control]\npath = "%s"\n'
                       % (store, port, self.temp / (name + ".sock")))
        return cfg, port

    def status(self, cfg):
        r = self.invoke("operator", cfg, "status")
        lines = r.stdout.decode(errors="replace").splitlines()

        def pick(word):
            return next((l for l in lines if l.startswith(word)), "")
        return {"exit": r.returncode, "headroom": pick("headroom"),
                "reserve": pick("maintenance-reserve"), "reclaim": pick("reclaim")}

    def owner(self, cfg):
        p = subprocess.Popen([str(base.IMAGE), "--fn", "operator", str(cfg), "run"],
                             env=self.env, stdout=subprocess.PIPE,
                             stderr=subprocess.DEVNULL)
        wait_for_announcement(p, b"LISTENING ", timeout=600)
        return p

    def stop_owner(self, p):
        p.send_signal(signal.SIGTERM)
        p.wait(timeout=600)
        p.stdout.close()

    def post(self, c, i):
        r = c.line("POST")
        if not r.startswith(b"340"):
            return r.decode(errors="replace").strip()
        c.stream.write(article(i) + b".\r\n")
        return c.readline().decode(errors="replace").strip()

    def verb(self, cfg, *words, env=None):
        r = self.invoke("operator", cfg, *words, env=env, timeout=3600)
        return (r.returncode, r.stdout.decode(errors="replace").strip()[-300:],
                r.stderr.decode(errors="replace").strip()[-300:])

    def cut_copy(self, store, name):
        copy = self.temp / name
        shutil.rmtree(copy, ignore_errors=True)
        shutil.copytree(store, copy)
        return copy, self.config(copy, name)[0]

    def stop_cut(self, cfg, verb, point):
        env = dict(self.env)
        env["FN_CHECKPOINT_TEST_STOP"] = point
        p = subprocess.Popen([str(base.IMAGE), "--fn", "operator", str(cfg),
                              "store", verb], env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE)
        stopped = False
        for _ in range(36000):
            state = open("/proc/%d/stat" % p.pid).read().split(")")[-1].split()[0]
            if state == "T":
                stopped = True
                break
            if p.poll() is not None:
                break
            time.sleep(0.05)
        p.kill()
        p.wait()
        p.stdout.close()
        p.stderr.close()
        return "stopped" if stopped else "exit-%s" % p.returncode

    def cuts(self, store, verb):
        """Every cut of VERB on a copy of STORE; returns the failures."""
        ref, rcfg = self.cut_copy(store, "cut-ref")
        code, _, err = self.verb(rcfg, "store", verb)
        self.assertEqual(code, 0, err)
        reference = selected_pack(ref)
        shutil.rmtree(ref, ignore_errors=True)
        plan = [("stop", p) for p in STOP_CUTS]
        if verb == "reclaim":
            plan += RECLAIM_FAULTS
        bad = []
        for action, point in plan:
            copy, ccfg = self.cut_copy(store, "cut-%s-%s-%s" % (verb, action, point))
            if action == "stop":
                first = self.stop_cut(ccfg, verb, point)
            else:
                env = dict(self.env)
                env["FN_NATIVE_RECLAIM_FAULT"] = "%s:%s" % (point, action)
                first = "exit-%d" % self.verb(ccfg, "store", verb, env=env)[0]
            reopened = self.status(ccfg)
            rerun = self.verb(ccfg, "store", verb)
            converged = selected_pack(copy) == reference
            self.out(tag="cut", verb=verb, action=action, point=point, first=first,
                     reopen_status=reopened["exit"], rerun_exit=rerun[0],
                     rerun_head=rerun[1][:120], converged=converged)
            if reopened["exit"] != 0 or rerun[0] != 0 or not converged:
                bad.append((verb, action, point))
            shutil.rmtree(copy, ignore_errors=True)
        return bad

    def test_full_store_finishes_releases_maintains_and_reuses(self):
        sender = self.temp / "sender-store"
        workflow = self.temp / "sender-workflow"
        cfg, port = self.config(sender, "sender")
        # 1. The accepted promise.
        r = self.invoke("store", sender, "init", *FLAGS, GROUP)
        self.assertEqual(r.returncode, 0, r.stderr.decode())
        payload = self.temp / "sender-article"
        payload.write_bytes(self.article)
        r = self.invoke("store", sender, "post", self.msgid.decode("ascii"),
                        payload, "-", "-", GROUP)
        self.assertEqual(r.returncode, 0, r.stderr.decode())
        r = self.invoke("app-journal", "workflow-init", sender, workflow,
                        "dtn://sender/", "dtn://receiver/", "native-policy",
                        "dtn://receiver/", "3600000", "origin-native", "wire-auth")
        self.assertEqual(r.returncode, 0, r.stderr.decode())
        r = self.invoke("app-journal", "workflow-enqueue", sender, workflow,
                        "1", "0", "work-native-bp", self.msgid.decode("ascii"),
                        "forward-native-bp", "dtn://receiver/", "native-policy",
                        "terms-native")
        self.assertEqual(r.returncode, 0, r.stderr.decode())
        r = self.invoke("bp-obligation", "undertake", sender, workflow,
                        "work-native-bp", "3")
        self.assertEqual(r.returncode, 0, r.stderr.decode())
        promised = self.status(cfg)
        self.out(tag="undertaken", **promised)
        self.assertIn("debt=1 held", promised["reserve"])

        # 2. Fill until ordinary admission refuses by name.
        t0 = time.perf_counter()
        owner = self.owner(cfg)
        accepted, refused = 0, ""
        try:
            c = m.Conn(port)
            for i in range(5000):
                answer = self.post(c, i)
                if not answer.startswith("240"):
                    refused = answer
                    break
                accepted += 1
            c.close()
        finally:
            self.stop_owner(owner)
        full = self.status(cfg)
        self.out(tag="full", accepted=accepted, refused=refused,
                 wall_s=round(time.perf_counter() - t0, 1),
                 footprint=footprint(sender), **full)
        self.assertTrue(refused.startswith("441"), refused)
        self.assertIn("debt=1 held", full["reserve"])

        # 3. Complete the outstanding work in the full store.
        receiver, rport = self.start_receiver()
        bp_sender = self.start_sender(rport)
        try:
            s_out, s_err = bp_sender.communicate(timeout=600)
            r_out, r_err = receiver.communicate(timeout=600)
        finally:
            for p in (receiver, bp_sender):
                if p.poll() is None:
                    p.kill()
                    p.wait(timeout=10)
                p.stdout.close()
                p.stderr.close()
        self.out(tag="bp-exchange", sender=bp_sender.returncode,
                 receiver=receiver.returncode,
                 accepted=b"BP summary accepted=1" in s_out)
        self.assertEqual(bp_sender.returncode, 0, s_err.decode())
        receipts = sorted((self.sender_spool / "receive-evidence").glob("*.adu"))
        self.assertEqual(len(receipts), 1)
        r = self.invoke("bp-obligation", "receipt", sender, workflow, receipts[0],
                        "2", "0", "trusted-local-observation-v0")
        pinned = self.invoke("bp-obligation", "status", sender, workflow,
                             "work-native-bp")
        discharged = self.status(cfg)
        self.out(tag="receipt", exit=r.returncode,
                 stderr=r.stderr.decode(errors="replace")[-300:],
                 obligation=pinned.stdout.decode(errors="replace").strip(),
                 **discharged)
        self.assertEqual(r.returncode, 0, r.stderr.decode())
        self.assertIn(b"pinned=no", pinned.stdout)
        self.assertIn("debt=0", discharged["reserve"])

        # 4. Release eligible content.
        code, so, se = self.verb(cfg, "retention", "set", "released-by-all-holders")
        self.out(tag="retention-set", exit=code, stderr=se)
        self.assertEqual(code, 0, se)
        code, so, se = self.verb(cfg, "store", "reclaim", "--dry-run")
        self.out(tag="dry-run", exit=code, stdout=so[:200])

        # 5. Maintain across crashes, then 6. the clean run.
        bad = self.cuts(sender, "compact")
        before_compact = footprint(sender)
        code, so, se = self.verb(cfg, "store", "compact")
        self.out(tag="compact", exit=code, stdout=so[:200], stderr=se,
                 before=before_compact, after=footprint(sender))
        self.assertEqual(code, 0, se)
        bad += self.cuts(sender, "reclaim")
        before = footprint(sender)
        pre = self.status(cfg)
        code, so, se = self.verb(cfg, "store", "reclaim")
        after = footprint(sender)
        post = self.status(cfg)
        self.out(tag="reclaim", exit=code, stdout=so[:200], stderr=se,
                 before=before, after=after, status_before=pre, status_after=post)
        self.assertEqual(code, 0, se)
        self.assertEqual(post["exit"], 0)
        owner = self.owner(cfg)
        try:
            c = m.Conn(port)
            reused = [self.post(c, 900000 + k) for k in range(3)]
            c.close()
        finally:
            self.stop_owner(owner)
        final = self.status(cfg)
        self.out(tag="reuse", posts=reused, footprint=footprint(sender), **final)
        self.out(tag="cuts", failures=bad)
        self.assertEqual(bad, [])
        self.assertTrue(all(a.startswith("240") for a in reused), reused)


if __name__ == "__main__":
    unittest.main()

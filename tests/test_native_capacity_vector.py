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
  5. maintain across crashes: `store compact' and `store reclaim' (format 9:
     a state checkpoint with the record log rotated, then the covered
     segments dropped; lane log-recovery), each killed at every rotation and
     drop cut (FN_NATIVE_LOG_FAULT, SIGKILL) on a copy; each copy reopens
     (`status' exit 0) and its rerun converges to the clean run's history
     (the `store export' archive of the copy equals the clean run's, file for
     file);
  6. recover and use the reclaimed capacity: the clean run, `status', and
     the next POST is 240.

It prints one JSON line per observation (and appends it to $FN_CV_LOG).
"""

import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import time
import unittest
from pathlib import Path

import tests.test_bp_app_native as base
from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, Client, Node, environment, executable, native_image, run)

HIST = int(os.environ.get("FN_CV_HIST", "300000"))
# T well above what H admits, so the history bound is the one the fill meets
# (the transaction budget is a lifetime budget: no maintenance returns it).
FLAGS = ["--profile", "default", "--max-transactions", "4096",
         "--max-history-octets", str(HIST), "--max-record-octets", "262144",
         "--max-article-octets", "131072", "--max-groups-per-article", "16"]
LOG = os.environ.get("FN_CV_LOG")
GROUP = "fn.test"
# The rotation and drop cuts of compaction and reclamation over the log
# (host/native/io.lisp fnn-log-prepare-spare / fnn-log-rotate /
# fnn-log-make-durable / fnn-log-drop: FN_NATIVE_LOG_FAULT).
LOG_CUTS = ["rotate-created", "rotate-fenced", "rotate-renamed", "rotate-headed", "rotate-durable",
            "drop-unlinked", "drop-durable"]


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


def archive_tree(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(Path(root).rglob("*")) if p.is_file()}


class NativeCapacityVectorTests(_Bp):

    def out(self, **rec):
        line = json.dumps(rec)
        print(line, flush=True)
        if LOG:
            with open(LOG, "a", encoding="utf-8") as f:
                f.write(line + "\n")

    def config(self, store, name):
        """A node serving STORE (anywhere): its fn.toml and port."""
        node = Node(self, base.IMAGE, root=self.temp / (name + "-node"), name=name)
        node.store_path = store
        node.write_config()
        self.nodes = getattr(self, "nodes", {})
        self.nodes[node.config] = node
        return node.config, node.port

    def status(self, cfg):
        # Row S3: the node is stopped at both calls; a stopped store's plain
        # `status' is its checkpoint header, and `--replay' asks for the
        # report over the replayed log (headroom, maintenance-reserve, reclaim).
        r = self.invoke("operator", cfg, "status", "--replay")
        lines = r.stdout.decode(errors="replace").splitlines()

        def pick(word):
            return next((l for l in lines if l.startswith(word)), "")
        return {"exit": r.returncode, "headroom": pick("headroom"),
                "reserve": pick("maintenance-reserve"), "reclaim": pick("reclaim")}

    def post(self, c, i):
        first, final = c.post(article(i))
        if final is None:
            return first.decode(errors="replace").strip()
        return final.decode(errors="replace").strip()

    def verb(self, cfg, *words, env=None):
        r = self.invoke("operator", cfg, *words, env=env, timeout=3600)
        return (r.returncode, r.stdout.decode(errors="replace").strip()[-300:],
                r.stderr.decode(errors="replace").strip()[-300:])

    def cut_copy(self, store, name):
        copy = self.temp / name
        shutil.rmtree(copy, ignore_errors=True)
        shutil.copytree(store, copy)
        return copy, self.config(copy, name)[0]

    def history(self, store):
        """The committed history the store's open reads, as `store export'
        writes it (the archive's files and their digests)."""
        archive = self.temp / "history-archive"
        shutil.rmtree(archive, ignore_errors=True)
        r = self.invoke("store", store, "export", archive, timeout=3600)
        self.assertEqual(r.returncode, 0, r.stderr.decode(errors="replace"))
        tree = archive_tree(archive)
        shutil.rmtree(archive, ignore_errors=True)
        return tree

    @staticmethod
    def same_but_the_instant(got, reference):
        """GOT is REFERENCE's history but for the reclaim's own instant: the
        same files, and only the newest configuration record (the instant
        record, whose stamp is the clock of the run that made it) and the
        MANIFEST that digests it differ.  A second instant record (a fresh
        reclaim after the death instead of the recorded one) is a different
        file set and fails."""
        if set(got) != set(reference):
            return False
        configs = sorted(name for name in reference if name.startswith("config/"))
        allowed = {"MANIFEST", *configs[-1:]}
        return all(got[name] == reference[name] for name in reference if name not in allowed)

    def cuts(self, store, verb):
        """A death at every rotation and drop cut of VERB on a copy of STORE;
        returns the failures."""
        ref, rcfg = self.cut_copy(store, "cut-ref")
        code, _, err = self.verb(rcfg, "store", verb)
        self.assertEqual(code, 0, err)
        reference = self.history(ref)
        shutil.rmtree(ref, ignore_errors=True)
        bad = []
        for point in LOG_CUTS:
            copy, ccfg = self.cut_copy(store, "cut-%s-%s" % (verb, point))
            env = {"FN_NATIVE_LOG_FAULT": point}
            first = "exit-%d" % self.verb(ccfg, "store", verb, env=env)[0]
            reopened = self.status(ccfg)
            if verb == "reclaim":
                # PKT-857: a reclaim publishes its instant (the
                # `retention-reclaim-at' configuration record) before it
                # rewrites anything, and every cut here is after it.  The
                # recovery completes THAT reclaim (`--recorded': the
                # decision from the recorded instant, nothing new recorded;
                # host/native/checkpoint.lisp fnn-log-reclaim-steps).
                rerun = self.verb(ccfg, "store", verb, "--recorded")
                converged = self.same_but_the_instant(self.history(copy), reference)
            else:
                rerun = self.verb(ccfg, "store", verb)
                converged = self.history(copy) == reference
            # A cut the verb never reaches (nothing to rotate or drop) is an
            # unexercised cut, not a pass.
            reached = first == "exit--9"
            self.out(tag="cut", verb=verb, point=point, first=first,
                     reached=reached, reopen_status=reopened["exit"],
                     rerun_exit=rerun[0], rerun_head=rerun[1][:120],
                     rerun_stderr=rerun[2][-160:], converged=converged)
            if (not reached or reopened["exit"] != 0 or not converged
                    or rerun[0] != 0):
                bad.append((verb, point, first))
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
        self.out(tag="undertaken", status=promised)
        self.assertIn("debt=1 held", promised["reserve"])

        # 2. Fill until ordinary admission refuses by name.
        t0 = time.perf_counter()
        owner = self.nodes[cfg]
        owner.start(timeout=600)
        accepted, refused = 0, ""
        try:
            c = Client(port, timeout=600)
            for i in range(5000):
                answer = self.post(c, i)
                if not answer.startswith("240"):
                    refused = answer
                    break
                accepted += 1
            c.close()
        finally:
            owner.stop(expect=None, grace=600)
        full = self.status(cfg)
        self.out(tag="full", accepted=accepted, refused=refused,
                 wall_s=round(time.perf_counter() - t0, 1),
                 footprint=footprint(sender), status=full)
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
                p.stop(grace=10)
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
                 status=discharged)
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
        # The reclaim campaign on copies of the store before its compaction:
        # after `store compact' the active segment is empty and a checkpoint
        # does not rotate it again (native m6: every reclaim cut unreached),
        # and the full store takes no commit to fill one.
        bad += self.cuts(sender, "reclaim")
        before_compact = footprint(sender)
        code, so, se = self.verb(cfg, "store", "compact")
        self.out(tag="compact", exit=code, stdout=so[:200], stderr=se,
                 before=before_compact, after=footprint(sender))
        self.assertEqual(code, 0, se)
        before = footprint(sender)
        pre = self.status(cfg)
        code, so, se = self.verb(cfg, "store", "reclaim")
        after = footprint(sender)
        post = self.status(cfg)
        self.out(tag="reclaim", exit=code, stdout=so[:200], stderr=se,
                 before=before, after=after, status_before=pre, status_after=post)
        self.assertEqual(code, 0, se)
        self.assertEqual(post["exit"], 0)
        owner = self.nodes[cfg]
        owner.start(timeout=600)
        try:
            c = Client(port, timeout=600)
            reused = [self.post(c, 900000 + k) for k in range(3)]
            c.close()
        finally:
            owner.stop(expect=None, grace=600)
        final = self.status(cfg)
        self.out(tag="reuse", posts=reused, footprint=footprint(sender), status=final)
        self.out(tag="cuts", failures=bad)
        self.assertEqual(bad, [])
        self.assertTrue(all(a.startswith("240") for a in reused), reused)


DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")


@unittest.skipUnless(executable(DEVELOPER), "build/fn-host-developer is required")
class NativeStorePostVerdictTests(unittest.TestCase):
    """Memory landing 3+4a: the developer `store post' asks ACL2's article
    verdict before it writes (host/native/io.lisp fnn-command-post ->
    host/store-node-host.lisp fn-store-sn-article-verdict-word ->
    books/store-capacity-vector.lisp fn-cvec-article-verdict-word, whose
    :admissible is exactly fn-cvec-article-verdict-at's, the count gate and
    the history gate fn-sbud-article-verdict-at at the article's own figure,
    then the capacity vector after it).  KEYSTONES
    fn-cvec-article-verdict-keeps-the-vector,
    fn-cvec-article-verdict-keeps-the-vector-for-a-held-row and
    fn-sbud-article-verdict-keeps-history: an article the verdict admits
    leaves the committed history plus its payload within H with the
    maintenance reserve still held.  Every figure is read back from the
    store's own report (`status --replay': the headroom line and the
    maintenance-reserve line), none is pinned: an article of exactly the room
    left (H less the history and the reserve) is admitted and fills H to the
    reserve, one octet more is refused by the history's word, and the
    transactions are admitted while one more record and the release's fit T,
    then refused by their word; a refusal writes nothing."""

    STEP = 30000

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.base = Path(self.tmp.name)
        self.serial = 0

    def tearDown(self):
        self.tmp.cleanup()

    def fn(self, *words):
        return run([DEVELOPER, "--fn", *[str(w) for w in words]], timeout=600,
                   env=environment({}))

    def init(self, name, *flags):
        store = self.base / name
        made = self.fn("store", store, "init", "--profile", "development",
                       "--max-record-octets", "196608", "--max-article-octets", "32768",
                       "--max-groups-per-article", "16", *flags, GROUP)
        self.assertEqual(made.returncode, EXIT_OK, made.stderr)
        return store

    def report(self, store):
        status = self.fn("store", store, "status", "--replay")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr)
        room, reserve = {}, {}
        for line in status.stdout.decode("ascii").splitlines():
            words = line.split()
            if words and words[0] == "headroom":
                room = {k: int(v) for k, v in (w.split("=", 1) for w in words[1:])}
            elif words and words[0] == "maintenance-reserve":
                reserve = dict(w.split("=", 1) for w in words[1:] if "=" in w)
                reserve["held"] = words[-1] == "held"
        self.assertTrue(room and reserve, status.stdout)
        return room, int(reserve["octets"]), int(reserve["debt"]), reserve["held"]

    def post(self, store, octets):
        self.serial += 1
        payload = self.base / "payload-{}".format(self.serial)
        payload.write_bytes(b"p" * octets)
        return self.fn("store", store, "post",
                       "<verdict-{}@capacity.example.invalid>".format(self.serial),
                       payload, "-", "-", GROUP)

    def assert_refused(self, store, octets, word):
        before = self.report(store)
        refused = self.post(store, octets)
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr)
        self.assertIn(word, refused.stderr)
        self.assertEqual(self.report(store), before)

    def test_store_post_admits_to_the_last_octet_of_h_and_the_last_transaction_of_t(self):
        store = self.init("history", "--max-history-octets", "262144")
        room, reserve, debt, held = self.report(store)
        self.assertEqual(debt, 0)
        self.assertTrue(held)

        def left(r, octets):
            return r["history-bound"] - r["bytes-used"] - octets
        while left(room, reserve) > self.STEP:
            posted = self.post(store, self.STEP)
            self.assertEqual(posted.returncode, EXIT_OK, posted.stderr)
            after, reserve, debt, held = self.report(store)
            self.assertEqual(after["bytes-used"], room["bytes-used"] + self.STEP)
            self.assertLessEqual(after["bytes-used"] + reserve, after["history-bound"])
            self.assertTrue(held)
            room = after
        last = left(room, reserve)
        self.assertGreaterEqual(last, 1)
        self.assertLess(last, 32768)
        self.assert_refused(store, last + 1, b"(history-exhausted)")
        posted = self.post(store, last)
        self.assertEqual(posted.returncode, EXIT_OK, posted.stderr)
        full, reserve, debt, held = self.report(store)
        self.assertEqual(full["bytes-used"] + reserve, full["history-bound"])
        self.assertTrue(held)
        self.assert_refused(store, 1, b"(history-exhausted)")

        store = self.init("transactions", "--max-transactions", "4",
                          "--max-history-octets", "262144")
        room, reserve, debt, held = self.report(store)
        budget = room["transactions-budget"]
        while room["transactions-used"] + 1 < budget:
            posted = self.post(store, 1)
            self.assertEqual(posted.returncode, EXIT_OK, posted.stderr)
            after, reserve, debt, held = self.report(store)
            self.assertEqual(after["transactions-used"], room["transactions-used"] + 1)
            self.assertTrue(held)
            room = after
        self.assertEqual(room["transactions-used"], budget - 1)
        self.assert_refused(store, 1, b"(transaction count)")


if __name__ == "__main__":
    unittest.main()

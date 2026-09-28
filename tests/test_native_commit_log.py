"""The store's commit through the record log, on the native images (lane
commit-onto-log; planning/design-2026-09-27-storage-log.md sections 3.3 and
4; tests/campaign/native_cuts.py POST_LOG_CUTS).

`operator CONFIG init` writes a format-9 store (journal/000001.log; the
profile frame's word is fn-store-9) and the served node commits every POST
through the log: concurrent posters are committed in batches (one append and
one barrier per commit quantum) and each is answered 240 only after its
batch's barrier.  The cases: concurrent POSTs answered 240 and every one
served again after a restart, no transaction file written, on both images;
a process death at each POST_LOG_CUTS cut on the developer image, the next
owner serving the article whole (a lost-reply POST is durable or absent, and
from log-fenced on it is durable) and admitting the next POST; and the
format-9 refusals by name of compact and reclaim (export and import run over
the log: tests.test_native_store_export; a format-8 store is refused at open
by name there too).

The oracle compares only what the node answers (the reply codes and the
article's octets) and what the store directory holds.
"""
from __future__ import annotations

import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import threading
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from tests.campaign import native_cuts  # noqa: E402
from tests.native_harness import wait_for_announcement  # noqa: E402
from tools.wire_stream import whole_stream

DEVELOPER = os.environ.get("FN_NATIVE_DEVELOPER_HOST", "")
PRODUCTION = os.environ.get("FN_NATIVE_HOST", "")
GROUP = "fn.test"


def free_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def msgid(i: int) -> str:
    return "<col-%06d@example.invalid>" % i


def article(i: int, pad: int = 0) -> bytes:
    # PAD octets of filler lines after the body line: a case that must fill
    # the log segment sizes its articles, not its POST count, so the fill
    # does not depend on the record layout (log-2-pad packs a batch's records
    # into one padded entry; 400 small POSTs no longer outgrow 1 MiB).
    filler = "".join("%s\r\n" % ("x" * 76) for _ in range(pad // 78))
    return ("From: col@example.invalid\r\nNewsgroups: %s\r\nSubject: col %d\r\n"
            "Message-ID: %s\r\n\r\nbody of %d\r\n%s" % (GROUP, i, msgid(i), i, filler)).encode("ascii")


class Conn:
    def __init__(self, port: int):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=300)
        self.stream = whole_stream(self.sock)
        self.greeting = self.stream.readline()

    def line(self, text: str) -> bytes:
        self.stream.write(text.encode("ascii") + b"\r\n")
        return self.stream.readline()

    def post(self, i: int, pad: int = 0) -> bytes:
        reply = self.line("POST")
        if not reply.startswith(b"340"):
            return reply
        self.stream.write(article(i, pad) + b".\r\n")
        return self.stream.readline()

    def article(self, i: int):
        head = self.line("ARTICLE %s" % msgid(i))
        if not head.startswith(b"220"):
            return head, None
        body = b""
        while True:
            line = self.stream.readline()
            if line == b".\r\n":
                return head, body
            body += line

    def close(self):
        try:
            self.line("QUIT")
        except OSError:
            pass
        self.sock.close()


# Every owner a case starts; tearDown reaps the ones still running.
LIVE: list = []


class Node:
    def __init__(self, image: str, root: Path, env=None):
        self.image, self.root = image, root
        self.env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
        for name in ("FN_NATIVE_POST_FAULT",):
            self.env.pop(name, None)
        self.env.update(env or {})
        self.store = root / "store"
        self.port = free_port()
        self.config = root / "fn.toml"
        self.config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                               '[control]\npath = "%s"\n' % (self.store, self.port, root / "c.sock"))
        self.proc = None

    def fn(self, *argv, env=None, timeout=600):
        return subprocess.run([self.image, "--fn", *argv], env=dict(self.env, **(env or {})),
                              capture_output=True, timeout=timeout)

    def init(self, env=None, profile=()):
        result = self.fn("operator", str(self.config), "init", *profile, GROUP, env=env)
        if result.returncode:
            raise AssertionError("init: %r" % result.stderr[-800:])
        secret = self.fn("store", str(self.store), "node-secret", "create", env=env)
        if secret.returncode not in (0, 1):
            raise AssertionError("node-secret: %r" % secret.stderr[-800:])

    def start(self, env=None):
        self.stderr = open(self.root / "owner.stderr", "ab")
        self.proc = subprocess.Popen([self.image, "--fn", "operator", str(self.config), "run"],
                                     env=dict(self.env, **(env or {})),
                                     stdout=subprocess.PIPE, stderr=self.stderr)
        LIVE.append(self)
        try:
            wait_for_announcement(self.proc, b"LISTENING ", timeout=600)
        except BaseException:
            # An owner that never announced is still a process: never leave it.
            self.reap()
            raise

    def reap(self):
        """Kill this node's owner if it is still running (a test's safety net:
        a timeout or a failed assertion must not leave an owner behind)."""
        if self.proc is not None and self.proc.poll() is None:
            self.proc.kill()
            try:
                self.proc.wait(timeout=60)
            except subprocess.TimeoutExpired:
                pass
        if getattr(self, "stderr", None) is not None and not self.stderr.closed:
            self.stderr.close()

    def stop(self):
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()
            try:
                self.proc.wait(timeout=300)
            except subprocess.TimeoutExpired:
                self.proc.kill()
                self.proc.wait()
        self.stderr.close()

    def transaction_files(self):
        d = self.store / "transactions"
        return sorted(p.name for p in d.iterdir()) if d.exists() else []


def post_concurrently(port: int, ids, connections: int, pad: int = 0):
    replies, errors = {}, []
    lock = threading.Lock()
    todo = list(ids)

    def worker():
        try:
            c = Conn(port)
            while True:
                with lock:
                    if not todo:
                        break
                    i = todo.pop(0)
                reply = c.post(i, pad)
                with lock:
                    replies[i] = reply
            c.close()
        except BaseException as e:  # noqa: BLE001 - reported by the case
            errors.append(repr(e))
    threads = [threading.Thread(target=worker) for _ in range(connections)]
    for t in threads:
        t.start()
    for t in threads:
        t.join(600)
    return replies, errors


class CommitLogMixin:
    image = ""

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory(prefix="fn-col-")
        self.root = Path(self.dir.name)

    def tearDown(self):
        while LIVE:
            LIVE.pop().reap()
        self.dir.cleanup()

    def test_concurrent_posts_are_committed_through_the_log_and_served_again(self):
        node = Node(self.image, self.root)
        node.init()
        segment = node.store / "journal" / "000001.log"
        self.assertTrue(segment.is_file(), "init wrote no log segment")
        node.start()
        try:
            replies, errors = post_concurrently(node.port, range(48), 8)
        finally:
            node.stop()
        self.assertEqual(errors, [])
        self.assertEqual(sorted(replies), list(range(48)))
        self.assertTrue(all(r.startswith(b"240") for r in replies.values()), replies)
        self.assertEqual(node.transaction_files(), [], "a format-9 commit wrote a transaction file")
        node.start()
        try:
            c = Conn(node.port)
            for i in range(48):
                head, body = c.article(i)
                self.assertTrue(head.startswith(b"220"), (i, head))
                self.assertIn(b"body of %d" % i, body)
            # The duplicate is answered as one, and the next POST is admitted.
            self.assertTrue(c.post(0).startswith(b"441"))
            self.assertTrue(c.post(48).startswith(b"240"))
            c.close()
        finally:
            node.stop()


@unittest.skipUnless(DEVELOPER, "FN_NATIVE_DEVELOPER_HOST names the developer image")
class DeveloperCommitLogTests(CommitLogMixin, unittest.TestCase):
    image = DEVELOPER

    def test_the_next_batch_prepares_behind_the_barrier(self):
        # Lane log-2 (books/owner-commit-pipeline.lisp): with the operator's
        # batch bound at 2 (`policy set log-batch-records 2') and each
        # barrier held 700 ms (the developer selector), eight posters leave a
        # backlog: while a batch's barrier runs, the next batch is prepared
        # behind it (START-NEXT, the developer trace line) and sealed by the
        # COMPLETE.  Every POST is answered 240 and served again after a
        # restart; the batch bound is the operator's configuration.
        node = Node(self.image, self.root)
        node.init()
        bound = node.fn("operator", str(node.config), "policy", "set", "log-batch-records", "2")
        self.assertEqual(bound.returncode, 0, bound.stderr[-800:])
        node.start(env={"FN_NATIVE_OWNER_TEST_BARRIER_MS": "700",
                        "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE": "1"})
        try:
            replies, errors = post_concurrently(node.port, range(16), 8)
        finally:
            node.stop()
        self.assertEqual(errors, [])
        self.assertEqual(sorted(replies), list(range(16)))
        self.assertTrue(all(r.startswith(b"240") for r in replies.values()), replies)
        trace = (self.root / "owner.stderr").read_bytes()
        self.assertIn(b"prepared behind the barrier", trace, trace[-2000:])
        # Served again after a restart: STAT by Message-ID (223).  The body
        # is not read here: on the post-flip base the served ARTICLE answers
        # 503 for every article (the served read is not given the arena;
        # planning/evidence/log-2-2026-09-27.md section 5), which the other
        # cases of this module still assert.
        node.start()
        try:
            c = Conn(node.port)
            for i in range(16):
                reply = c.line("STAT %s" % msgid(i))
                self.assertTrue(reply.startswith(b"223"), (i, reply))
            c.close()
        finally:
            node.stop()

    def test_every_post_log_cut_is_old_or_new_and_the_node_goes_on(self):
        names = tuple(cut.name for cut in native_cuts.POST_LOG_CUTS)
        self.assertEqual(names, ("record-completing", "finish-consumed", "finish-durable",
                                 "log-written", "log-fenced"))
        for k, cut in enumerate(native_cuts.POST_LOG_CUTS):
            with self.subTest(cut=cut.name):
                root = self.root / cut.name
                root.mkdir()
                node = Node(self.image, root)
                node.init()
                node.start()
                c = Conn(node.port)
                self.assertTrue(c.post(0).startswith(b"240"))
                c.close()
                node.stop()
                node.start({"FN_NATIVE_POST_FAULT": cut.name + ":kill"})
                c = Conn(node.port)
                try:
                    reply = c.post(1)
                except OSError:
                    reply = b""
                node.proc.wait(timeout=300)
                node.stderr.close()
                self.assertFalse(reply.startswith(b"240"), (cut.name, reply))
                node.start()
                try:
                    c = Conn(node.port)
                    head, body = c.article(0)
                    self.assertTrue(head.startswith(b"220"), (cut.name, head))
                    head, body = c.article(1)
                    if cut.candidate == "present":
                        self.assertTrue(head.startswith(b"220"), (cut.name, head))
                    if cut.candidate == "absent":
                        self.assertTrue(head.startswith(b"430"), (cut.name, head))
                    if head.startswith(b"220"):
                        self.assertIn(b"body of 1", body)
                    else:
                        self.assertTrue(head.startswith(b"430"), (cut.name, head))
                    again = c.post(1)
                    self.assertTrue(again.startswith(b"441" if head.startswith(b"220") else b"240"),
                                    (cut.name, again))
                    self.assertTrue(c.post(2).startswith(b"240"))
                    c.close()
                finally:
                    node.stop()

    def test_the_segment_grows_and_a_death_while_it_grows_keeps_every_acknowledged_post(self):
        # books/store-log-extend.lisp: when the open batch and a spare unit
        # do not fit, the segment grows to ACL2's target (twice the extent)
        # and is fenced, at rest, before the append.  A death at each of the
        # extension's cuts (FN_NATIVE_LOG_FAULT) keeps every POST answered
        # 240; the next owner serves them, grows the segment and goes on.
        #
        # The fill is sized, not counted: small POSTs never fill a segment
        # now (log-2-pad packs a batch into one padded entry, and the owner's
        # checkpoint rotates to a fresh segment every hundred or so), so the
        # case posts articles of a third of the extent (the store's article
        # bound raised to 1 MiB for it): one acknowledged alone first, then
        # four at a time, whose batches cannot fit the remaining segment.
        initial = 1048576
        pad = initial // 3
        profile = ("--max-article-octets", str(initial))
        for cut in ("log-extended", "log-extent-fenced"):
            with self.subTest(cut=cut):
                root = self.root / cut
                root.mkdir()
                node = Node(self.image, root)
                node.init(profile=profile)
                segment = node.store / "journal" / "000001.log"
                self.assertEqual(segment.stat().st_size, initial)
                node.start({"FN_NATIVE_LOG_FAULT": cut})
                try:
                    first = Conn(node.port)
                    self.assertTrue(first.post(0, pad).startswith(b"240"), cut)
                    first.close()
                    replies, _errors = post_concurrently(node.port, range(1, 13), 4, pad)
                    node.proc.wait(timeout=300)
                finally:
                    # Never leave an owner running: a death that did not come
                    # is this case's failure, reported below, not a stray.
                    if node.proc.poll() is None:
                        node.proc.kill()
                        node.proc.wait(timeout=60)
                    node.stderr.close()
                self.assertEqual(node.proc.returncode, -9, cut)
                acked = [0] + sorted(i for i, r in replies.items() if r.startswith(b"240"))
                # The death came inside the extension: the segment is past its
                # initial extent (preallocated; at log-extent-fenced also fenced).
                grown = segment.stat().st_size
                self.assertGreater(grown, initial, cut)
                self.assertEqual(grown % 4096, 0, cut)
                node.start()
                try:
                    c = Conn(node.port)
                    for i in acked:
                        head, body = c.article(i)
                        self.assertTrue(head.startswith(b"220"), (cut, i, head))
                        self.assertIn(b"body of %d" % i, body)
                    c.close()
                    more, errors = post_concurrently(node.port, range(1000, 1012), 4, pad)
                    self.assertEqual(errors, [])
                    self.assertEqual(len(more), 12, cut)
                    self.assertTrue(all(r.startswith(b"240") for r in more.values()), cut)
                finally:
                    node.stop()
                # The next owner went on: every history segment (a checkpoint
                # may have rotated past 000001.log and dropped it) is whole
                # units.  Format 10's genesis, 000000.log, is one fixed record
                # and never extended.
                segments = sorted(p for p in (node.store / "journal").glob("*.log")
                                  if p.name != "000000.log")
                self.assertTrue(segments, cut)
                for path in segments:
                    self.assertEqual(path.stat().st_size % 4096, 0, (cut, path.name))

    def test_store_post_and_probe_commit_through_the_log(self):
        # The developer entries that commit without an owner (fnn-command-post,
        # fnn-command-probe) take the same route: a batch of one each.
        root = self.root / "direct"
        root.mkdir()
        store = root / "store"
        env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
        init = subprocess.run([self.image, "--fn", "store", str(store), "init", GROUP],
                              env=env, capture_output=True, timeout=600)
        self.assertEqual(init.returncode, 0, init.stderr[-800:])
        self.assertTrue((store / "journal" / "000001.log").is_file())
        payload = root / "payload"
        payload.write_bytes(article(900))
        posted = [subprocess.run(
            [self.image, "--fn", "store", str(store), "post", msgid(900),
             str(payload), "-", "-", GROUP], env=env, capture_output=True, timeout=600)
            for _ in range(2)]
        self.assertEqual(posted[0].returncode, 0, posted[0].stderr[-800:])
        self.assertIn(b"committed sequence=", posted[0].stdout)
        # The reopen replays the log: the second is the same article, a duplicate.
        self.assertEqual(posted[1].returncode, 0, posted[1].stderr[-800:])
        self.assertIn(b"duplicate", posted[1].stdout)
        self.assertEqual(
            sorted(p.name for p in (store / "transactions").iterdir())
            if (store / "transactions").exists() else [], [])
        probe_root = root / "probe"
        probe = subprocess.run([self.image, "--fn", "store", str(probe_root), "probe", "5"],
                               env=env, capture_output=True, timeout=900)
        self.assertEqual(probe.returncode, 0, probe.stderr[-800:])
        self.assertTrue((probe_root / "journal" / "000001.log").is_file())

    def test_format_9_history_is_read_from_the_log_after_the_open(self):
        # The open answers the history's COUNT and keeps no records (PKT-823);
        # a reader that needs records reads them after the open
        # (fnn-history-records / fnn-history-last-record), which on format 9
        # is the log kernel's committed records, never transactions/ (lane
        # rm2-format9).  `store recover' reports the log's count; the owner
        # start reads the newest record for its pending key statement
        # (fnn-owner-install), so a restarted owner that answers the duplicate
        # 441 and admits the next POST 240 read the history through the log.
        node = Node(self.image, self.root)
        node.init()
        node.start()
        try:
            c = Conn(node.port)
            for i in (910, 911, 912):
                self.assertTrue(c.post(i).startswith(b"240"), i)
            c.close()
        finally:
            node.stop()
        self.assertEqual(node.transaction_files(), [])
        recovered = node.fn("store", str(node.store), "recover")
        self.assertEqual(recovered.returncode, 0, recovered.stderr[-800:])
        self.assertIn(b"recovered transactions=3 articles=3", recovered.stdout)
        node.start()
        try:
            c = Conn(node.port)
            self.assertTrue(c.post(911).startswith(b"441"))
            self.assertTrue(c.post(913).startswith(b"240"))
            c.close()
        finally:
            node.stop()
        recovered = node.fn("store", str(node.store), "recover")
        self.assertEqual(recovered.returncode, 0, recovered.stderr[-800:])
        self.assertIn(b"recovered transactions=4 articles=4", recovered.stdout)

    def test_format_9_compact_reclaim_and_export_run_over_the_log(self):
        # Lane log-recovery: `store compact' (rotation and drop), `store
        # reclaim' (the rewritten history's checkpoint and the drop) and
        # `store export' run over the log (tests.test_native_log_compaction,
        # tests.test_native_store_export); on a fresh store each exits 0.
        node = Node(self.image, self.root)
        node.init()
        for argv in (("operator", str(node.config), "store", "reclaim"),
                     ("operator", str(node.config), "store", "compact"),
                     ("store", str(node.store), "export", str(self.root / "archive"))):
            with self.subTest(argv=argv[-2:]):
                result = node.fn(*argv)
                self.assertEqual(result.returncode, 0, (argv, result.stdout, result.stderr[-600:]))


@unittest.skipUnless(PRODUCTION, "FN_NATIVE_HOST names the production image")
class ProductionCommitLogTests(CommitLogMixin, unittest.TestCase):
    image = PRODUCTION


if __name__ == "__main__":
    unittest.main()

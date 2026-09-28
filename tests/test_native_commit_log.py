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

import threading
import unittest

from tests.campaign import native_cuts  # noqa: E402
from tests.native_harness import EXIT, Client, Node, native_image, requires, scratch

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
PRODUCTION = native_image("FN_NATIVE_HOST")
GROUP = "fn.test"


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


def connect(port: int) -> Client:
    return Client(port, timeout=300, greeting=None)


def post(client: Client, i: int, pad: int = 0) -> bytes:
    """POST article I; the final reply, or the first when it was not 340."""
    first, final = client.post(article(i, pad))
    return first if final is None else final


def read_article(client: Client, i: int):
    """(status line, the served octets; b"" when not 220)."""
    return client.multiline("ARTICLE %s" % msgid(i))


def init(node: Node, profile=()):
    node.operator("init", *profile, GROUP, timeout=600, expect=EXIT.OK)
    secret = node.store("node-secret", "create", timeout=600)
    if secret.returncode not in (EXIT.OK, EXIT.REFUSED):
        raise AssertionError("node-secret: %r" % secret.stderr[-800:])


def start(node: Node, env=None):
    return node.start(env=env, timeout=600)


def stop(node: Node):
    node.stop(expect=None, grace=300)


def transaction_files(node: Node):
    d = node.store_path / "transactions"
    return sorted(p.name for p in d.iterdir()) if d.exists() else []


def post_concurrently(port: int, ids, connections: int, pad: int = 0):
    replies, errors = {}, []
    lock = threading.Lock()
    todo = list(ids)

    def worker():
        try:
            c = connect(port)
            while True:
                with lock:
                    if not todo:
                        break
                    i = todo.pop(0)
                reply = post(c, i, pad)
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
    image = None

    def setUp(self):
        self.root = scratch(self, "fn-col-")

    def test_concurrent_posts_are_committed_through_the_log_and_served_again(self):
        node = Node(self, self.image, root=self.root / "node")
        init(node)
        segment = node.store_path / "journal" / "000001.log"
        self.assertTrue(segment.is_file(), "init wrote no log segment")
        start(node)
        try:
            replies, errors = post_concurrently(node.port, range(48), 8)
        finally:
            stop(node)
        self.assertEqual(errors, [])
        self.assertEqual(sorted(replies), list(range(48)))
        self.assertTrue(all(r.startswith(b"240") for r in replies.values()), replies)
        self.assertEqual(transaction_files(node), [], "a format-9 commit wrote a transaction file")
        start(node)
        try:
            c = connect(node.port)
            for i in range(48):
                head, body = read_article(c, i)
                self.assertTrue(head.startswith(b"220"), (i, head))
                self.assertIn(b"body of %d" % i, body)
            # The duplicate is answered as one, and the next POST is admitted.
            self.assertTrue(post(c, 0).startswith(b"441"))
            self.assertTrue(post(c, 48).startswith(b"240"))
            c.close()
        finally:
            stop(node)


@requires(DEVELOPER)
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
        node = Node(self, self.image, root=self.root / "node")
        init(node)
        bound = node.invoke("operator", node.config, "policy", "set", "log-batch-records", "2")
        self.assertEqual(bound.returncode, 0, bound.stderr[-800:])
        traced = start(node, {"FN_NATIVE_OWNER_TEST_BARRIER_MS": "700",
                              "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE": "1"})
        try:
            replies, errors = post_concurrently(node.port, range(16), 8)
        finally:
            stop(node)
        self.assertEqual(errors, [])
        self.assertEqual(sorted(replies), list(range(16)))
        self.assertTrue(all(r.startswith(b"240") for r in replies.values()), replies)
        trace = traced.stderr.since(0)
        self.assertIn(b"prepared behind the barrier", trace, trace[-2000:])
        # Served again after a restart: STAT by Message-ID (223).  The body
        # is not read here: on the post-flip base the served ARTICLE answers
        # 503 for every article (the served read is not given the arena;
        # planning/evidence/log-2-2026-09-27.md section 5), which the other
        # cases of this module still assert.
        start(node)
        try:
            c = connect(node.port)
            for i in range(16):
                reply = c.command("STAT %s" % msgid(i))
                self.assertTrue(reply.startswith(b"223"), (i, reply))
            c.close()
        finally:
            stop(node)

    def test_every_post_log_cut_is_old_or_new_and_the_node_goes_on(self):
        names = tuple(cut.name for cut in native_cuts.POST_LOG_CUTS)
        self.assertEqual(names, ("record-completing", "finish-consumed", "finish-durable",
                                 "log-written", "log-fenced"))
        for k, cut in enumerate(native_cuts.POST_LOG_CUTS):
            with self.subTest(cut=cut.name):
                root = self.root / cut.name
                root.mkdir()
                node = Node(self, self.image, root=root)
                init(node)
                start(node)
                c = connect(node.port)
                self.assertTrue(post(c, 0).startswith(b"240"))
                c.close()
                stop(node)
                start(node, {"FN_NATIVE_POST_FAULT": cut.name + ":kill"})
                c = connect(node.port)
                try:
                    reply = post(c, 1)
                except (OSError, EOFError):
                    reply = b""
                node.process.wait(timeout=300)
                node.process.finish()
                self.assertFalse(reply.startswith(b"240"), (cut.name, reply))
                start(node)
                try:
                    c = connect(node.port)
                    head, body = read_article(c, 0)
                    self.assertTrue(head.startswith(b"220"), (cut.name, head))
                    head, body = read_article(c, 1)
                    if cut.candidate == "present":
                        self.assertTrue(head.startswith(b"220"), (cut.name, head))
                    if cut.candidate == "absent":
                        self.assertTrue(head.startswith(b"430"), (cut.name, head))
                    if head.startswith(b"220"):
                        self.assertIn(b"body of 1", body)
                    else:
                        self.assertTrue(head.startswith(b"430"), (cut.name, head))
                    again = post(c, 1)
                    self.assertTrue(again.startswith(b"441" if head.startswith(b"220") else b"240"),
                                    (cut.name, again))
                    self.assertTrue(post(c, 2).startswith(b"240"))
                    c.close()
                finally:
                    stop(node)

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
                node = Node(self, self.image, root=root)
                init(node, profile=profile)
                segment = node.store_path / "journal" / "000001.log"
                self.assertEqual(segment.stat().st_size, initial)
                start(node, {"FN_NATIVE_LOG_FAULT": cut})
                try:
                    first = connect(node.port)
                    self.assertTrue(post(first, 0, pad).startswith(b"240"), cut)
                    first.close()
                    replies, _errors = post_concurrently(node.port, range(1, 13), 4, pad)
                    node.process.wait(timeout=300)
                finally:
                    # Never leave an owner running: a death that did not come
                    # is this case's failure, reported below, not a stray.
                    if node.process.poll() is None:
                        node.process.kill()
                        node.process.wait(timeout=60)
                    node.process.finish()
                self.assertEqual(node.process.returncode, -9, cut)
                acked = [0] + sorted(i for i, r in replies.items() if r.startswith(b"240"))
                # The death came inside the extension: the segment is past its
                # initial extent (preallocated; at log-extent-fenced also fenced).
                grown = segment.stat().st_size
                self.assertGreater(grown, initial, cut)
                self.assertEqual(grown % 4096, 0, cut)
                start(node)
                try:
                    c = connect(node.port)
                    for i in acked:
                        head, body = read_article(c, i)
                        self.assertTrue(head.startswith(b"220"), (cut, i, head))
                        self.assertIn(b"body of %d" % i, body)
                    c.close()
                    more, errors = post_concurrently(node.port, range(1000, 1012), 4, pad)
                    self.assertEqual(errors, [])
                    self.assertEqual(len(more), 12, cut)
                    self.assertTrue(all(r.startswith(b"240") for r in more.values()), cut)
                finally:
                    stop(node)
                # The next owner went on: every history segment (a checkpoint
                # may have rotated past 000001.log and dropped it) is whole
                # units.  Format 10's genesis, 000000.log, is one fixed record
                # and never extended.
                segments = sorted(p for p in (node.store_path / "journal").glob("*.log")
                                  if p.name != "000000.log")
                self.assertTrue(segments, cut)
                for path in segments:
                    self.assertEqual(path.stat().st_size % 4096, 0, (cut, path.name))

    def test_store_post_and_probe_commit_through_the_log(self):
        # The developer entries that commit without an owner (fnn-command-post,
        # fnn-command-probe) take the same route: a batch of one each.
        root = self.root / "direct"
        node = Node(self, self.image, root=root, listener=False, control=False)
        store = node.store_path
        init = node.store("init", GROUP, timeout=600)
        self.assertEqual(init.returncode, 0, init.stderr[-800:])
        self.assertTrue((store / "journal" / "000001.log").is_file())
        payload = root / "payload"
        payload.write_bytes(article(900))
        posted = [node.store("post", msgid(900), payload, "-", "-", GROUP, timeout=600)
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
        probe = node.invoke("store", probe_root, "probe", "5", timeout=900)
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
        node = Node(self, self.image, root=self.root / "node")
        init(node)
        start(node)
        try:
            c = connect(node.port)
            for i in (910, 911, 912):
                self.assertTrue(post(c, i).startswith(b"240"), i)
            c.close()
        finally:
            stop(node)
        self.assertEqual(transaction_files(node), [])
        recovered = node.invoke("store", node.store_path, "recover")
        self.assertEqual(recovered.returncode, 0, recovered.stderr[-800:])
        self.assertIn(b"recovered transactions=3 articles=3", recovered.stdout)
        start(node)
        try:
            c = connect(node.port)
            self.assertTrue(post(c, 911).startswith(b"441"))
            self.assertTrue(post(c, 913).startswith(b"240"))
            c.close()
        finally:
            stop(node)
        recovered = node.invoke("store", node.store_path, "recover")
        self.assertEqual(recovered.returncode, 0, recovered.stderr[-800:])
        self.assertIn(b"recovered transactions=4 articles=4", recovered.stdout)

    def test_format_9_compact_reclaim_and_export_run_over_the_log(self):
        # Lane log-recovery: `store compact' (rotation and drop), `store
        # reclaim' (the rewritten history's checkpoint and the drop) and
        # `store export' run over the log (tests.test_native_log_compaction,
        # tests.test_native_store_export); on a fresh store each exits 0.
        node = Node(self, self.image, root=self.root / "node")
        init(node)
        for argv in (("operator", node.config, "store", "reclaim"),
                     ("operator", node.config, "store", "compact"),
                     ("store", node.store_path, "export", self.root / "archive")):
            with self.subTest(argv=argv[-2:]):
                result = node.invoke(*argv, timeout=600)
                self.assertEqual(result.returncode, 0, (argv, result.stdout, result.stderr[-600:]))


@requires(PRODUCTION)
class ProductionCommitLogTests(CommitLogMixin, unittest.TestCase):
    image = PRODUCTION


if __name__ == "__main__":
    unittest.main()

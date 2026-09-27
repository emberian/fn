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
from log-fenced on it is durable) and admitting the next POST; the
per-file layout still written under FN_NATIVE_STORE_FORMAT=8 (the developer
selector for the modules that read it, PKT-830); and the format-9 refusals
by name of compact, reclaim and export.

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
from tests.native_process import wait_for_announcement  # noqa: E402

DEVELOPER = os.environ.get("FN_NATIVE_DEVELOPER_HOST", "")
PRODUCTION = os.environ.get("FN_NATIVE_HOST", "")
GROUP = "fn.test"


def free_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def msgid(i: int) -> str:
    return "<col-%06d@example.invalid>" % i


def article(i: int) -> bytes:
    return ("From: col@example.invalid\r\nNewsgroups: %s\r\nSubject: col %d\r\n"
            "Message-ID: %s\r\n\r\nbody of %d\r\n" % (GROUP, i, msgid(i), i)).encode("ascii")


class Conn:
    def __init__(self, port: int):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=300)
        self.stream = self.sock.makefile("rwb", buffering=0)
        self.greeting = self.stream.readline()

    def line(self, text: str) -> bytes:
        self.stream.write(text.encode("ascii") + b"\r\n")
        return self.stream.readline()

    def post(self, i: int) -> bytes:
        reply = self.line("POST")
        if not reply.startswith(b"340"):
            return reply
        self.stream.write(article(i) + b".\r\n")
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


class Node:
    def __init__(self, image: str, root: Path, env=None):
        self.image, self.root = image, root
        self.env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
        for name in ("FN_NATIVE_POST_FAULT", "FN_NATIVE_STORE_FORMAT"):
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

    def init(self, env=None):
        result = self.fn("operator", str(self.config), "init", GROUP, env=env)
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
        wait_for_announcement(self.proc, b"LISTENING ", timeout=600)

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


def post_concurrently(port: int, ids, connections: int):
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
                reply = c.post(i)
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

    def test_every_post_log_cut_is_old_or_new_and_the_node_goes_on(self):
        names = tuple(cut.name for cut in native_cuts.POST_LOG_CUTS)
        self.assertEqual(names, ("finish-consumed", "finish-durable", "log-written", "log-fenced"))
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

    def test_store_post_and_probe_commit_through_the_log(self):
        # The developer entries that commit without an owner (fnn-command-post,
        # fnn-command-probe) take the same route: a batch of one each.
        root = self.root / "direct"
        root.mkdir()
        store = root / "store"
        env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
        env.pop("FN_NATIVE_STORE_FORMAT", None)
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

    def test_format_8_selector_keeps_the_per_file_layout(self):
        node = Node(self.image, self.root)
        node.init(env={"FN_NATIVE_STORE_FORMAT": "8"})
        self.assertFalse((node.store / "journal").exists())
        node.start({"FN_NATIVE_STORE_FORMAT": "8"})
        try:
            replies, errors = post_concurrently(node.port, range(4), 2)
        finally:
            node.stop()
        self.assertEqual(errors, [])
        self.assertTrue(all(r.startswith(b"240") for r in replies.values()), replies)
        self.assertEqual(len(node.transaction_files()), 4)

    def test_format_9_refuses_what_the_log_does_not_do_yet_by_name(self):
        node = Node(self.image, self.root)
        node.init()
        for argv in (("operator", str(node.config), "store", "compact"),
                     ("operator", str(node.config), "store", "reclaim"),
                     ("store", str(node.store), "export", str(self.root / "archive"))):
            with self.subTest(argv=argv[-2:]):
                result = node.fn(*argv)
                self.assertEqual(result.returncode, 1, (argv, result.stdout, result.stderr))
                self.assertIn(b"reason=record-log", result.stdout + result.stderr)


@unittest.skipUnless(PRODUCTION, "FN_NATIVE_HOST names the production image")
class ProductionCommitLogTests(CommitLogMixin, unittest.TestCase):
    image = PRODUCTION


if __name__ == "__main__":
    unittest.main()

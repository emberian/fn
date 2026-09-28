"""Opt-in native witness for catching up from a peer (NNT-053, SCN-184, PRF-325).

Node A holds 1,000 articles in fn.test.  Node B, new, is configured with A
as a peer (inbound fn.*, dialled by B only) and `peer catch-up A 2`: B's
owner asks A for XFNCATCHUP batches (books/peer-catchup-serve.lisp on A),
verifies each batch's digest chain and offers its records by IHAVE to
itself (books/peer-catchup.lisp, host/native/pull-service.lisp).

- test_catch_up_imports_every_article: B ends with the same Message-IDs in
  fn.test as A, every article's octets equal A's apart from the Path line
  (B's acceptance adds its own identity) and neither node's Xref is
  compared (numbers are each node's own; B numbers in A's log order).  B's
  log names a done round at position 1000 whose digest is the chain over
  A's 1,000 stored articles, recomputed here from A's ARTICLE replies.
- test_kill_mid_catch_up_resumes: B is started with
  FN_CATCHUP_TEST_KILL=before-write:3 (developer image): it dies by SIGKILL
  after committing the third batch's records and before journaling that
  batch's cursor.  Restarted, it resumes from the second batch's cursor: the
  third batch is offered again and drawn 435 (duplicate), and B ends with
  exactly A's articles, none twice.

Run: FN_NATIVE_HOST=<launcher> FN_NATIVE_DEVELOPER_HOST=<developer launcher> \
     python3 -m unittest -v tests.test_native_peer_catchup
"""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import socket
import subprocess
import tempfile
import time
import unittest

from tests.native_process import wait_for_announcement
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import blake3_ref  # noqa: E402  fn's digest (books/blake3.lisp), store format 10

ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))
# FN_CATCHUP_TEST_KILL is a developer-image selector; a production image
# refuses to start with it by name.
DEVELOPER_TEXT = os.environ.get("FN_NATIVE_DEVELOPER_HOST")
DEVELOPER = Path(DEVELOPER_TEXT) if DEVELOPER_TEXT else None
COUNT = int(os.environ.get("FN_CATCHUP_ARTICLES", "1000"))
INTERVAL = "2"
# The store both nodes use, named: 1,000 articles of about 2.3 KiB are
# about 2.3 MiB of history on each node, which the default init's sizing
# for this process refuses early ("no capacity"); 64 MiB of history and
# 32 KiB articles hold them with room.
PROFILE = ("--max-transactions", "16384", "--max-history-octets", str(64 << 20),
           "--max-record-octets", "196608", "--max-article-octets", "32768",
           "--max-groups-per-article", "16", "--max-open-suffix", "128")
# About 2 KiB of body per article, so the 256 KiB batch quantum makes
# several batches of the 1,000.
FILLER = ("catch-up filler line " * 4 + "\r\n") * 24


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def sha256_of(path):
    try:
        return hashlib.sha256(Path(path).read_bytes()).hexdigest()
    except OSError:
        return None


def message_id(n):
    return "<catchup-{:05d}@example.invalid>".format(n)


def article(n):
    lines = ["From: poster@example.invalid", "Newsgroups: fn.test",
             "Subject: catch-up {}".format(n),
             "Date: Sun, 27 Sep 2026 20:00:00 +0000",
             "Message-ID: " + message_id(n)]
    body = "article {}\r\n.a line that begins with a dot\r\n".format(n) + FILLER
    return ("\r\n".join(lines) + "\r\n\r\n" + body).encode("ascii")


class Client:
    """A small NNTP reader over one socket."""

    def __init__(self, port):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=60)
        self.file = self.sock.makefile("rb")
        greeting = self.file.readline()
        assert greeting[:3] in (b"200", b"201"), greeting

    def close(self):
        try:
            self.sock.sendall(b"QUIT\r\n")
        except OSError:
            pass
        self.file.close()
        self.sock.close()

    def command(self, line):
        self.sock.sendall(line.encode("ascii") + b"\r\n")
        return self.file.readline()

    def block(self):
        out = []
        while True:
            line = self.file.readline()
            if not line:
                raise AssertionError("connection closed inside a block")
            if line == b".\r\n":
                return out
            if line.startswith(b".."):
                line = line[1:]
            out.append(line)

    def post(self, payload):
        first = self.command("POST")
        assert first.startswith(b"340"), first
        stuffed = payload.replace(b"\r\n.", b"\r\n..")
        self.sock.sendall(stuffed + b".\r\n")
        second = self.file.readline()
        assert second.startswith(b"240"), second

    def listgroup(self, group):
        status = self.command("LISTGROUP " + group)
        if not status.startswith(b"211"):
            return status, []
        return status, [int(line) for line in self.block()]

    def article_bytes(self, spec):
        status = self.command("ARTICLE " + spec)
        if not status.startswith(b"220"):
            return status, None
        return status, b"".join(self.block())


def without_path_and_xref(octets):
    head, _, body = octets.partition(b"\r\n\r\n")
    kept = [l for l in head.split(b"\r\n")
            if not (l.lower().startswith(b"path:") or l.lower().startswith(b"xref:"))]
    return b"\r\n".join(kept) + b"\r\n\r\n" + body


def chain_step(chain, msgid, octets):
    return blake3_ref.blake3(chain + blake3_ref.blake3(octets)
                             + msgid.encode("ascii"))


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a native launcher")
class NativePeerCatchupTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-catchup-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("FN_CATCHUP_TEST_KILL", None)
        self.processes = []
        self.addCleanup(self.stop_all)
        self.evidence = Path(os.environ.get("FN_CATCHUP_EVIDENCE", self.base / "evidence"))
        self.evidence.mkdir(parents=True, exist_ok=True)
        self.nodes = []
        self.addCleanup(self.keep_logs)

    def keep_logs(self):
        for node in self.nodes:
            for name in ("fn.log", "stderr.log"):
                source = node["root"] / name
                if source.exists():
                    shutil.copyfile(source, self.evidence / "{}-{}-{}".format(
                        self._testMethodName, node["name"], name))

    # ------------------------------------------------------------ nodes

    def command(self, arguments, expected=0):
        result = subprocess.run(list(map(str, arguments)), cwd=ROOT, env=self.env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=180, check=False)
        self.assertEqual(result.returncode, expected, result)
        return result

    def initialize(self, name, identity):
        root = self.base / name
        root.mkdir()
        store, control = root / "store", root / "control.sock"
        port = free_port()
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                store, port, control, root / "fn.log"), encoding="ascii")
        self.command([IMAGE, "--fn", "operator", config, "init", *PROFILE, "fn.test"])
        node = {"name": name, "root": root, "config": config, "port": port,
                "store": store, "log": root / "fn.log"}
        self.nodes.append(node)
        self.command([IMAGE, "--fn", "operator", config, "policy", "set",
                      "path-identity", identity])
        return node

    def catch_up_from(self, node, name, identity, port):
        """NAME is a peer B dials only: inbound fn.*, outbound none; its
        source address is one no socket here uses."""
        self.command([IMAGE, "--fn", "operator", node["config"], "peer", "add",
                      name, identity, "127.0.0.1", str(port), "fn.*", "-",
                      "source-address", "127.0.0.9", "true"])
        self.command([IMAGE, "--fn", "operator", node["config"], "peer", "catch-up",
                      name, INTERVAL])

    def start(self, node, extra_env=None, expect_death=False):
        image = IMAGE
        env = dict(self.env)
        if extra_env:
            if DEVELOPER is None or not os.access(DEVELOPER, os.X_OK):
                self.skipTest("set FN_NATIVE_DEVELOPER_HOST: the FN_CATCHUP_TEST_KILL cuts")
            image = DEVELOPER
            env.update(extra_env)
        err = open(node["root"] / "stderr.log", "ab")
        process = subprocess.Popen(
            [str(image), "--fn", "operator", str(node["config"]), "run"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=err)
        self.processes.append(process)
        node["process"] = process
        wait_for_announcement(process, b"LISTENING ")

    def stop(self, node):
        process = node.pop("process")
        process.terminate()
        process.communicate(timeout=60)
        self.processes.remove(process)

    def stop_all(self):
        for process in self.processes:
            if process.poll() is None:
                process.terminate()
                try:
                    process.communicate(timeout=60)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.communicate(timeout=60)

    def log_lines(self, node):
        try:
            return [l for l in node["log"].read_text(errors="replace").splitlines()
                    if "catch-up peer=" in l]
        except OSError:
            return []

    def await_log(self, node, pattern, timeout=600):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            for line in self.log_lines(node):
                if re.search(pattern, line):
                    return line
            process = node.get("process")
            if process is not None and process.poll() is not None:
                break
            time.sleep(0.5)
        self.fail("{}: no catch-up line matching {!r}; lines: {}; log tail: {}".format(
            node["name"], pattern, self.log_lines(node)[-5:],
            node["log"].read_text(errors="replace")[-2000:] if node["log"].exists() else ""))

    # ------------------------------------------------------------ fixtures

    def populated_a(self):
        a = self.initialize("A", "a.catchup.example.invalid")
        self.start(a)
        client = Client(a["port"])
        try:
            for n in range(COUNT):
                client.post(article(n))
        finally:
            client.close()
        return a

    def articles_of(self, node):
        """{msgid: stored octets} of fn.test, and the numbers in order."""
        client = Client(node["port"])
        try:
            status, numbers = client.listgroup("fn.test")
            self.assertTrue(status.startswith(b"211"), status)
            out = {}
            order = []
            for number in numbers:
                status, octets = client.article_bytes(str(number))
                self.assertTrue(status.startswith(b"220"), status)
                msgid = status.split()[2].decode("ascii")
                self.assertNotIn(msgid, out)
                out[msgid] = octets
                order.append(msgid)
            return out, order
        finally:
            client.close()

    def expected_digest(self, a_articles, a_order):
        chain = bytes(32)
        for msgid in a_order:
            chain = chain_step(chain, msgid, without_xref(a_articles[msgid]))
        return chain.hex()

    def compare(self, a, b):
        a_articles, a_order = self.articles_of(a)
        b_articles, b_order = self.articles_of(b)
        self.assertEqual(len(a_articles), COUNT)
        self.assertEqual(sorted(b_articles), sorted(a_articles))
        # B numbered them in A's log order: catch-up is oldest first.
        self.assertEqual(b_order, a_order)
        for msgid, octets in a_articles.items():
            self.assertEqual(without_path_and_xref(b_articles[msgid]),
                             without_path_and_xref(octets), msgid)
        return a_articles, a_order

    def fncu_frames(self, node):
        data = (node["store"] / "catch-up" / "A.fnfd").read_bytes()
        frames, at = [], 0
        while at + 4 <= len(data):
            size = int.from_bytes(data[at:at + 4], "big")
            frames.append(size)
            at += 4 + size
        self.assertEqual(at, len(data), "a torn FNCU tail")
        return frames

    def witness(self, kind, data, nodes):
        data = dict(data, kind=kind)
        for node in nodes:
            keep = self.evidence / "{}-{}.log".format(kind, node["name"])
            if node["log"].exists():
                shutil.copyfile(node["log"], keep)
            data["log_sha256_" + node["name"]] = sha256_of(node["log"])
        data["image_sha256"] = sha256_of(IMAGE)
        (self.evidence / (kind + ".witness.json")).write_text(
            json.dumps(data, sort_keys=True, indent=1), encoding="utf-8")
        print("NATIVE-CATCHUP-WITNESS " + json.dumps(data, sort_keys=True), flush=True)

    # ------------------------------------------------------------ cases

    def test_catch_up_imports_every_article(self):
        a = self.populated_a()
        b = self.initialize("B", "b.catchup.example.invalid")
        self.catch_up_from(b, "A", "a.catchup.example.invalid", a["port"])
        started = time.monotonic()
        self.start(b)
        done = self.await_log(b, r"catch-up peer=A round=done position={} ".format(COUNT))
        elapsed = time.monotonic() - started
        a_articles, a_order = self.compare(a, b)
        digest = re.search(r"digest=([0-9a-f]{64})", done).group(1)
        self.assertEqual(digest, self.expected_digest(a_articles, a_order))
        first = [l for l in self.log_lines(b) if "round=done" in l][0]
        imported = int(re.search(r"imported=(\d+)", first).group(1))
        self.assertEqual(imported, COUNT, first)
        journals = sorted(str(p.relative_to(b["store"])) for p in
                          (b["store"] / "catch-up").rglob("*") if p.is_file())
        self.stop(b)
        self.stop(a)
        self.witness("catch-up", {"articles": COUNT, "done_line": done,
                                  "seconds_to_done": round(elapsed, 2),
                                  "digest": digest, "journals": journals,
                                  "lines": self.log_lines(b)}, [a, b])
        self.assertTrue(journals, "no FNCU journal under the store's catch-up directory")

    def test_kill_mid_catch_up_resumes(self):
        a = self.populated_a()
        b = self.initialize("B", "b.catchup.example.invalid")
        self.catch_up_from(b, "A", "a.catchup.example.invalid", a["port"])
        self.start(b, extra_env={"FN_CATCHUP_TEST_KILL": "before-write:3"})
        process = b["process"]
        code = process.wait(timeout=600)
        b.pop("process")
        self.processes.remove(process)
        self.assertEqual(code, -signal.SIGKILL,
                         "B was to die at the third FNCU append; log: {}".format(
                             b["log"].read_text(errors="replace")[-2000:]))
        # The cut's own line goes to the owner's log queue, which a SIGKILL
        # may not let drain; the journal is the evidence: two FNCU cursor
        # frames (four-octet length, then the frame), the third never written.
        frames = self.fncu_frames(b)
        self.assertEqual(len(frames), 2, frames)
        killed_lines = self.log_lines(b)
        self.start(b)
        done = self.await_log(b, r"catch-up peer=A round=done position={} ".format(COUNT))
        a_articles, a_order = self.compare(a, b)
        digest = re.search(r"digest=([0-9a-f]{64})", done).group(1)
        self.assertEqual(digest, self.expected_digest(a_articles, a_order))
        duplicate = int(re.search(r"duplicate=(\d+)", done).group(1))
        imported = int(re.search(r"imported=(\d+)", done).group(1))
        # The third batch was committed before the cut and offered again.
        self.assertGreater(duplicate, 0, done)
        self.assertLess(imported + duplicate, COUNT, done)
        self.stop(b)
        self.stop(a)
        self.witness("catch-up-kill", {"articles": COUNT, "done_line": done,
                                       "before_kill": killed_lines,
                                       "frames_at_the_cut": frames,
                                       "lines": self.log_lines(b)}, [a, b])


def without_xref(octets):
    head, _, body = octets.partition(b"\r\n\r\n")
    kept = [l for l in head.split(b"\r\n") if not l.lower().startswith(b"xref:")]
    return b"\r\n".join(kept) + b"\r\n\r\n" + body


if __name__ == "__main__":
    unittest.main()

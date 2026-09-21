"""Opt-in two-node native ingress/outbound-feed composition witness.

Python is the external harness and pre-start configuration tool.  Both running
nodes are the production saved image through its public operator entry; no
Python service or feed process participates after startup.
"""

import hashlib
import os
from pathlib import Path
import socket
import struct
import subprocess
import tempfile
import time
import unittest

from tests.native_process import wait_for_announcement


ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
CORE = Path(str(IMAGE) + ".core") if IMAGE is not None else None
SOURCE = os.environ.get("FN_NATIVE_IMAGE_SOURCE_SHA")
LAUNCHER_SHA256 = os.environ.get("FN_NATIVE_LAUNCHER_SHA256")
CORE_SHA256 = os.environ.get("FN_NATIVE_CORE_SHA256")


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


ACTUAL_LAUNCHER = digest(IMAGE) if IMAGE is not None and IMAGE.is_file() else None
ACTUAL_CORE = digest(CORE) if CORE is not None and CORE.is_file() else None
READY = bool(
    IMAGE_TEXT and IMAGE is not None and CORE is not None
    and IMAGE.is_file() and os.access(IMAGE, os.X_OK) and CORE.is_file()
    and SOURCE and LAUNCHER_SHA256 == ACTUAL_LAUNCHER
    and CORE_SHA256 == ACTUAL_CORE)


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(
    READY,
    "set explicit native image/source and matching launcher/core SHA-256 values",
)
class NativePeeringTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        print("native-peering launcher-sha256={} core-sha256={} declared-source={}".format(
            ACTUAL_LAUNCHER, ACTUAL_CORE, SOURCE))

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-peering-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.processes = []
        self.addCleanup(self.stop_all)

    def command(self, arguments, expected=0, timeout=180):
        result = subprocess.run(
            list(map(str, arguments)), cwd=ROOT, env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=timeout, check=False)
        self.assertEqual(result.returncode, expected,
                         "command {} returned {}\nstdout={}\nstderr={}".format(
                             arguments, result.returncode,
                             result.stdout.decode("utf-8", "replace"),
                             result.stderr.decode("utf-8", "replace")))
        return result

    def initialize(self, name, port):
        root = self.base / name
        store = root / "store"
        control = root / "control.sock"
        root.mkdir()
        self.command([IMAGE, "--fn", "store", store, "init", "fn.test"])
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(store, port, control),
            encoding="ascii")
        return {"name": name, "root": root, "store": store,
                "control": control, "config": config, "port": port}

    def configure_peer(self, source, target, outbound="fn.*"):
        self.command([
            IMAGE, "--fn", "operator", source["config"], "peer", "add",
            target["name"], "{}.example.invalid".format(target["name"]),
            "127.0.0.1", str(target["port"]), "fn.*", outbound,
            "127.0.0.1", "true",
        ])

    def start(self, node):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.processes.append(process)
        node["process"] = process
        line = wait_for_announcement(process, b"LISTENING ")
        self.assertEqual(line, "LISTENING {}\n".format(node["port"]).encode(),
                         "{} emitted an unexpected readiness line: {!r}".format(
                             node["name"], line))

    def stop_all(self):
        for process in self.processes:
            if process.poll() is None:
                process.terminate()
        for process in self.processes:
            if process.poll() is None:
                process.wait(timeout=30)
            if process.stdout:
                process.stdout.close()
            if process.stderr:
                process.stderr.close()
        self.processes = []

    @staticmethod
    def article(message_id, marker):
        return ("From: sender@example.invalid\r\n"
                "Newsgroups: fn.test\r\n"
                "Subject: native two-node {}\r\n"
                "Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n"
                "Message-ID: {}\r\n\r\n{}\r\n".format(
                    marker, message_id, marker)).encode("ascii")

    def post(self, node, message_id, marker):
        payload = node["root"] / (marker + ".article")
        payload.write_bytes(self.article(message_id, marker))
        self.command([IMAGE, "--fn", "operator", node["config"], "post",
                      "--message-id", message_id, "--payload", payload,
                      "--group", "fn.test"])

    def article_from(self, node, message_id):
        try:
            client = socket.create_connection(("127.0.0.1", node["port"]), timeout=10)
        except ConnectionRefusedError:
            process = node.get("process")
            if process is not None and process.poll() is not None:
                self.fail("{} exited while awaiting article: {}".format(
                    node["name"], process.stderr.read().decode("utf-8", "replace")))
            return None
        with client:
            stream = client.makefile("rwb", buffering=0)
            if not stream.readline().startswith(b"200 "):
                return None
            stream.write(b"ARTICLE " + message_id.encode("ascii") + b"\r\n")
            if not stream.readline().startswith(b"220 "):
                return None
            article = bytearray()
            while True:
                line = stream.readline()
                if line == b".\r\n":
                    return bytes(article)
                if not line:
                    return None
                article.extend(line[1:] if line.startswith(b"..") else line)

    def await_article(self, node, message_id, timeout=60):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            article = self.article_from(node, message_id)
            if article is not None:
                return article
            time.sleep(0.1)
        self.fail("{} did not receive {}".format(node["name"], message_id))

    def duplicate_offer(self, node, message_id):
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=10) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"IHAVE " + message_id.encode("ascii") + b"\r\n")
            return stream.readline()

    def transfer_then_reset_before_reply(self, node, message_id, marker):
        client = socket.create_connection(("127.0.0.1", node["port"]), timeout=10)
        greeting = bytearray()
        while not greeting.endswith(b"\n"):
            chunk = client.recv(1)
            self.assertTrue(chunk)
            greeting.extend(chunk)
        self.assertTrue(greeting.startswith(b"200 "))
        payload = self.article(message_id, marker).replace(b"\r\n.\r\n", b"\r\n..\r\n")
        client.sendall(b"TAKETHIS " + message_id.encode("ascii") + b"\r\n"
                       + payload + b".\r\n")
        # Force a reset while the owner is completing the accepted article.
        # A reply write may fail, but that connection-local failure must not
        # be reclassified as an ambiguous Store outcome or stop the owner.
        client.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER,
                          struct.pack("ii", 1, 0))
        client.close()

    def capabilities(self, node):
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=10) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"CAPABILITIES\r\n")
            self.assertTrue(stream.readline().startswith(b"101 "))
            lines = []
            while True:
                line = stream.readline()
                if line == b".\r\n":
                    break
                self.assertNotEqual(line, b"")
                lines.append(line.rstrip(b"\r\n"))
            # Keep this on one connection: it detects a worker that returns
            # after every successful read instead of only after QUIT/close.
            stream.write(b"QUIT\r\n")
            self.assertTrue(stream.readline().startswith(b"205 "))
            return lines

    def test_public_native_nodes_exchange_both_ways_and_suppress_duplicate(self):
        a = self.initialize("a", free_port())
        b = self.initialize("b", free_port())
        self.configure_peer(a, b)
        self.configure_peer(b, a)
        self.start(a)
        self.start(b)
        self.assertIn(b"IHAVE", self.capabilities(a))
        self.assertIn(b"STREAMING", self.capabilities(a))
        self.assertIn(b"IHAVE", self.capabilities(b))
        self.assertIn(b"STREAMING", self.capabilities(b))

        a_id = "<native-a-to-b@example.invalid>"
        self.post(a, a_id, "a-to-b")
        a_source = self.await_article(a, a_id)
        b_article = self.await_article(b, a_id)
        self.assertEqual(b_article, a_source)
        self.assertTrue(self.duplicate_offer(b, a_id).startswith(b"435 "))

        b_id = "<native-b-to-a@example.invalid>"
        self.post(b, b_id, "b-to-a")
        b_source = self.await_article(b, b_id)
        a_article = self.await_article(a, b_id)
        self.assertEqual(a_article, b_source)
        self.assertTrue(self.duplicate_offer(a, b_id).startswith(b"435 "))


    def test_durable_feed_requeues_after_source_process_death(self):
        a = self.initialize("restart-a", free_port())
        b = self.initialize("restart-b", free_port())
        self.configure_peer(a, b)
        self.configure_peer(b, a, outbound="-")
        self.start(a)

        message_id = "<native-requeue-after-kill@example.invalid>"
        self.post(a, message_id, "requeue-after-kill")
        journal = a["store"] / "feed" / "restart-b.fnfd"
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline and not journal.is_file():
            time.sleep(0.05)
        self.assertTrue(journal.is_file(), "accepted post has no durable FNFD intent")

        source = self.processes.pop(0)
        source.kill()
        source.wait(timeout=30)
        source.stdout.close()
        source.stderr.close()

        self.start(b)
        self.start(a)
        source_article = self.await_article(a, message_id)
        target_article = self.await_article(b, message_id)
        self.assertEqual(target_article, source_article)
        self.assertTrue(self.duplicate_offer(b, message_id).startswith(b"435 "))

    def test_reset_while_transit_completes_keeps_durable_article_and_owner(self):
        source = self.initialize("reset-source", free_port())
        target = self.initialize("reset-target", free_port())
        self.configure_peer(target, source, outbound="-")
        self.start(target)

        message_id = "<native-reset-after-transit@example.invalid>"
        self.transfer_then_reset_before_reply(target, message_id, "reset-after-transit")
        self.assertEqual(self.await_article(target, message_id),
                         self.article(message_id, "reset-after-transit"))
        self.assertIsNone(target["process"].poll(),
                          "connection-local reply failure stopped the owner")
        self.assertIn(b"IHAVE", self.capabilities(target))

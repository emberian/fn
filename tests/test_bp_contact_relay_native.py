"""Two real native BP processes through a byte-only interruptible relay."""

import os
from pathlib import Path
import select
import shutil
import socket
import subprocess
import tempfile
import threading
import time
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement

# specs/host.md "BP run classes" (books/bp-run-class.lisp, PRF-131): a
# connection lost after it existed is exit 6 (connection-local: the job stays
# and is re-offered; no recovery); exit 3 stays the fence.
LOST = 6



ROOT = Path(__file__).resolve().parent.parent
DEFAULT_IMAGE = ROOT / "build" / "fn-host-dtn"


class ByteRelay:
    """Forward bytes without inspecting or answering any protocol message."""

    def __init__(self):
        self.listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(4)
        self.listener.settimeout(0.2)
        self.port = self.listener.getsockname()[1]
        self.target = None
        self.cut_next = False
        self.cut_after = None
        self.stopped = threading.Event()
        self.workers = []
        self.thread = threading.Thread(target=self._accept, daemon=True)
        self.thread.start()

    def route(self, port, cut_next=False, cut_after=None):
        self.target = port
        self.cut_next = cut_next
        # Forward both ways, but sever both sides once the client has sent
        # CUT_AFTER octets: a transfer that started and never finished.
        self.cut_after = cut_after

    def _accept(self):
        while not self.stopped.is_set():
            try:
                client, _ = self.listener.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            target, cut, limit = self.target, self.cut_next, self.cut_after
            self.cut_next = False
            worker = threading.Thread(
                target=self._exchange, args=(client, target, cut, limit),
                daemon=True
            )
            self.workers.append(worker)
            worker.start()

    @staticmethod
    def _exchange(client, target, cut, limit=None):
        with client:
            if target is None:
                return
            try:
                upstream = socket.create_connection(("127.0.0.1", target), 5)
            except OSError:
                return
            with upstream:
                if cut:
                    # Deliver one real transport byte, then sever both sides.
                    # The relay never fabricates TCPCL or BP success.
                    client.settimeout(5)
                    try:
                        first = client.recv(1)
                        if first:
                            upstream.sendall(first)
                    except OSError:
                        pass
                    return
                sockets = (client, upstream)
                forwarded = 0
                for connection in sockets:
                    connection.setblocking(False)
                deadline = time.monotonic() + 35
                while time.monotonic() < deadline:
                    readable, _, _ = select.select(sockets, (), (), 0.2)
                    for source in readable:
                        try:
                            data = source.recv(65536)
                        except OSError:
                            return
                        if not data:
                            return
                        destination = upstream if source is client else client
                        if limit is not None and source is client:
                            if forwarded + len(data) >= limit:
                                try:
                                    destination.sendall(data[:limit - forwarded])
                                except OSError:
                                    pass
                                return
                            forwarded += len(data)
                        try:
                            destination.sendall(data)
                        except OSError:
                            return

    def close(self):
        self.stopped.set()
        self.listener.close()
        self.thread.join(timeout=2)
        for worker in self.workers:
            worker.join(timeout=2)


class NativeBpContactRelayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sender_image = Path(os.environ.get("FN_NATIVE_CONTACT_SENDER", DEFAULT_IMAGE))
        cls.receiver_image = Path(os.environ.get("FN_NATIVE_CONTACT_RECEIVER", DEFAULT_IMAGE))
        if not all(os.access(path, os.X_OK)
                   for path in (cls.sender_image, cls.receiver_image)):
            raise unittest.SkipTest("two native DTN image paths are required")
        # The receiver is the node, `bp-node serve`, which admits a TCPCL
        # principal from the store's observed-channel profile (`operator
        # bp-boundary add`) under the store's path identity.  The DTN image
        # carries the node and the operator; FN_NATIVE_CONTACT_RECEIVER is it.
        cls.trusted_image = cls.receiver_image

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-contact-relay-"))
        self.addCleanup(shutil.rmtree, self.tmp)
        self.sender_journal = self.tmp / "sender"
        self.receiver_journal = self.tmp / "receiver"
        self.adu = self.tmp / "request.adu"
        self.adu.write_bytes(b"interrupted contact custody witness")
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.relay = ByteRelay()
        self.addCleanup(self.relay.close)

    def invoke(self, image, *args):
        return subprocess.run(
            [str(image), "--fn", *map(str, args)], cwd=ROOT, env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=90,
            check=False,
        )

    def trust_receiver(self):
        """Store, path identity and the sender's boundary, before any contact."""
        self.receiver_store = self.tmp / "receiver-store"
        self.receiver_config = self.tmp / "receiver-fn.toml"
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as reservation:
            reservation.bind(("127.0.0.1", 0))
            self.receiver_port = reservation.getsockname()[1]
        steps = (
            ("store", self.receiver_store, "init", "fn.test"),
            ("operator", self.receiver_config, "policy", "set",
             "path-identity", "receiver.bp.gate.invalid"),
            ("operator", self.receiver_config, "bp-boundary", "add",
             "sender-boundary", "sender.bp.gate.invalid", "dtn://sender/",
             self.receiver_port, "fn.test", "32768", "16"),
        )
        self.receiver_config.write_text(
            f'[store]\npath = "{self.receiver_store}"\n', encoding="ascii")
        for step in steps:
            done = self.invoke(self.trusted_image, *step)
            self.assertEqual(done.returncode, 0, (step, done.stdout, done.stderr))

    def receive_once(self):
        if not hasattr(self, "receiver_port"):
            self.trust_receiver()
        process = subprocess.Popen(
            [str(self.trusted_image), "--fn", "bp-node", "serve",
             str(self.receiver_port), str(self.receiver_journal),
             str(self.receiver_store), str(self.tmp / "receiver-fnrj"),
             str(self.tmp / "receiver-fnwf"), "dtn://receiver/",
             "dtn://sender/", "dtn://receiver/", "native-policy",
             "dtn://receiver/", "127.0.0.1", str(self.relay.port), "1",
             "3600000", "2", "32", "1048576", "0", "0"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0,
        )
        line = wait_for_announcement(process, b"BP NODE LISTENING ", timeout=45)
        return process, int(line.rsplit(b" ", 1)[1])

    def service_run(self, work, journal=None, lifetime=3600000):
        return self.invoke(
            self.sender_image, "bp-service", "run", "127.0.0.1",
            self.relay.port, self.adu, journal or self.sender_journal,
            "dtn://sender/", "dtn://receiver/", work, work + "-attempt", 0,
            lifetime, 2, 32, 1048576, 0, 0,
        )

    def tick(self, start_delay, end_delay, wall=0, journal=None,
             lifetime=3600000):
        return self.invoke(
            self.sender_image, "bp-contact", "tick",
            journal or self.sender_journal,
            "dtn://sender/", "dtn://receiver/", start_delay, end_delay,
            lifetime, 2, 32, 1048576, wall, 0,
        )

    def test_interrupted_contact_receiver_restart_then_expiry(self):
        first, first_port = self.receive_once()
        self.relay.route(first_port, cut_next=True)
        try:
            interrupted = self.service_run("work-interrupted")
            self.assertEqual(interrupted.returncode, LOST, interrupted.stderr)
            self.assertIn(b"BP queue accepted", interrupted.stdout)
            self.assertIn(b"reason=uncertain", interrupted.stdout)
            try:
                first.wait(timeout=15)
            except subprocess.TimeoutExpired:
                first.terminate()
                first.wait(timeout=10)
        finally:
            if first.poll() is None:
                first.kill()
                first.wait(timeout=10)
            first.stdout.close()
            first.stderr.close()

        restarted, restarted_port = self.receive_once()
        self.relay.route(restarted_port)
        try:
            closed = self.tick(1, 60000)
            self.assertEqual(closed.returncode, 0, closed.stderr)
            self.assertIn(b"BP contact closed", closed.stdout)
            self.assertIsNone(restarted.poll(), "closed window sent no transfer")

            delivered = self.tick(0, 60000)
            received_out, received_err = restarted.communicate(timeout=90)
            self.assertEqual(delivered.returncode, 0, delivered.stderr)
            self.assertIn(b"BP contact open", delivered.stdout)
            self.assertEqual(restarted.returncode, 0, received_err)
            self.assertIn(b"BP accepted", received_out)
        finally:
            if restarted.poll() is None:
                restarted.kill()
                restarted.wait(timeout=10)
            restarted.stdout.close()
            restarted.stderr.close()

        held = tuple((self.receiver_journal / "lifecycle").glob("*.fnb"))
        self.assertTrue(held, "receiver custody must have a durable FNBS row")

        # A queued job carries the age anchor of its Bundle Age block
        # (`fn-bpn-anchor-of`: age 0 at the CLOCK_BOOTTIME reading of the
        # enqueue), and `fn-clock-expiry-decision` ages an anchored bundle by
        # that clock alone (RFC 9171 section 4.2.6, 4.4.2); no wall reading
        # can expire it.  So expiry is observed by elapsed time: a separate
        # sender journal whose bundles live 1000 ms, and a tick after 1500 ms.
        self.relay.route(None)
        expiring = self.tmp / "sender-expiring"
        second = self.service_run("work-to-expire", journal=expiring,
                                  lifetime=1000)
        self.assertEqual(second.returncode, LOST, second.stderr)
        before = len(tuple((expiring / "lifecycle").glob("*.fnb")))
        time.sleep(1.5)
        expired = self.tick(1, 60000, journal=expiring, lifetime=1000)
        self.assertEqual(expired.returncode, 0, expired.stderr)
        self.assertIn(b"BP contact closed", expired.stdout)
        self.assertIn(b"status=expired", expired.stdout)
        after = len(tuple((expiring / "lifecycle").glob("*.fnb")))
        self.assertGreater(after, before)


if __name__ == "__main__":
    unittest.main()

"""External process-cut plumbing; native durability remains the image test."""
import os
from pathlib import Path
import signal
import socket
import sys
import tempfile
import threading
import time
import unittest

from tests.consumer_reply_hold import ConsumerReplyHold
from tests.native_harness import ROOT, start


class ConsumerProcessCutsTests(unittest.TestCase):
    def test_reply_hold_forwards_request_but_discards_answer(self):
        with tempfile.TemporaryDirectory(prefix="fn-cut-") as temporary:
            root = Path(temporary)
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as server:
                server.bind(str(root / "owner"))
                server.listen(1)
                received = []

                def owner():
                    with server.accept()[0] as connection:
                        received.append(connection.recv(1024))
                        connection.sendall(b"opaque reply")

                thread = threading.Thread(target=owner)
                thread.start()
                proxy = ConsumerReplyHold(root / "proxy", root / "owner")
                self.addCleanup(proxy.close)
                with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
                    client.connect(proxy.path)
                    client.sendall(b"opaque request")
                    self.assertTrue(proxy.reply_received.wait(3), proxy.error)
                    client.settimeout(0.05)
                    with self.assertRaises(socket.timeout):
                        client.recv(1024)
                    proxy.close()
                    self.assertEqual(client.recv(1024), b"")
                thread.join(timeout=3)
                self.assertFalse(thread.is_alive())
                self.assertEqual(received, [b"opaque request"])

    def test_application_cut_allows_external_sigkill(self):
        env = dict(os.environ, FN_CONSUMER_CUT="after-commit",
                   FN_CONSUMER_CUT_ACTION="stop")
        process = start([sys.executable, "-c",
                         "from tools.fn_consumer import cut; cut('after-commit'); "
                         "print('must not continue')"], cwd=ROOT, env=env)
        self.addCleanup(process.stop, 1)
        deadline = time.monotonic() + 5
        while b"CONSUMER-CUT after-commit" not in process.stderr.since(0):
            if process.poll() is not None or time.monotonic() >= deadline:
                self.fail("cut announcement missing")
            time.sleep(0.01)
        self.assertIsNone(process.poll())
        process.kill()
        stdout, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, -signal.SIGKILL)
        self.assertEqual(stdout, b"")


if __name__ == "__main__":
    unittest.main()

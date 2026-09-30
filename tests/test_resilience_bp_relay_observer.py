"""Actual loopback byte relay facts; no native fn image verdict."""
import socket
import threading
import unittest
from tests.test_bp_contact_relay_native import ByteRelay


class RelayObserverTests(unittest.TestCase):
    def test_callback_requires_actual_limit_sever(self):
        listener = socket.socket()
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        listener.settimeout(3)
        relay = ByteRelay()
        observed, received = [], []
        done = threading.Event()

        def upstream():
            connection, _ = listener.accept()
            with connection:
                while True:
                    data = connection.recv(100)
                    if not data:
                        break
                    received.append(data)

        worker = threading.Thread(target=upstream)
        worker.start()
        try:
            def observe(**fields):
                observed.append(fields)
                done.set()
            relay.route(listener.getsockname()[1], cut_after=4, observer=observe)
            self.assertFalse(done.is_set(), "configuration alone is not a fault observation")
            with socket.create_connection(("127.0.0.1", relay.port), 3) as client:
                client.sendall(b"abcdefgh")
                self.assertTrue(done.wait(3))
            worker.join(3)
            self.assertFalse(worker.is_alive())
            self.assertEqual(b"".join(received), b"abcd")
            self.assertEqual(observed, [dict(event="byte-limit-severed", forwarded=4,
                                             send_succeeded=True, limit=4)])
        finally:
            relay.close()
            listener.close()
            worker.join(3)

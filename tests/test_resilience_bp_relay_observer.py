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
        callback_release = threading.Event()

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
                done.set()
                callback_release.wait(3)
                observed.append(fields)
            completed = relay.route(listener.getsockname()[1], cut_after=4, observer=observe)
            self.assertFalse(done.is_set(), "configuration alone is not a fault observation")
            with socket.create_connection(("127.0.0.1", relay.port), 3) as client:
                client.sendall(b"abcdefgh")
                self.assertTrue(done.wait(3))
                client.settimeout(3)
                self.assertEqual(client.recv(1), b"", "peer finished before callback completed")
                self.assertFalse(completed.is_set())
                replacement = relay.route(None)
                callback_release.set()
                self.assertTrue(completed.wait(3))
                self.assertFalse(replacement.is_set(), "old exchange cannot complete new route")
            worker.join(3)
            self.assertFalse(worker.is_alive())
            self.assertEqual(b"".join(received), b"abcd")
            self.assertEqual(observed, [dict(event="byte-limit-severed", forwarded=4,
                                             send_succeeded=True, limit=4)])
        finally:
            callback_release.set()
            relay.close()
            listener.close()
            worker.join(3)

    def test_atomic_route_snapshot_and_once_only_cut(self):
        relay = ByteRelay()
        stop = threading.Event()
        errors = []
        callbacks = [object(), object()]
        def publish():
            for i in range(1000):
                relay.route(i % 2, cut_next=True, cut_after=i % 2 + 10,
                            observer=callbacks[i % 2])
            stop.set()
        worker = threading.Thread(target=publish)
        worker.start()
        try:
            while not stop.is_set():
                target, cut, limit, observer, completed = relay._snapshot_route()
                if target is not None and (limit != target + 10 or observer is not callbacks[target]):
                    errors.append((target, limit, observer))
            worker.join(3)
            self.assertEqual(errors, [])
            relay.route(1, cut_next=True, cut_after=11, observer=callbacks[1])
            self.assertTrue(relay._snapshot_route()[1])
            self.assertFalse(relay._snapshot_route()[1])
        finally:
            relay.close()
            worker.join(3)

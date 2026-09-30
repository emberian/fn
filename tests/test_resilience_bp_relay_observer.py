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

    def test_drain_waits_for_second_exchange_callback(self):
        listener = socket.socket()
        listener.bind(("127.0.0.1", 0))
        listener.listen(2)
        listener.settimeout(3)
        relay = ByteRelay()
        first_done, second_entered, release_second = (threading.Event() for _ in range(3))
        drained = threading.Event()
        observations, received = [], []
        callback_lock = threading.Lock()
        callback_count = [0]
        results = []

        def upstream():
            for _ in range(2):
                connection, _ = listener.accept()
                with connection:
                    data = b""
                    while True:
                        chunk = connection.recv(100)
                        if not chunk:
                            break
                        data += chunk
                    received.append(data)

        def observe(**fields):
            with callback_lock:
                callback_count[0] += 1
                number = callback_count[0]
            if number == 2:
                second_entered.set()
                release_second.wait(3)
            observations.append(fields)
            if number == 1:
                first_done.set()

        server = threading.Thread(target=upstream)
        server.start()
        handle = relay.route(listener.getsockname()[1], cut_after=4, observer=observe)
        def drain():
            results.append(relay.drain(handle, 3))
            drained.set()
        drain_thread = threading.Thread(target=drain)
        try:
            for index in range(2):
                with socket.create_connection(("127.0.0.1", relay.port), 3) as client:
                    client.settimeout(3)
                    client.sendall(b"abcdefgh")
                    self.assertEqual(client.recv(1), b"")
                self.assertTrue((first_done if index == 0 else second_entered).wait(3))
            self.assertTrue(handle.is_set(), "first exchange already completed")
            drain_thread.start()
            self.assertFalse(drained.wait(0.05), "first completion must not seal second callback")
            self.assertEqual(len(observations), 1)
            release_second.set()
            self.assertTrue(drained.wait(3))
            self.assertEqual(results, [True])
            self.assertEqual(len(observations), 2)
            server.join(3)
            self.assertEqual(received, [b"abcd", b"abcd"])
        finally:
            release_second.set()
            if drain_thread.ident is not None:
                drain_thread.join(3)
            relay.close()
            listener.close()
            server.join(3)

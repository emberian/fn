"""Focused controls for the native WAIT-to-APPEND observation join."""
import importlib.util
import os
from pathlib import Path
import selectors
import tempfile
from types import SimpleNamespace
import unittest

SPEC = importlib.util.spec_from_file_location(
    "cursor_restart", Path(__file__).with_name("native-consumer-cursor-restart.py"))
cursor = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cursor)


class WaitJoin(unittest.TestCase):
    def setUp(self):
        reader, writer = os.pipe()
        self.writer = os.fdopen(writer, "wb", buffering=0)
        stdout = os.fdopen(reader, "rb", buffering=0)
        self.node = cursor.fixture.restart.Node.__new__(cursor.fixture.restart.Node)
        self.node.proc = SimpleNamespace(stdout=stdout)
        self.node.pending = b""
        self.node.log = tempfile.NamedTemporaryFile()
        self.node.selector = selectors.DefaultSelector()
        self.node.selector.register(stdout, selectors.EVENT_READ)
        for resource in (stdout, self.writer, self.node.log, self.node.selector):
            self.addCleanup(resource.close)
        self.waiting = SimpleNamespace(pid=101, returncode=None, poll=lambda: None)
        self.appended = []

    def append(self):
        self.appended.append(True)
        return "receipt"

    def join(self):
        return cursor.append_after_parked_wait(
            self.node, self.waiting, self.append, park_timeout=0.03)

    def test_pending_client_without_park_cannot_start_append(self):
        with self.assertRaisesRegex(AssertionError, "no .*WAIT-PARKED"):
            self.join()
        self.assertEqual(self.appended, [])

    def test_park_for_other_client_or_request_cannot_start_append(self):
        self.writer.write(b"WAIT-PARKED 102 2 14 1 33 1 8\n")
        self.writer.write(b"WAIT-PARKED 101 1 14 1 33 1 8\n")
        with self.assertRaisesRegex(AssertionError, "no .*WAIT-PARKED"):
            self.join()
        self.assertEqual(self.appended, [])

    def test_matching_park_joins_before_append(self):
        self.writer.write(b"WAIT-PARKED 101 1 14 1 33 1 8\n")
        self.writer.write(b"WAIT-PARKED 101 2 14 1 33 2 8\n")
        self.assertEqual(self.join(), "receipt")
        self.assertEqual(self.appended, [True])

    def test_wait_already_returned_cannot_start_append(self):
        self.waiting.poll = lambda: 0
        self.writer.write(b"WAIT-PARKED 101 2 14 1 33 2 8\n")
        with self.assertRaisesRegex(AssertionError, "WAIT ended before APPEND"):
            self.join()
        self.assertEqual(self.appended, [])


if __name__ == "__main__":
    unittest.main()

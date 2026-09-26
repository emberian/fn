"""tools/acl2_slots.py: a bounded wait refuses naming the holders (PKT-346).

Every case uses a private slot directory (FN_ACL2_SLOT_DIR) and a pool of
one or two, and holds slots from a child process so the flocks are real.
"""
from __future__ import annotations

import os
import pathlib
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import acl2_slots  # noqa: E402

HOLDER = r'''
import os, sys, time
sys.path.insert(0, sys.argv[1])
import acl2_slots
with acl2_slots.slot(sys.argv[2]):
    print("HELD", flush=True)
    time.sleep(60)
'''


class SlotWaitTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.env = {"FN_ACL2_SLOT_DIR": self.tmp.name, "FN_ACL2_SLOTS": "2"}
        self.children = []

    def tearDown(self):
        for child in self.children:
            child.kill()
            child.wait(timeout=5)
        self.tmp.cleanup()

    def hold(self, label):
        child = subprocess.Popen(
            [sys.executable, "-c", HOLDER, str(ROOT / "tools"), label],
            env={**os.environ, **self.env}, stdout=subprocess.PIPE, text=True)
        self.children.append(child)
        self.assertEqual(child.stdout.readline().strip(), "HELD")
        return child

    def test_holders_names_only_held_slots(self):
        first = self.hold("proof-repl peer-keys-repl")
        with mock.patch.dict(os.environ, self.env):
            with acl2_slots.slot("mine"):
                pass  # slot-001 now holds a stale "PID mine" line, released
            named = acl2_slots.holders()
        self.assertEqual(named, [f"slot-000: {first.pid} proof-repl peer-keys-repl"])

    def test_a_bounded_wait_refuses_naming_every_holder(self):
        first = self.hold("proof-repl a")
        second = self.hold("certify books/b")
        with mock.patch.dict(os.environ, self.env):
            started = time.monotonic()
            with self.assertRaises(acl2_slots.SlotWaitExpired) as refusal:
                with acl2_slots.slot("waiter", wait_seconds=0.3):
                    self.fail("acquired a slot of a full pool")
            self.assertLess(time.monotonic() - started, 5)
        message = str(refusal.exception)
        self.assertIn(f"slot-000: {first.pid} proof-repl a", message)
        self.assertIn(f"slot-001: {second.pid} certify books/b", message)
        self.assertIn("within 0.3s (waiter)", message)

    def test_the_environment_bounds_the_wait_and_the_minute_line_names_holders(self):
        first = self.hold("proof-repl sccr")
        lines = []
        with mock.patch.dict(os.environ, {**self.env, "FN_ACL2_SLOTS": "1",
                                          "FN_ACL2_SLOT_WAIT": "0.4"}):
            with self.assertRaises(acl2_slots.SlotWaitExpired):
                with acl2_slots.slot("waiter", log=lines.append, report_every=0.1):
                    pass
        self.assertTrue(lines)
        self.assertIn(f"holders: slot-000: {first.pid} proof-repl sccr", lines[0])

    def test_unset_wait_is_unbounded_and_a_freed_slot_is_taken(self):
        first = self.hold("x")
        with mock.patch.dict(os.environ, {**self.env, "FN_ACL2_SLOTS": "1"}):
            os.environ.pop("FN_ACL2_SLOT_WAIT", None)
            self.assertIsNone(acl2_slots.configured_wait())
            killer = __import__("threading").Timer(0.5, first.kill)
            killer.start()
            with acl2_slots.slot("waiter") as held:
                self.assertEqual(held.index, 0)
                self.assertGreater(held.seconds, 0.3)
            killer.join()

    def test_the_wrapper_exits_75_naming_the_holder(self):
        first = self.hold("proof-repl orphan")
        fake = pathlib.Path(self.tmp.name) / "fake-acl2"
        fake.write_text("#!/bin/sh\nexit 0\n")
        fake.chmod(0o755)
        answer = subprocess.run(
            [sys.executable, str(ROOT / "tools" / "acl2"), "--wait-seconds", "0.3"],
            env={**os.environ, **self.env, "FN_ACL2_SLOTS": "1", "FN_ACL2": str(fake)},
            capture_output=True, text=True, timeout=30)
        self.assertEqual(answer.returncode, 75, answer.stderr)
        self.assertIn(f"slot-000: {first.pid} proof-repl orphan", answer.stderr)


if __name__ == "__main__":
    unittest.main()

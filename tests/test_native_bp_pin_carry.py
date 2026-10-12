"""Saved developer core probe; seat must rebuild Part A/B first.

FN_NATIVE_DEVELOPER_HOST=build/fn-host-developer timeout 90 python3 -m unittest -v \
    tests.test_native_bp_pin_carry
No sockets or running node. This probes compiled entries, not disk durability.
"""
import re
import subprocess
import unittest
from tests.test_native_entry_guard import IMAGE, ROOT, image_command


class NativeBpPinCarryTests(unittest.TestCase):
    def test_carry_lineages_zero_scans_and_rebuilds(self):
        self.assertTrue(IMAGE.is_file(), "rebuild developer image; this check must not SKIP")
        argv, env = image_command([
            '(in-package "ACL2")',
            '(load "tests/native_bp_pin_carry.lisp")',
        ])
        result = subprocess.run(argv, env=env, cwd=ROOT, capture_output=True,
                                text=True, timeout=75, check=False)
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output[-12000:])
        counts = {name: tuple(map(int, (scans, builds, queries)))
                  for name, scans, builds, queries in re.findall(
                      r"PIN-COUNTS ([a-z-]+) scans=(\d+) builds=(\d+) queries=(\d+)", output)}
        self.assertGreater(counts["cold"][0], 0)
        self.assertGreater(counts["cold"][1], 0)
        for phase in ("first-ion-after-install", "owner-alternating",
                      "sync-forward", "standalone-gate"):
            self.assertEqual(counts[phase][:2], (0, 0), (phase, counts))
            self.assertGreater(counts[phase][2], 0, (phase, counts))
        self.assertGreater(counts["replay-distinct-release"][0], 0)
        print("BP pin (scans, builds, queries):", counts)
        self.assertIn("PASS BP pin carry lineage", output)

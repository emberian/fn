"""tools/reach_check.py: the orphan it reports must be a real orphan.

A gate that cries wolf gets switched off.  These tests pin the two things
that would make this one lie: a function the host demonstrably calls must
never be reported unreachable, and a function named nowhere outside the
books must never be reported hosted.
"""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import reach_check                                            # noqa: E402


class GraphTests(unittest.TestCase):
    """The call graph, against functions whose status is not in doubt."""

    @classmethod
    def setUpClass(cls):
        cls.graph = reach_check.Graph()

    def test_the_served_read_path_is_reachable(self):
        """host/owner-host.lisp fn-owner-chunk calls fn-own-read, which runs
        fn-served-step, which dispatches to fn-peer-command."""
        for name in ("fn-own-read", "fn-served-step", "fn-peer-command",
                     "fn-peer-decide-offer"):
            self.assertIn(name, self.graph.reachable,
                          f"{name} is on the served path and must be reachable")

    def test_a_function_named_nowhere_outside_books_is_not_reachable(self):
        """The control. fn-transfer-* has no adapter on this tree; if this
        starts failing, either transfer got hosted (good, rebaseline) or the
        graph has started reaching through something it should not."""
        named = subprocess.run(
            ["grep", "-rl", "fn-transfer-add-chunk", "host/", "tools/"],
            cwd=ROOT, capture_output=True, text=True).stdout.split()
        self.assertEqual(named, [], "the premise of this test has changed")
        self.assertNotIn("fn-transfer-add-chunk", self.graph.reachable)

    def test_an_attached_implementation_is_reached_through_its_constraint(self):
        """host/store-host.lisp names files through fn-store-txn-name ->
        fn-sbud-txn-name -> the constrained fn-bs-txn-name, which
        books/byte-store-txn-name.lisp `defattach`es to fn-bs-txn-name-impl."""
        self.assertIn("fn-bs-txn-name-impl", self.graph.reachable)

    def test_the_bridges_count_as_host_lines(self):
        """tools/run_owner.py drives the owner by building ACL2 forms as
        text. A symbol named only there is still called by the host."""
        self.assertGreater(self.graph.seeds["bridge"], 0)


class RatchetTests(unittest.TestCase):
    """The baseline may shrink and may not grow silently."""

    def run_check(self, *flags):
        return subprocess.run(
            [sys.executable, "tools/reach_check.py", *flags],
            cwd=ROOT, capture_output=True, text=True)

    def test_the_tree_is_at_its_baseline(self):
        done = self.run_check("--summary", "--strict")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("0 of them unbaselined", done.stdout)

    def test_an_unbaselined_orphan_fails_and_is_named(self):
        registry = ROOT / "planning" / "proofs.json"
        original = registry.read_text()
        planted = "fn-transfer-add-chunk-preserves-statep"
        try:
            loaded = json.loads(original)
            rows = loaded["proofs"] if isinstance(loaded, dict) else loaded
            rows[0]["events"] = list(rows[0].get("events", [])) + [planted]
            registry.write_text(json.dumps(loaded, indent=2) + "\n")
            done = self.run_check("--summary", "--strict")
            self.assertEqual(done.returncode, 1, done.stdout)
            self.assertIn("NEW unreachable subject", done.stdout)
            self.assertIn(planted, done.stdout)
        finally:
            registry.write_text(original)
        self.assertEqual(registry.read_text(), original)

    def test_every_baselined_orphan_carries_a_reason(self):
        baseline = json.loads(
            (ROOT / "planning" / "reach-baseline.json").read_text())
        self.assertTrue(baseline["accepted"])
        for key, reason in baseline["accepted"].items():
            self.assertGreater(len(reason), 40,
                               f"{key} is accepted without saying why")
        self.assertEqual(reach_check.unexplained(baseline["accepted"]), [])

    def test_a_placeholder_reason_is_untriaged(self):
        self.assertEqual(
            reach_check.unexplained({"PRF-1:x": "no host line reaches this subject and "
                                     + reach_check.PLACEHOLDER,
                                     "PRF-1:y": "SPEC: the model the hosted z refines",
                                     "PRF-1:w": "a reason with no disposition word"}),
            ["PRF-1:w", "PRF-1:x"])


if __name__ == "__main__":
    unittest.main()

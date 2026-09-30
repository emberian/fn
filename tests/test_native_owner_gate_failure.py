"""Actual gate/owner failure containment with recording ACL2 scheduler results."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tests.test_native_receiver_failure_boundary import ROOT, proof_repl, selected_source

GATE_NAMES = [
    "fnn-owner-gate-abort-locked", "fnn-owner-gate-abort", "fnn-owner-gate-check",
    "fnn-owner-gate-fail-locked", "fnn-owner-class-index", "fnn-owner-gate-pick",
    "fnn-owner-gate-enter", "fnn-owner-gate-leave",
    "fnn-owner-stop-service",
]


def gate_source(tree):
    source, hashes = selected_source(tree)
    forms = proof_repl.forms((tree / "host/native/owner.lisp").read_text())
    named = {proof_repl.head_and_name(f)[1]: f for f in forms}
    extra = [next(f for f in forms if f.startswith("(defstruct (fnn-owner-gate "))]
    hashes["fnn-owner-gate"] = hashlib.sha256(extra[0].encode()).hexdigest()
    for name in GATE_NAMES:
        extra.append(named[name])
        hashes[name] = hashlib.sha256(named[name].encode()).hexdigest()
    return source + "\n\n".join(extra) + "\n", hashes


class OwnerGateFailureTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_gate_fault_stops_and_wakes_queued_waiters(self):
        tree = Path(os.environ.get("FN_GATE_FAILURE_SOURCE_TREE", ROOT))
        source, hashes = gate_source(tree)
        base = (ROOT / "tests/fixtures/native_receiver_failure_boundary.lisp").read_text()
        base = base.split(";; Complete normal result")[0]
        fixture = base + (ROOT / "tests/fixtures/native_owner_gate_failure.lisp").read_text()
        with tempfile.TemporaryDirectory() as directory:
            source_path = Path(directory) / "source.lisp"
            source_path.write_text(source)
            driver_path = Path(directory) / "driver.lisp"
            driver_path.write_text(fixture.replace("__SOURCE_FILE__", json.dumps(str(source_path))))
            run = subprocess.run(
                [shutil.which("sbcl"), "--noinform", "--disable-debugger", "--script", str(driver_path)],
                capture_output=True, text=True, timeout=30,
            )
        after, after_hashes = gate_source(tree)
        evidence = os.environ.get("FN_GATE_FAILURE_EVIDENCE")
        if evidence:
            destination = Path(evidence)
            destination.mkdir(parents=True, exist_ok=True)
            (destination / "source.lisp").write_text(source)
            (destination / "fixture.lisp").write_text(fixture)
            (destination / "run.log").write_text(run.stdout + run.stderr)
            (destination / "result.json").write_text(json.dumps({
                "source_tree": str(tree), "function_hashes_before": hashes,
                "function_hashes_after": after_hashes,
                "fixture_sha256": hashlib.sha256(fixture.encode()).hexdigest(),
                "exit_code": run.returncode,
                "scope": "Actual gate enter/pick/leave and owner boundaries, real mutexes/waiters, recording ACL2 scheduler decisions; not cost/image qualification",
            }, indent=2) + "\n")
        self.assertEqual(source, after, "selected source changed during test")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("PASS owner gate failure boundary", run.stdout)


if __name__ == "__main__":
    unittest.main()

"""Actual receiver/owner fault composition with recording core callbacks.

Uses real SBCL mutexes, arrays and the selected native function bodies.
Scheduler admission, core callbacks and provider projection are recording
adapters; this is not a core proof, funded runtime or image qualification.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import proof_repl

SELECTED = {
    "host/native/io.lisp": [
        "fnn-store-error", "fnn-store-fault", "fnn-fixed-callback-fault",
        "fnn-fixed-callback-fail", "fnn-store-indeterminate", "fnn-os-error",
        "fnn-refuse", "fnn-fault", "fnn-core-mv",
    ],
    "host/native/owner.lisp": [
        "fnn-with-roster", "fnn-owner-gated", "fnn-payload-lifecycle-drain",
        "fnn-owner-stop-service-locked", "fnn-owner-signal-commit",
        "fnn-owner-shared-action-locked", "fnn-owner-serialized",
        "fnn-owner-connection-selected-p",
        "fnn-owner-receiver-fill",
    ],
}


def selected_source(tree):
    selected = []
    hashes = {}
    for relative, names in SELECTED.items():
        forms = proof_repl.forms((tree / relative).read_text())
        named = {proof_repl.head_and_name(form)[1]: form for form in forms}
        if relative.endswith("owner.lisp"):
            struct = next(form for form in forms
                          if form.startswith("(defstruct (fnn-owner-service "))
            selected.append(struct)
            hashes["fnn-owner-service"] = hashlib.sha256(struct.encode()).hexdigest()
        for name in names:
            form = named[name]
            selected.append(form)
            hashes[name] = hashlib.sha256(form.encode()).hexdigest()
    return "\n\n".join(selected) + "\n", hashes


class ReceiverFailureBoundaryTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_receiver_fault_fences_before_later_work(self):
        tree = Path(os.environ.get("FN_RX_FAILURE_SOURCE_TREE", ROOT))
        source, hashes = selected_source(tree)
        fixture = (ROOT / "tests/fixtures/native_receiver_failure_boundary.lisp").read_text()
        with tempfile.TemporaryDirectory() as directory:
            source_path = Path(directory) / "source.lisp"
            source_path.write_text(source)
            driver = fixture.replace("__SOURCE_FILE__", json.dumps(str(source_path)))
            driver_path = Path(directory) / "driver.lisp"
            driver_path.write_text(driver)
            run = subprocess.run(
                [shutil.which("sbcl"), "--noinform", "--disable-debugger", "--script", str(driver_path)],
                capture_output=True, text=True, timeout=30,
            )
        after_source, after_hashes = selected_source(tree)
        evidence = os.environ.get("FN_RX_FAILURE_EVIDENCE")
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
                "scope": "Actual native bodies; recording core/scheduler/provider adapters; no qualification or funding claim",
            }, indent=2) + "\n")
        self.assertEqual(source, after_source, "source changed during execution")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("PASS receiver fault boundary", run.stdout)


if __name__ == "__main__":
    unittest.main()

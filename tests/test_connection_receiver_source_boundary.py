"""Actual connection/RX wrapper ordering, with recording core decisions only."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest
from tests.test_native_receiver_failure_boundary import ROOT, proof_repl

SUBJECTS = {
    "planning/evidence/connection-receiver-source-2026-09-30/acquisition-gate-recording/controller-source.lisp": {
        "fn-rxt-pending-rangep", "fn-owner-rx-turn-parser-acquirablep", "fn-owner-rx-turn-parser-acquire"},
    "planning/evidence/connection-receiver-source-2026-09-30/native-hooks/selected-source.lisp": {
        "fnn-owner-connection-open-locked", "fnn-owner-connection-close-locked", "fnn-owner-receiver-turn-start"},
    "books/connection-receiver-source.lisp": {
        "fn-crx-originp", "fn-crx-open-origin", "fn-crx-origin-currentp",
        "fn-crx-issued", "fn-crx-turn-currentp", "fn-crx-revoke"},
    "host/receiver-source-gate-host.lisp": {
        "fn-owner-rx-connection-issued", "fn-owner-rx-parser-source-currentp",
        "fn-owner-rx-connection-revoke"},
    "host/connection-receiver-source-host.lisp": {
        "fn-mio-connection-rx-path", "fn-owner-index-rx-open",
        "fn-owner-rx-connection-turn-start", "fn-owner-index-rx-close"},
}

def selected():
    chunks, hashes = [], {}
    for path, names in SUBJECTS.items():
        forms = [f for f in proof_repl.forms((ROOT / path).read_text())
                 if proof_repl.head_and_name(f)[1] in names]
        assert len(forms) == len(names), (path, len(forms), len(names))
        chunks.extend(forms)
        hashes.update({proof_repl.head_and_name(f)[1]: hashlib.sha256(f.encode()).hexdigest()
                       for f in forms})
    return "\n\n".join(chunks), hashes

class ConnectionReceiverSourceBoundary(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_wrappers(self):
        source, hashes = selected()
        fixture = (ROOT / "tests/fixtures/connection_receiver_source_boundary.lisp").read_text()
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory)
            (p / "source.lisp").write_text(source)
            (p / "driver.lisp").write_text(fixture.replace("__SOURCE_FILE__", json.dumps(str(p / "source.lisp"))))
            run = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger",
                                  "--script", str(p / "driver.lisp")],
                                 capture_output=True, text=True, timeout=30)
        after, after_hashes = selected()
        evidence = os.environ.get("FN_CONNECTION_RX_EVIDENCE")
        if evidence:
            d = Path(evidence); d.mkdir(parents=True, exist_ok=True)
            (d / "selected-source.lisp").write_text(source)
            (d / "run.log").write_text(run.stdout + run.stderr)
            match = re.search(r"boundaries: (\d+) scenarios", run.stdout)
            (d / "result.json").write_text(json.dumps({
                "function_hashes_before": hashes, "function_hashes_after": after_hashes,
                "file_hashes": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SUBJECTS},
                "fixture_sha256": hashlib.sha256(fixture.encode()).hexdigest(),
                "exit_code": run.returncode, "scenarios": int(match[1]) if match else None,
                "scope": "Literal actual 19 functions, recording runtime getter/core/registry/STATE; no installation/native/proof/funding claim"
            }, indent=2) + "\n")
        self.assertEqual(source, after, "source changed during boundary test")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("PASS connection receiver boundaries", run.stdout)

    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_ordering_refuters(self):
        source, _ = selected()
        fixture = (ROOT / "tests/fixtures/connection_receiver_source_boundary.lisp").read_text()
        mutations = {
            "filled-gate-deadlock": ("(fn-owner-rx-turn-parser-acquirablep ticket fn-rx-provider\n", "(fn-owner-rx-turn-consumablep ticket fn-rx-provider\n"),
            "open-suffix-unfunded": ("(* 8 path)", "(* 7 path)"),
            "close-suffix-unfunded": ("(* 6 path)", "(* 5 path)"),
            "post-open-capacity-unchecked": ("(equal capacity capacity1)", "t"),
            "post-open-instance-unchecked": ("(equal instance instance1)", "t"),
            "erp-binds": ("(or erp (not (eq (fn-omk-at 0 result) :opened)))", "(not (eq (fn-omk-at 0 result) :opened))"),
            "busy-overwrites-state": ("(if (not (eq started :admitted))", "(if nil"),
            "native-current-not-forwarded": ("(fnn-owner-receiver-turn-runtime-current runtime)", ":wrong-current"),
            "native-turn-update-dropped": ("(fnn-owner-receiver-turn-runtime-turn runtime) turn)", "(fnn-owner-receiver-turn-runtime-turn runtime) :turn)"),
            "close-before-state-revoke": ("(let ((state (fn-owner-rx-connection-revoke id holder state)))", "(let ((state state))"),
        }
        results = {}
        for name, (old, new) in mutations.items():
            with self.subTest(mutation=name), tempfile.TemporaryDirectory() as directory:
                self.assertEqual(source.count(old), 1)
                p = Path(directory)
                (p / "source.lisp").write_text(source.replace(old, new, 1))
                (p / "driver.lisp").write_text(fixture.replace("__SOURCE_FILE__", json.dumps(str(p / "source.lisp"))))
                run = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger",
                                      "--script", str(p / "driver.lisp")], capture_output=True, text=True, timeout=30)
                results[name] = {"exit_code": run.returncode, "scope": "Test-only mutation; actual retained fixture refuted"}
                evidence = os.environ.get("FN_CONNECTION_RX_EVIDENCE")
                if evidence:
                    (Path(evidence) / (name + ".log")).write_text(run.stdout + run.stderr)
                self.assertNotEqual(run.returncode, 0, name + " was not refuted")
                self.assertIn("assertion", run.stderr.lower(), run.stdout + run.stderr)
        evidence = os.environ.get("FN_CONNECTION_RX_EVIDENCE")
        if evidence:
            (Path(evidence) / "ordering-refuters.json").write_text(json.dumps(results, indent=2) + "\n")

if __name__ == "__main__":
    unittest.main()

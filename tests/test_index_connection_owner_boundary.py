"""Actual owner join bodies against recording core/registry decisions.

This verifies ordering and uncertainty propagation, not ACL2 composition,
constructor adequacy, native dispatch, or source/owner correspondence.
"""
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tests.test_native_receiver_failure_boundary import ROOT, proof_repl

OWNER_NAMES = {
    "fn-owner-open-at", "fn-owner-open", "fn-owner-exposure-open",
    "fn-owner-open-peer", "fn-owner-close", "fn-owner-fault",
    "fn-owner-at-reader-view", "fn-owner-at-working-view",
}
JOIN_NAMES = {"fn-owner-index-open", "fn-owner-index-close"}


def selected(tree, relative, names):
    forms = proof_repl.forms((tree / relative).read_text())
    matched = [f for f in forms if proof_repl.head_and_name(f)[1] in names]
    assert len(matched) == len(names), (relative, len(matched), len(names))
    return "\n\n".join(matched), {
        proof_repl.head_and_name(f)[1]: hashlib.sha256(f.encode()).hexdigest()
        for f in matched
    }


class IndexConnectionOwnerTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_owner_boundary(self):
        owner = Path(os.environ.get("FN_CONNECTION_OWNER_SOURCE_TREE", ROOT))
        a, ah = selected(owner, "host/owner-host.lisp", OWNER_NAMES)
        b, bh = selected(ROOT, "host/index-connection-owner-host.lisp", JOIN_NAMES)
        fixture = (ROOT / "tests/fixtures/index_connection_owner_boundary.lisp").read_text()
        with tempfile.TemporaryDirectory() as directory:
            source_path = Path(directory) / "source.lisp"
            source_path.write_text(a + "\n" + b + "\n")
            driver = Path(directory) / "driver.lisp"
            driver.write_text(fixture.replace("__SOURCE_FILE__", json.dumps(str(source_path))))
            run = subprocess.run(
                [shutil.which("sbcl"), "--noinform", "--disable-debugger", "--script", str(driver)],
                capture_output=True, text=True, timeout=30,
            )
        a2, ah2 = selected(owner, "host/owner-host.lisp", OWNER_NAMES)
        b2, bh2 = selected(ROOT, "host/index-connection-owner-host.lisp", JOIN_NAMES)
        evidence = os.environ.get("FN_CONNECTION_OWNER_EVIDENCE")
        if evidence:
            destination = Path(evidence)
            destination.mkdir(parents=True, exist_ok=True)
            (destination / "selected-source.lisp").write_text(a + "\n" + b + "\n")
            (destination / "run.log").write_text(run.stdout + run.stderr)
            (destination / "result.json").write_text(json.dumps({
                "owner_source_tree": str(owner), "function_hashes_before": {**ah, **bh},
                "function_hashes_after": {**ah2, **bh2}, "exit_code": run.returncode,
                "fixture_sha256": hashlib.sha256(fixture.encode()).hexdigest(),
                "scenarios": int(re.search(r"boundaries: (\d+) scenarios", run.stdout)[1]) if run.returncode == 0 else None,
                "scope": "Actual eight owner and two join bodies; recording core/registry/STATE; no ACL2 composite/native/funding claim",
            }, indent=2) + "\n")
        self.assertEqual(a + b, a2 + b2, "selected source changed during test")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("PASS connection owner boundaries", run.stdout)


if __name__ == "__main__":
    unittest.main()

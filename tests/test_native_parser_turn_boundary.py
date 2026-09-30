"""Actual parser transport/escape boundary, with recording core and I/O."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "planning/evidence/native-parser-turn-2026-09-30"
SOURCES = [ROOT / "planning/evidence/native-parser-stop-2026-09-30/native-stop-source.lisp",
           PACKET / "native-boundary-source.lisp", PACKET / "runtime-source.lisp",
           ROOT / "host/native/receiver-parser-turn.lisp"]


class NativeParserTurnBoundary(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_transport_and_escape(self):
        self.run_fixture()

    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_transport_mutations(self):
        changes = {
            "current-substitution": ("(fnn-owner-receiver-turn-runtime-current runtime)", ":wrong-current"),
            "holder-substitution": ("(fnn-connection-custody-token node)", ":wrong-holder"),
            "pool-return-dropped": ("(fnn-owner-service-connection-pool service) pool)",
                                    "(fnn-owner-service-connection-pool service) :old-pool)"),
            "turn-return-dropped": ("(fnn-owner-receiver-turn-runtime-turn runtime) turn\n",
                                    "(fnn-owner-receiver-turn-runtime-turn runtime) :old-turn\n"),
        }
        for name, change in changes.items():
            with self.subTest(mutation=name):
                self.run_fixture(name, change)

    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_stop_boundary_mutations(self):
        self.run_fixture("missing-stop-fence",
                         ("(fnn-owner-service-stopping service) t", "(fnn-owner-service-stopping service) nil"), 0)
        self.run_fixture("drain-skipped",
                         ("(when first-stop (fnn-payload-lifecycle-drain service))", "nil"), 0)

    def run_fixture(self, name="baseline", change=None, source_index=-1):
        originals = [p.read_text() for p in SOURCES]
        chunks = originals.copy()
        if change:
            old, new = change
            self.assertEqual(chunks[source_index].count(old), 1)
            chunks[source_index] = chunks[source_index].replace(old, new, 1)
        source = "\n\n".join(chunks)
        fixture = (ROOT / "tests/fixtures/native_parser_turn_boundary.lisp").read_text()
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            (tmp / "source.lisp").write_text(source)
            (tmp / "driver.lisp").write_text(fixture.replace("__SOURCE_FILE__", json.dumps(str(tmp / "source.lisp"))))
            run = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger", "--script",
                                  str(tmp / "driver.lisp")], capture_output=True, text=True, timeout=30)
        self.assertEqual(originals, [p.read_text() for p in SOURCES])
        evidence = os.environ.get("FN_NATIVE_PARSER_EVIDENCE")
        if evidence:
            out = Path(evidence); out.mkdir(parents=True, exist_ok=True)
            (out / (name + ".log")).write_text(run.stdout + run.stderr)
            (out / (name + ".json")).write_text(json.dumps({
                "source_hashes": {str(p.relative_to(ROOT)): hashlib.sha256(s.encode()).hexdigest()
                                  for p, s in zip(SOURCES, originals)},
                "fixture_sha256": hashlib.sha256(fixture.encode()).hexdigest(),
                "exit_code": run.returncode,
                "scope": "Literal native transport, runtime constructor/startup, core-MV and shared-action boundary; recording core/provider/claim/STATE; no installed runtime or allocation qualification"
            }, indent=2) + "\n")
        if change:
            self.assertNotEqual(run.returncode, 0)
            self.assertIn("assertion", run.stderr.lower(), run.stdout + run.stderr)
        else:
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn("PASS native parser turn", run.stdout)


if __name__ == "__main__":
    unittest.main()

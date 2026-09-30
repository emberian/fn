"""Actual evaluation/install cut with recording parser storage and STATE writes.

No installed runtime, ACL2 composition or alias settlement claim.
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

SOURCE = ROOT / "planning/evidence/reader-parser-staged-candidate-2026-09-30/current-result.lisp"

class ReaderParserInstallBoundary(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_evaluation_install_cuts(self):
        source = SOURCE.read_text() + "\n" + (SOURCE.parent / "parser-span.lisp").read_text()
        fixture = (ROOT / "tests/fixtures/reader_parser_install_boundary.lisp").read_text()
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory)
            (p / "source.lisp").write_text(source)
            (p / "driver.lisp").write_text(fixture.replace("__SOURCE_FILE__", json.dumps(str(p / "source.lisp"))))
            run = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger", "--script", str(p / "driver.lisp")],
                                 capture_output=True, text=True, timeout=30)
        evidence = os.environ.get("FN_PARSER_INSTALL_EVIDENCE")
        if evidence:
            d = Path(evidence); d.mkdir(parents=True, exist_ok=True)
            (d / "run.log").write_text(run.stdout + run.stderr)
            (d / "selected-source.lisp").write_text(source)
            (d / "result.json").write_text(json.dumps({"source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "fixture_sha256": hashlib.sha256(fixture.encode()).hexdigest(), "exit_code": run.returncode,
                "scope": "Actual five evaluator/install/delegation/upper caller bodies; recording core, parser stage and STATE; no actual service/proof/runtime/settlement claim"}, indent=2) + "\n")
        self.assertEqual(source, SOURCE.read_text() + "\n" + (SOURCE.parent / "parser-span.lisp").read_text())
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("PASS parser install cuts", run.stdout)

    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_stage_ordering_refuters(self):
        source = SOURCE.read_text() + "\n" + (SOURCE.parent / "parser-span.lisp").read_text()
        fixture = (ROOT / "tests/fixtures/reader_parser_install_boundary.lisp").read_text()
        changes = {
            "missing-stage": ("(fn-owner-rx-turn-parser-stage ticket RC fn-rx-provider fn-receiver-turn fn-page-read-pool)",
                              "(mv :parser-staged fn-rx-provider fn-receiver-turn fn-page-read-pool)"),
            "state-write-before-stage": ("(mv nil cache RC state)",
                              "(mv nil cache RC (f-put-global 'fn-owner-access-cache cache state))"),
            "finish-source-detached": ("(fn-owner-rx-turn-parser-finish ticket wire step", "(fn-owner-rx-turn-parser-finish ticket :old-wire step"),
        }
        results = {}
        for name, (old, new) in changes.items():
            with self.subTest(mutation=name), tempfile.TemporaryDirectory() as directory:
                self.assertEqual(source.count(old), 1)
                p = Path(directory)
                (p / "source.lisp").write_text(source.replace(old, new, 1))
                (p / "driver.lisp").write_text(fixture.replace("__SOURCE_FILE__", json.dumps(str(p / "source.lisp"))))
                run = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger", "--script", str(p / "driver.lisp")],
                                     capture_output=True, text=True, timeout=30)
                results[name] = {"exit_code": run.returncode, "scope": "Test-only mutation refuted by unchanged fixture assertion"}
                evidence = os.environ.get("FN_PARSER_INSTALL_EVIDENCE")
                if evidence:
                    (Path(evidence) / (name + ".log")).write_text(run.stdout + run.stderr)
                self.assertNotEqual(run.returncode, 0)
                self.assertIn("assertion", run.stderr.lower(), run.stdout + run.stderr)
        evidence = os.environ.get("FN_PARSER_INSTALL_EVIDENCE")
        if evidence:
            (Path(evidence) / "refuters.json").write_text(json.dumps(results, indent=2) + "\n")

if __name__ == "__main__":
    unittest.main()

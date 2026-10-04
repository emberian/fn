"""Selected Linux/SBCL foreign-observation primitive, not served installation."""
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
INPUTS = (
    "host/native/fn-fs-observation.c",
    "host/native/fs-observation.lisp",
    "tests/native/fs-observation-controlled-mock.c",
    "tests/native/fs-observation-component.lisp",
)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class FilesystemObservationTests(unittest.TestCase):
    @unittest.skipUnless(platform.system() == "Linux" and platform.machine() == "x86_64",
                         "this evidence fixture selects Linux x86-64")
    def test_actual_syscall_fields_failure_and_foreign_wait_gc(self):
        compiler = shutil.which(os.environ.get("CC", "cc"))
        sbcl = shutil.which(os.environ.get("FN_FS_OBSERVATION_SBCL", "sbcl"))
        self.assertIsNotNone(compiler, "a C11 compiler is required")
        self.assertIsNotNone(sbcl, "the selected SBCL executable is required")
        before = {name: digest(ROOT / name) for name in INPUTS}
        records = []
        with tempfile.TemporaryDirectory(prefix="fn-fs-observation-") as directory:
            work = Path(directory)
            libraries = []
            for source, name in ((INPUTS[0], "observation"), (INPUTS[2], "controlled")):
                library = work / ("lib" + name + ".so")
                argv = [compiler, "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror",
                        "-fPIC", "-shared", "-pthread", str(ROOT / source), "-o", str(library)]
                built = subprocess.run(argv, capture_output=True, text=True, timeout=60)
                records.append({"argv": argv, "returncode": built.returncode,
                                "stdout": built.stdout, "stderr": built.stderr})
                self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
                libraries.append(library)
            disassembly = work / "disassembly.txt"
            argv = [sbcl, "--noinform", "--disable-debugger", "--script", str(ROOT / INPUTS[3]),
                    *(str(path) for path in libraries), str(ROOT / INPUTS[1]), str(disassembly)]
            run = subprocess.run(argv, capture_output=True, text=True, timeout=30)
            records.append({"argv": argv, "returncode": run.returncode,
                            "stdout": run.stdout, "stderr": run.stderr})
            evidence = os.environ.get("FN_FS_OBSERVATION_EVIDENCE")
            if evidence:
                out = Path(evidence)
                out.mkdir(parents=True, exist_ok=True)
                (out / "runs.json").write_text(json.dumps(records, indent=2) + "\n")
                (out / "native-run.log").write_text(run.stdout + run.stderr)
                if disassembly.exists():
                    shutil.copyfile(disassembly, out / "disassembly.txt")
                (out / "coordinate.json").write_text(json.dumps({
                    "inputs": before,
                    "sbcl": {"path": sbcl, "sha256": digest(sbcl)},
                    "compiler": {"path": compiler, "sha256": digest(compiler),
                                 "version": subprocess.check_output([compiler, "--version"], text=True)},
                    "libraries": {path.name: digest(path) for path in libraries},
                    "platform": platform.platform(),
                    "scope": "Actual primitive and controlled foreign wait/full GC; no ACL2 proof, "
                             "installed admission, global participant policy, libc allocation bound or served activation.",
                }, indent=2) + "\n")
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            for marker in ("real success/failure PASS", "wide fields/stale failure PASS",
                           "foreign wait/full GC/retained storage PASS",
                           "lost acknowledgment retains uncertainty PASS",
                           "FS-OBSERVATION-COMPONENT PASS"):
                self.assertIn(marker, run.stdout)
        self.assertEqual(before, {name: digest(ROOT / name) for name in INPUTS})


if __name__ == "__main__":
    unittest.main()

"""Source gate preflight controls; no ACL2, compiler, or listener starts."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

GATE = Path(__file__).resolve().parents[1] / 'tools/native_gate.sh'
SHA = 'a' * 40


class NativeGate(unittest.TestCase):
    def test_bad_source_pin_refuses_before_git_or_runtime(self):
        result = subprocess.run(['/bin/sh', str(GATE), '/absent', 'short', 'fnct'], capture_output=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn(b'full 40-character SHA', result.stderr)

    def test_durable_retry_uses_a_separate_store_and_grant_cut(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binaries = root / "bin"
            binaries.mkdir()
            log = root / "calls"
            (binaries / "git").write_text('#!/bin/sh\ncase "$*" in *rev-parse*) echo '+SHA+';; esac\n')
            (binaries / "python3").write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "'+str(log)+'"\n')
            for command in binaries.iterdir():
                command.chmod(0o755)
            env = dict(os.environ, PATH=str(binaries) + ":/usr/bin:/bin")
            for mode in ("fnct", "durable-retry"):
                subprocess.run(["/bin/sh", str(GATE), str(root), SHA, mode],
                               env=env, capture_output=True, check=True)
            campaigns = [call.split() for call in log.read_text().splitlines()
                         if call.startswith("tests/native-append-fetch-restart.py ")]
            self.assertEqual(len(campaigns), 2)
            for call, mode, options in zip(campaigns, ("fnct", "durable-retry"),
                                           ([], ["--durable-retry"])):
                script, flag, directory, *extra = call
                self.assertEqual(script, "tests/native-append-fetch-restart.py")
                self.assertEqual(flag, "--directory")
                self.assertEqual(extra, options)
                path = Path(directory)
                self.assertEqual(path.parent.parent, Path("build"))
                self.assertTrue(path.parent.name.startswith(f"native-{SHA}-{mode}."))
                self.assertEqual(path.name, "run")

    def test_retry_after_failure_retains_first_image(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("bin", "tests", "tools"):
                (root / name).mkdir()
            git = root / "bin" / "git"
            git.write_text('#!/bin/sh\ncase "$*" in *rev-parse*) echo '+SHA+';; esac\n')
            git.chmod(0o755)
            (root / "bin" / "python3").symlink_to(sys.executable)
            (root / "tools" / "certs.py").write_text("raise SystemExit(0)\n")
            (root / "tests" / "native-append-fetch-restart.py").write_text(
                "from pathlib import Path\nimport sys\n"
                "run = Path(sys.argv[2])\nrun.mkdir(parents=True, exist_ok=False)\n"
                "retry = Path('first-attempt').exists()\n"
                "(run / 'node.img').write_bytes(b'retry' if retry else b'first')\n"
                "if not retry: Path('first-attempt').write_text(str(run))\n"
                "raise SystemExit(0 if retry else 17)\n")
            env = dict(os.environ, PATH=str(root / "bin") + ":/usr/bin:/bin")
            def attempt():
                return subprocess.run(["/bin/sh", str(GATE), str(root), SHA, "fnct"],
                                      env=env, capture_output=True)
            self.assertEqual(attempt().returncode, 17)
            first_image = root / (root / "first-attempt").read_text() / "node.img"
            retry = attempt()
            self.assertEqual(retry.returncode, 0, retry.stderr)
            self.assertEqual(first_image.read_bytes(), b"first")
            self.assertCountEqual((p.read_bytes() for p in (root / "build").rglob("node.img")),
                                  [b"first", b"retry"])

    def test_missing_current_certificates_refuse_before_build_or_socket(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); binaries = root/'bin'; binaries.mkdir()
            log = root/'calls'
            (binaries/'git').write_text('#!/bin/sh\ncase "$*" in *rev-parse*) echo '+SHA+';; esac\n')
            (binaries/'python3').write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "'+str(log)+'"\nexit 31\n')
            for command in binaries.iterdir(): command.chmod(0o755)
            env = dict(os.environ, PATH=str(binaries)+':/usr/bin:/bin')
            for mode in ('host','fnct','durable-retry','nntp','large','cursor','fanout','membership'):
                with self.subTest(mode=mode):
                    result = subprocess.run(['/bin/sh',str(GATE),str(root),SHA,mode],env=env,capture_output=True)
                    self.assertEqual(result.returncode,31,result.stderr)
            calls=log.read_text().splitlines()
            self.assertEqual(len(calls),8)
            self.assertTrue(all(line.startswith('tools/certs.py install-set books/node-profile books/native-b3-evidence ') for line in calls))
            self.assertTrue(all('--toolchain-identity 8aeb1bea' in line for line in calls))
            self.assertFalse((root/'build').exists())

if __name__=='__main__': unittest.main()

"""Source gate preflight controls; no ACL2, compiler, or listener starts."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

GATE = Path(__file__).resolve().parents[1] / 'tools/native_gate.sh'
SHA = 'a' * 40


class NativeGate(unittest.TestCase):
    def test_bad_source_pin_refuses_before_git_or_runtime(self):
        result = subprocess.run(['/bin/sh', str(GATE), '/absent', 'short', 'fnct'], capture_output=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn(b'full 40-character SHA', result.stderr)

    def test_missing_current_certificates_refuse_before_build_or_socket(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); binaries = root/'bin'; binaries.mkdir()
            log = root/'calls'
            (binaries/'git').write_text('#!/bin/sh\ncase "$*" in *rev-parse*) echo '+SHA+';; esac\n')
            (binaries/'python3').write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "'+str(log)+'"\nexit 31\n')
            for command in binaries.iterdir(): command.chmod(0o755)
            env = dict(os.environ, PATH=str(binaries)+':/usr/bin:/bin')
            for mode in ('host','fnct','nntp','large','cursor'):
                with self.subTest(mode=mode):
                    result = subprocess.run(['/bin/sh',str(GATE),str(root),SHA,mode],env=env,capture_output=True)
                    self.assertEqual(result.returncode,31,result.stderr)
            calls=log.read_text().splitlines()
            self.assertEqual(len(calls),5)
            self.assertTrue(all(line.startswith('tools/certs.py install-set books/node-profile books/native-b3-evidence ') for line in calls))
            self.assertTrue(all('--toolchain-identity 8aeb1bea' in line for line in calls))
            self.assertFalse((root/'build').exists())

if __name__=='__main__': unittest.main()

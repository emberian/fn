"""Run actual native writer transport with recording core callbacks, no image grant."""
import os
from pathlib import Path
import subprocess
import shutil
import tempfile
import unittest

from tools.proof_repl import spans

ROOT = Path(__file__).resolve().parents[1]


class NativeIndexWriterTransport(unittest.TestCase):
    def test_recording_transports_use_current_core_mv(self):
        io = (ROOT / 'host/native/io.lisp').read_text()
        macro = next(io[a:b] for a, b in spans(io)
                     if io[a:b].startswith('(defmacro fnn-core-mv '))
        fixture = (ROOT / 'tests/native/index-writer-turn-recording.lisp').read_text()
        anchor = '(in-package "ACL2")'
        self.assertEqual(fixture.count(anchor), 1)
        fixture = fixture.replace(anchor, anchor + '\n' + macro, 1)
        sbcl = os.environ.get('FN_SBCL') or subprocess.check_output(
            ['python3', 'tools/native_env.py', 'sbcl'], cwd=ROOT, text=True).strip() or shutil.which('sbcl')
        self.assertIsNotNone(sbcl, 'An SBCL executable is required for this source fixture')
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / 'recording.lisp'
            script.write_text(fixture)
            result = subprocess.run([sbcl, '--script', str(script)], cwd=ROOT,
                                    text=True, capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.count('PASS recorded'), 3, result.stdout)

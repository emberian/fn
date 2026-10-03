"""The acceptance packet refuses missing inputs before invoking an image."""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class AcceptanceInputs(unittest.TestCase):
    def test_missing_subject_is_named_without_traceback_or_packet(self):
        script = (ROOT / 'tests/ltp/run_current_source_acceptance.sh').read_text()
        program = script.split("<<'PY'\n", 1)[1].split('\nPY\n', 1)[0]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            image = root / 'image'
            image.write_bytes(b'not executed')
            packet = root / 'packet'
            done = subprocess.run([sys.executable, '-', str(packet), str(image),
                                   'historical-identity', hashlib.sha256(image.read_bytes()).hexdigest(), str(root)],
                                  input=program, capture_output=True, text=True)
            self.assertNotEqual(done.returncode, 0)
            self.assertIn('MissingAcceptanceSubject: host/native/workflow.lisp', done.stderr)
            self.assertNotIn('Traceback', done.stderr)
            self.assertFalse(packet.exists())

    def test_subjects_exist_and_missing_runner_dependency_is_named(self):
        script = (ROOT / 'tests/ltp/run_current_source_acceptance.sh').read_text()
        program = script.split("<<'PY'\n", 1)[1].split('\nPY\n', 1)[0]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            image = root / 'image'
            image.write_bytes(b'not executed')
            done = subprocess.run([sys.executable, '-', str(root / 'packet'), str(image), 'old',
                                   hashlib.sha256(image.read_bytes()).hexdigest(), str(ROOT)],
                                  input=program, capture_output=True, text=True)
            self.assertNotEqual(done.returncode, 0)
            self.assertIn('MissingAcceptanceDependency:', done.stderr)
            self.assertNotIn('Traceback', done.stderr)

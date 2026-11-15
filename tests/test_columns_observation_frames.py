"""Narrow source controls; ACL2 admission belongs to the actual caller gate."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'books/columns-observation-frames.lisp'

class ObservationFrames(unittest.TestCase):
    def run_controls(self, source=SOURCE):
        return subprocess.run(['sbcl', '--script', 'tests/columns-observation-frames-controls.lsp'],
                              cwd=ROOT, env={**os.environ, 'FRAME_SOURCE': str(source)},
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def test_exact_event_and_refusals(self):
        result = self.run_controls()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('SOURCE CONTROLS PASS', result.stdout)

    def mutant(self, old, new):
        source = SOURCE.read_text()
        self.assertEqual(source.count(old), 1)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'mutant.lisp'
            path.write_text(source.replace(old, new))
            result = self.run_controls(path)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn('assertion', result.stdout.lower())

    def test_same_field_acceptance_mutant_refused(self):
        self.mutant('(not (eq read-field write-field))', 't')

    def test_wrong_subject_mutant_refused(self):
        self.mutant('(,reader i ,table))', '(,reader j ,table))')

    def test_missing_frame_mutant_refused(self):
        self.mutant("(getpropc frame 'theorem nil world)", 't')

if __name__ == '__main__':
    unittest.main()

"""Narrow source controls; ACL2 admission belongs to the actual caller gate."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import sys

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'books/columns.lisp'
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr

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
        functions = lr.match('(defun fn2-columns-observation-frame-event ?*body)',
                             lr.parse(source).forms, deep=False)
        self.assertEqual(len(functions), 1)
        function = functions[0]
        target = source[function.start:function.end]
        self.assertEqual(target.count(old), 1)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'mutant.lisp'
            path.write_text(source[:function.start] + target.replace(old, new) +
                            source[function.end:])
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

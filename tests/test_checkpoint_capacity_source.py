"""Source arithmetic controls only: no ACL2 admission or production execution."""
import shutil
import subprocess
import unittest
from pathlib import Path

from tools import lisp_source

ROOT = Path(__file__).resolve().parents[1]


def emit(value):
    return '(' + ' '.join(map(emit, value)) + ')' if isinstance(value, list) else str(value)


def arithmetic():
    names = {'fn2-checkpoint-map-page-count', 'fn2-checkpoint-ticket-demand',
             'fn2-checkpoint-capacity-demand', 'fn2-checkpoint-capacity-required'}
    output = []
    for name in ('checkpoint-map-format', 'checkpoint-capacity'):
        for source in lisp_source.forms((ROOT / 'books' / (name + '.lisp')).read_text()):
            form = lisp_source.read_sexp(source)
            if isinstance(form, list) and form[:1] == ['defun'] and form[1] in names:
                output.append(emit(form[:3] + [f for f in form[3:] if f[:1] != ['declare']]))
    return '\n'.join(output)


@unittest.skipUnless(shutil.which('sbcl'), 'source arithmetic control requires SBCL')
class CapacitySourceTests(unittest.TestCase):
    def run_source(self, source):
        script = '''
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun nfix (x) (if (natp x) x 0))
(defun zp (x) (not (and (integerp x) (< 0 x))))
(defvar *fn2-checkpoint-map-slots*)
(defvar *fn2-checkpoint-arena-slots*)
(defvar *fn2-checkpoint-allocation-records-per-ticket*)
''' + source + '''
; Parameterized packing controls, not guessed production codec widths.
(dolist (packing '((13 7 5) (2 2 2) (100 100 25)))
 (let ((*fn2-checkpoint-map-slots* (first packing))
       (*fn2-checkpoint-arena-slots* (second packing))
       (*fn2-checkpoint-allocation-records-per-ticket* (third packing)))
  (loop for extents from 1 to 80 do
   (loop for base from 0 to 40 do
    (let* ((maps (max 1 (ceiling extents (first packing))))
           (expected
            (or (loop for tickets from 1 to extents
                  for arena = (max 1 (ceiling tickets (second packing)))
                  when (= tickets (+ 1 (ceiling (+ base maps arena) (third packing))))
                  return (+ base maps arena tickets)) 0)))
     (assert (= expected (fn2-checkpoint-capacity-required base extents))))))))
'''
        return subprocess.run(['sbcl', '--noinform', '--disable-debugger', '--script', '/dev/stdin'],
                              input=script, text=True, capture_output=True, timeout=30)

    def test_exact_source_fixedpoint(self):
        result = self.run_source(arithmetic())
        self.assertEqual(result.returncode, 0, result.stderr[-2000:])

    def test_omitted_arena_allocation_is_detected(self):
        original = arithmetic()
        mutant = original.replace(
            '(fn2-checkpoint-map-page-count (nfix tickets) *fn2-checkpoint-arena-slots*)', '0')
        self.assertNotEqual(original, mutant)
        self.assertNotEqual(self.run_source(mutant).returncode, 0)

    def test_actual_profile_and_planner_consume_shared_arithmetic(self):
        plan = (ROOT / 'books/checkpoint-plan.lisp').read_text()
        kind = (ROOT / 'books/checkpoint-kind.lisp').read_text()
        self.assertIn('(include-book "checkpoint-capacity")', plan)
        self.assertIn('(next (fn2-checkpoint-ticket-demand ', plan)
        self.assertNotIn('(defun fn2-checkpoint-ticket-demand', plan)
        self.assertIn('(fn2-checkpoint-minimum-capacityp (fn2-b-capacity :extent-slots 16 profile))', kind)

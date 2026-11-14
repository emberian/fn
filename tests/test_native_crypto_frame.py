"""Execute the actual zero-prefix qualifier with a correct-count ABI fault.

ACL2's reference body and the host's qualifier/wrapper are read from source.
Only the pool representation and foreign-call boundary are test substitutes;
this is a qualification regression, not a proof of the C implementation.
"""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as rw


def source_parts():
    native = rw.parse(ROOT / 'host/b3-native.lisp')
    qualifier = [m for m in rw.match('(dolist (n _) ?*body)', native.forms)
                 if 'fn2-b3-native-zero-prefix' in native.text[m.start:m.end]]
    assert len(qualifier) == 1
    wrapper = rw.match('_', native.forms, deep=False, head='defun',
                       name='fn2-b3-native-zero-prefix')
    assert len(wrapper) == 1
    reference = rw.parse(ROOT / 'books/format-check.lisp')
    function = rw.match('_', reference.forms, deep=False, head='defun',
                        name='fn2-fc-zero-prefix')[0].node
    # XARGS is ACL2 admission syntax; the unchanged reference body runs in SBCL.
    reference_text = '(' + ' '.join(rw.emit(item) for i, item in enumerate(function.items)
                                    if i != 3) + ')'
    return (native.text[wrapper[0].start:wrapper[0].end], reference_text,
            native.text[qualifier[0].start:qualifier[0].end])


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for native frame controls')
class NativeCryptoFrame(unittest.TestCase):
    def run_qualifier(self, corrupt):
        wrapper, reference, qualifier = source_parts()
        program = f'''
          (defconstant *fn2-pool-datai* 0)
          (defun zp (n) (<= n 0))
          (defun fn2-pool-datai (i pool) (aref (svref pool 0) i))
          {reference}
          (defparameter *pool*
            (vector (make-array 8192 :element-type '(unsigned-byte 8) :initial-element 0)
                    (vector 91 92) 17))
          (defun fn2-b3-native-reference (name)
            (assert (eq name 'fn2-fc-zero-prefix)) #'fn2-fc-zero-prefix)
          (define-condition fn2-b3-native-refused (error)
            ((detail :initarg :detail :reader native-detail))
            (:report (lambda (c s) (princ (native-detail c) s))))
          (defun fn2-b3-%zero (sap n)
            (prog1 (fn2-fc-zero-prefix 3 n *pool*)
              {'(setf (sb-sys:sap-ref-8 sap n) (logxor 1 (sb-sys:sap-ref-8 sap n)))' if corrupt else ''}))
          {wrapper}
          (handler-case
            (let* ((pool *pool*) (bytes (svref pool 0)))
              {qualifier}
              (format t "FRAME_QUALIFICATION_OK~%") (sb-ext:exit :code 0))
            (error (c) (format t "FRAME_QUALIFICATION_REJECTED ~a~%" c)
                       (sb-ext:exit :code 1)))
        '''
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lisp') as script:
            script.write(program)
            script.flush()
            return subprocess.run(['sbcl', '--script', script.name], text=True,
                                  capture_output=True, timeout=10)

    def test_correct_result_and_unchanged_pool_pass(self):
        result = self.run_qualifier(False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('FRAME_QUALIFICATION_OK', result.stdout)

    def test_correct_count_cannot_hide_write_beyond_span(self):
        # The primitive returns the real reference count, then toggles byte N,
        # outside [0,N). This includes the empty-span case; no truncation occurs.
        result = self.run_qualifier(True)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('zero-prefix result or pool frame', result.stdout)
        self.assertNotIn('FRAME_QUALIFICATION_OK', result.stdout)


if __name__ == '__main__':
    unittest.main()

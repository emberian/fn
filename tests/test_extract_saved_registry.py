"""The saved registry keeps aliases across restore; no pool installation credit."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/extract'))
import cl


class SavedRegistryTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_restore_keeps_mutated_stobj_and_saved_alias(self):
        # A neutral one-field fixture tests the generic registry's save seam,
        # independently of any selected runtime pool schema or admission.
        ir = {'roots': [], 'boundary': [], 'functions': [],
              'stobjs': [{'name': 'ACL2::REGISTRY-FIXTURE', 'abstract': False,
                          'fields': [{'field': 'ACL2::FIELD', 'type': ['y', 'COMMON-LISP::T'],
                                      'init': ['y', 'COMMON-LISP::NIL'], 'resizable': False,
                                      'names': ['ACL2::FIELD', 'ACL2::UPDATE-FIELD', None, None, 'ACL2::FIELDP']}]}]}
        text, _ = cl.CL(ir).program()
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            (out / 'defs.lisp').write_text(text)
            driver = f'''(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_INVISIBLE" (:use))
(defpackage "ACL2_*1*_ACL2" (:use))
(load {json.dumps(str(ROOT / 'tools/extract/clruntime.lisp'))})
(load (compile-file {json.dumps(str(out / 'defs.lisp'))}))
(in-package "ACL2")
(xl-make-live-stobjs)
(defparameter *saved-registry* *xl-user-stobj-alist*)
(defparameter *saved-alias* (cdr (assoc 'registry-fixture *xl-user-stobj-alist*)))
(setf (svref *saved-alias* 0) :held)
(xl-make-live-stobjs)
(assert (eq *saved-registry* *xl-user-stobj-alist*))
(assert (eq *saved-alias* (cdr (assoc 'registry-fixture *xl-user-stobj-alist*))))
(sb-ext:save-lisp-and-die {json.dumps(str(out / 'saved.core'))}
  :toplevel (lambda ()
              (xl-make-live-stobjs)
              (assert (eq *saved-registry* *xl-user-stobj-alist*))
              (assert (eq *saved-alias* (cdr (assoc 'registry-fixture *xl-user-stobj-alist*))))
              (assert (eq (svref *saved-alias* 0) :held))
              (setf (svref *saved-alias* 0) :completed)
              (assert (eq (svref (cdr (assoc 'registry-fixture *xl-user-stobj-alist*)) 0)
                          :completed))
              (format t "PASS saved registry identity and held field~%")
              (sb-ext:exit :code 0)))
'''
            (out / 'save.lisp').write_text(driver)
            save = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger',
                                   '--script', str(out / 'save.lisp')], capture_output=True, text=True, timeout=30)
            self.assertEqual(save.returncode, 0, save.stdout + save.stderr)
            restored = subprocess.run([shutil.which('sbcl'), '--core', str(out / 'saved.core'),
                                       '--noinform', '--disable-debugger'], capture_output=True, text=True, timeout=30)
            self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
            self.assertIn('PASS saved registry identity and held field', restored.stdout)


if __name__ == '__main__':
    unittest.main()

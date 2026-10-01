"""Property snapshot semantics; actual ACL2 export admission is separate."""
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class WorldSnapshotTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_presence_defaults_and_installation_refusal(self):
        source = '''(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_INVISIBLE" (:use))
(defpackage "ACL2_*1*_ACL2" (:use))
(load "RUNTIME")
(in-package "ACL2")
(assert (handler-case (progn (table-alist 'fn-interfaces (w nil)) nil) (error () t)))
(xl-set-world-snapshot '((f (formals) (guard quote t) (stobjs-in) (stobjs-out nil)
                           (symbol-class . :common-lisp-compliant))
                         (st (:xl-stobj-creator . create-st) (:xl-stobj-recognizer . stp))
                         (fn-interfaces (table-alist (f :class :common-lisp-compliant)))))
(assert (null (getpropc 'f 'formals :missing)))
(assert (eq (getpropc 'f 'unknown :missing) :missing))
(assert (eq (getpropc 'missing 'formals :missing) :missing))
(assert (equal (guard 'f nil (w nil)) '(quote t)))
(assert (eq (symbol-class 'f (w nil)) :common-lisp-compliant))
(assert (eq (symbol-class 'missing (w nil)) :missing-world-metadata))
(assert (equal (stobjs-out 'f (w nil)) '(nil)))
(assert (eq (get-stobj-creator 'st (w nil)) 'create-st))
(assert (eq (get-stobj-recognizer 'st (w nil)) 'stp))
(assert (equal (table-alist 'fn-interfaces (w nil)) '((f :class :common-lisp-compliant))))
(xl-set-props '((f nil nil (quote t))))
(assert (handler-case (progn (table-alist 'fn-interfaces (w nil)) nil) (error () t)))
(format t "PASS snapshot presence/NIL/default/legacy fail-closed~%")
'''.replace('RUNTIME', str(ROOT / 'tools/extract/clruntime.lisp'))
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / 'snapshot.lisp'
            script.write_text(source)
            run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger',
                                  '--script', str(script)], capture_output=True, text=True, timeout=30)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn('PASS snapshot presence/NIL/default/legacy fail-closed', run.stdout)


if __name__ == '__main__':
    unittest.main()

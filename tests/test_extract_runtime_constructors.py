"""Actual tagged stock-world constructor IR; layout differential, not allocation proof."""
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools/extract"))
import cl


class RuntimeConstructorTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required for raw constructor differential")
    def test_actual_three_field_pool_and_congruent_rx_compiled_layout(self):
        ir = json.loads((ROOT / "tests/extract/runtime-constructors.json").read_text())
        text, inventory = cl.CL(ir).program()
        self.assertEqual(inventory["host-defined"], [])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / "constructors.lisp").write_text(text)
            driver = f'''(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_INVISIBLE" (:use))
(defpackage "ACL2_*1*_ACL2" (:use))
(load "{ROOT}/tools/extract/clruntime.lisp")
(multiple-value-bind (output warnings failure)
    (compile-file "{path}/constructors.lisp" :output-file "{path}/constructors.fasl")
  (declare (ignore warnings)) (assert (not failure)) (load output))
(in-package "ACL2")
(dolist (name '(create-fn-page-read-pool create-fn-octets$c create-fn-octets-rx))
  (assert (compiled-function-p (symbol-function name))))
(let ((pool (create-fn-page-read-pool)) (rx (create-fn-octets-rx))
      (foundation (create-fn-octets$c)))
  (assert (and (simple-vector-p pool) (= (length pool) 3)
               (equal (coerce pool 'list) '(nil :uninitialized nil))))
  (dolist (buffer (list rx foundation))
    (assert (and (simple-vector-p buffer) (= (length buffer) 2)
                 (typep (svref buffer 0) '(simple-array (unsigned-byte 8) (*)))
                 (zerop (length (svref buffer 0))) (eql (svref buffer 1) 0))))
  (assert (not (eq rx foundation)))
  (assert (not (eq (svref rx 0) (svref foundation 0)))))
(format t "PASS current stock constructor layouts and fresh RX backing~%")
'''
            (path / "driver.lisp").write_text(driver)
            run = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger",
                                  "--script", str(path / "driver.lisp")],
                                 capture_output=True, text=True, timeout=30)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn("PASS current stock constructor", run.stdout)


if __name__ == "__main__":
    unittest.main()

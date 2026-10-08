"""tools/extract/clruntime.lisp's runtime entries for ACL2's printer path: warning1 renders the
"Guards" warning maybe-warn-for-guard-body passes it (the text the image prints, without fmt's line
filling), stays silent when WARNING is in inhibit-output-lst, and wormhole-er halts naming the
function instead of printing through ERROR-FMS."""
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = ROOT / "tools" / "extract" / "clruntime.lisp"

# The string and alist maybe-warn-for-guard-body passes (ACL2 8.7 interface-raw.lisp:1889).
DRIVER = r"""
(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_INVISIBLE" (:use))
(defpackage "ACL2_GLOBAL_ACL2" (:use))
(in-package "ACL2")
(defun global-symbol (x) (intern (symbol-name x) "ACL2_GLOBAL_ACL2"))
(handler-bind ((warning #'muffle-warning))
  (load (compile-file "%(runtime)s" :output-file "%(fasl)s")))
(in-package "ACL2")
(defparameter *str* "Guard-checking will be inhibited for some ~
                              recursive calls, including ~x0; see :DOC ~
                              guard-checking-inhibited.")
(format t "<<")
(warning1 'top-level "Guards" *str* (list (cons #\0 'fn-ast-render-window-aux)) *the-live-state*)
(format t ">>~%%")
(xl-set-global 'inhibit-output-lst '(warning))
(format t "[[")
(warning1 'top-level "Guards" *str* (list (cons #\0 'fn-x)) *the-live-state*)
(format t "]]~%%")
(format t "HALT ~a~%%" (catch 'raw-ev-fncall (wormhole-er 'update-fn-x (list 1 2)) :returned))
"""

EXPECTED_WARNING = ("<<\nACL2 Warning [Guards] in TOP-LEVEL:  Guard-checking will be inhibited for some "
                    "recursive calls, including FN-AST-RENDER-WINDOW-AUX; see :DOC "
                    "guard-checking-inhibited.\n\n>>\n")


@unittest.skipUnless(shutil.which("sbcl"), "no sbcl")
class RuntimePrinterTests(unittest.TestCase):
    def test_guards_warning_inhibition_and_wormhole_halt(self):
        with tempfile.TemporaryDirectory() as directory:
            driver = Path(directory) / "driver.lisp"
            driver.write_text(DRIVER % {"runtime": RUNTIME,
                                        "fasl": Path(directory) / "clruntime.fasl"})
            done = subprocess.run(["sbcl", "--script", str(driver)], capture_output=True,
                                  text=True, timeout=600)
        self.assertEqual(done.returncode, 0, done.stderr[-2000:])
        self.assertIn(EXPECTED_WARNING, done.stdout)
        self.assertIn("[[]]\n", done.stdout)
        self.assertIn("HALT ACL2 Halted\n", done.stdout)
        self.assertIn("ACL2 Error in WORMHOLE:  UPDATE-FN-X applied to (1 2)", done.stderr)


if __name__ == "__main__":
    unittest.main()

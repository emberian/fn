"""Host counterparts call mapped primitives and retain their ACL2 guards."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools/extract"))
import cl


class PrimitiveCounterpartTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_total_len_and_guarded_addition_are_callable(self):
        true = ["q", ["y", "COMMON-LISP::T"]]
        variable = lambda name: ["v", "ACL2::" + name]
        numeric = lambda name: ["c", "ACL2::ACL2-NUMBERP", [variable(name)]]
        functions = [
            {"name": "ACL2::LEN", "kind": "defun", "formals": ["ACL2::X"],
             "class": "common-lisp-compliant", "guard": true, "body": true},
            {"name": "ACL2::BINARY-+", "kind": "defun", "formals": ["ACL2::X", "ACL2::Y"],
             "class": "common-lisp-compliant", "guard": ["c", "COMMON-LISP::IF", [numeric("X"), numeric("Y"), ["q", ["y", "COMMON-LISP::NIL"]]]],
             "body": true},
        ]
        ir = {"roots": [f["name"] for f in functions], "functions": functions,
              "boundary": [{"name": f["name"]} for f in functions], "stobjs": []}
        text, _ = cl.CL(ir).program()
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            (out / "defs.lisp").write_text(text)
            driver = f'''(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_INVISIBLE" (:use))
(defpackage "ACL2_*1*_ACL2" (:use))
(load {json.dumps(str(ROOT / "tools/extract/clruntime.lisp"))})
(load (compile-file {json.dumps(str(out / "defs.lisp"))}))
(assert (= (acl2_*1*_acl2::len '(1 2 . :tail)) 2))
(assert (= (acl2_*1*_acl2::len :atom) 0))
(assert (= (acl2_*1*_acl2::binary-+ 3 4) 7))
(assert (equal (catch 'acl2::raw-ev-fncall (acl2_*1*_acl2::binary-+ :bad 4)) "ACL2 Halted"))
(format t "PASS primitive counterparts and original guard~%")
'''
            (out / "driver.lisp").write_text(driver)
            result = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger",
                                     "--script", str(out / "driver.lisp")], capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("PASS primitive counterparts", result.stdout)
            self.assertIn("guard for the function call (BINARY-+ ...) is violated", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()

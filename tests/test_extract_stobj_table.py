"""Actual guard-verified P2 node source -> ACL2 IR -> extracted SBCL effects.

This narrow integration test uses the pooled ACL2 wrapper, never an image build.
The fixture is the provider prototype's exact node definition span (forms 3–7).
"""
import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/extract/stobj-table-provider.lisp"


@unittest.skipUnless(shutil.which("sbcl"), "SBCL unavailable")
class StobjTableTests(unittest.TestCase):
    def test_real_export_preserves_registration_reads_and_lazy_creation(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            ir = output / "provider.json"
            reference = '''
(ld "%s")
(mv-let (s id) (fn-ibp-node-left-id-read fn-ibp-node)
  (cw "OBS ~x0 ~x1 ~x2~%%" s id (fn-ibp-node-children-count fn-ibp-node)))
(fn-ibp-node-add-left 17 fn-ibp-node)
(mv-let (s id) (fn-ibp-node-left-id-read fn-ibp-node)
  (cw "OBS ~x0 ~x1 ~x2~%%" s id (fn-ibp-node-children-count fn-ibp-node)))
(fn-ibp-node-add-left 99 fn-ibp-node)
(mv-let (s id) (fn-ibp-node-left-id-read fn-ibp-node)
  (cw "OBS ~x0 ~x1 ~x2~%%" s id (fn-ibp-node-children-count fn-ibp-node)))
(ld "tools/extract/frontend.lisp")
(xt-extract '(fn-ibp-node-add-left fn-ibp-node-left-id-read
              fn-ibp-node-children-count) "%s" state)
:q
(sb-ext:exit :code 0)
''' % (FIXTURE, ir)
            acl2 = subprocess.run([str(ROOT / "tools/acl2"), "--timeout", "90"],
                                  input=reference, cwd=ROOT, capture_output=True, text=True, timeout=120)
            self.assertEqual(acl2.returncode, 0, acl2.stderr)
            self.assertNotIn("ACL2 Error", acl2.stdout, acl2.stdout[-3000:])
            observations = [":UNAVAILABLE NIL 0", ":PRESENT 17 1", ":PRESENT 17 1"]
            for result in observations:
                self.assertIn("OBS " + result, acl2.stdout)
            data = json.loads(ir.read_text())
            self.assertIn("ACL2::FN-IBP-NODE-RIGHT", data["stobj_names"])
            # RIGHT is a valid world name even though its creator is outside
            # this executable closure. Registry validity is not reachability.
            self.assertNotIn("ACL2::FN-IBP-NODE-RIGHT", [s["name"] for s in data["stobjs"]])
            defs = output / "defs.lisp"
            generated = subprocess.run(["python3", str(ROOT / "tools/extract/cl.py"), str(ir),
                                        "--out", str(defs), "--inventory", str(output / "inventory.json")],
                                       capture_output=True, text=True)
            self.assertEqual(generated.returncode, 0, generated.stderr)
            driver = output / "driver.lisp"
            driver.write_text('''
(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_INVISIBLE" (:use))
(defpackage "ACL2_*1*_ACL2" (:use))
(load "%s") (load "%s")
(in-package "ACL2")
(xl-make-live-stobjs)
(defvar *creates* 0)
(let ((original (symbol-function 'xl-make-stobj-table)))
  (setf (symbol-function 'xl-make-stobj-table)
        (lambda (&rest args) (incf *creates*) (apply original args))))
(let ((node (cdr (assoc 'fn-ibp-node *xl-user-stobj-alist*))))
  (flet ((observe ()
           (multiple-value-bind (s id) (fn-ibp-node-left-id-read node)
             (format t "OBS ~s ~s ~s~%%" s id (fn-ibp-node-children-count node)))))
    (observe)
    (assert (= *creates* 0))
    (assert (null (fn-ibp-node-children-boundp 'fn-ibp-node-right node)))
    (fn-ibp-node-add-left 17 node) (observe)
    (assert (= *creates* 1))
    (dotimes (i 1000) (fn-ibp-node-left-id-read node))
    (fn-ibp-node-add-left 99 node) (observe)
    (assert (= *creates* 1))))
''' % (ROOT / "tools/extract/clruntime.lisp", defs))
            backend = subprocess.run(["sbcl", "--script", str(driver)],
                                     capture_output=True, text=True, timeout=60)
            self.assertEqual(backend.returncode, 0, backend.stderr[-3000:])
            self.assertEqual([line[4:] for line in backend.stdout.splitlines() if line.startswith("OBS ")],
                             observations)


@unittest.skipUnless(shutil.which("sbcl"), "SBCL unavailable")
class RecursiveStobjTableTests(unittest.TestCase):
    def test_lazy_creator_is_only_a_matching_stobj_binding(self):
        import sys
        sys.path.insert(0, str(ROOT / "tools/extract"))
        import cl
        import chicken
        ir = json.loads((ROOT / "tests/extract/stobj-table-path-core.json").read_text())
        key = "ACL2::FN-IBP-NODE-LEFT"
        actual = ["c", "ACL2::FN-IBP-NODE-CHILDREN-GET",
                  [["q", ["y", key]], ["v", "ACL2::NODE"],
                   ["c", "ACL2::CREATE-FN-IBP-NODE-LEFT", []]]]
        for backend in (cl.CL(ir), chicken.Backend(ir)):
            self.assertIsNotNone(backend.stobj_table_binding(key, actual))
            self.assertIsNone(backend.stobj_table_binding("ACL2::OTHER", actual))
        # Direct calls keep ordinary argument evaluation. The stock lazy
        # rewrite belongs to the translated stobj-let binding pattern.
        self.assertNotIn("(or ", cl.CL(ir).emit(actual, {}, 1, "raw"))
        scheme = chicken.Backend(ir)
        scheme.counter = 0
        self.assertNotIn("%table", scheme.emit(actual, {}, 1))

    def test_guarded_recursive_kernel_matches_all_stock_outputs(self):
        import importlib.util
        module = importlib.util.spec_from_file_location(
            "path_drivers", ROOT / "tests/extract/stobj_table_path_drivers.py")
        drivers = importlib.util.module_from_spec(module)
        module.loader.exec_module(drivers)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            defs = output / "defs.lisp"
            generated = subprocess.run(
                ["python3", str(ROOT / "tools/extract/cl.py"),
                 str(ROOT / "tests/extract/stobj-table-path-core.json"),
                 "--out", str(defs), "--inventory", str(output / "inventory.json")],
                capture_output=True, text=True)
            self.assertEqual(generated.returncode, 0, generated.stderr)
            drivers.generate(ROOT / "tests/extract/stobj-table-path-stock.txt",
                             output / "driver", defs, ROOT / "tools/extract/clruntime.lisp")
            result = subprocess.run(["sbcl", "--script", str(output / "driver.lisp")],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(len(result.stdout.splitlines()), 10)
            self.assertTrue(all(line.startswith("PASS ") for line in result.stdout.splitlines()))


if __name__ == "__main__":
    unittest.main()

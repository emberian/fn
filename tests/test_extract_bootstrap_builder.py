"""Image-only worker setup must precede actual bootstrap capture."""
import importlib.util
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "tools/extract/core_build.py"
SPEC = importlib.util.spec_from_file_location("bootstrap_core_build", SCRIPT)
BUILDER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILDER)

LOADS = '''(load "host/native/runtime-participants.lisp")
(load "host/native/runtime-image-policy.lisp")
(load "host/native/runtime-bootstrap.lisp")
'''
INSTALL = ("(let* ((pool (fnn-live-page-read-pool))\n"
           "       (gate (cl-user::fnn-runtime-participants-install-for-image pool)))\n"
           "  (cl-user::fnn-runtime-image-policy-prepare pool gate))\n")
REGISTER = ("(cl-user::fnn-runtime-image-policy-register-image-hook)\n"
            "(cl-user::fnn-runtime-participants-register-image-hooks)\n")
PREPARE = "(fnn-runtime-bootstrap-image-prepare)\n"


class BootstrapBuilderTest(unittest.TestCase):
    def generate(self, body):
        with tempfile.TemporaryDirectory() as directory:
            tree = Path(directory)
            build = tree / "selected.lisp"
            build.write_text("(progn! (set-raw-mode t)\n" + body + ")\n")
            before = build.read_bytes()
            result = BUILDER.product_block(tree, "selected.lisp")
            self.assertEqual(build.read_bytes(), before)
            return result

    def test_genuine_gate_is_captured_after_install(self):
        result = self.generate(LOADS + PREPARE)
        self.assertIn(LOADS + INSTALL + REGISTER + PREPARE, result)

    def test_complete_existing_setup_is_not_repeated(self):
        body = LOADS + INSTALL + REGISTER + PREPARE
        self.assertEqual(self.generate(body), "\n" + body)

    def test_legacy_block_has_no_new_runtime_side_effect(self):
        body = '(load "host/native/io.lisp")\n'
        self.assertEqual(self.generate(body), "\n" + body)

    def test_missing_or_late_macro_load_refuses(self):
        for body in (PREPARE, PREPARE + LOADS, LOADS.replace('(load "host/native/runtime-image-policy.lisp")\n', "") + PREPARE):
            with self.subTest(body=body), self.assertRaises(ValueError):
                self.generate(body)

    def test_partial_repeated_or_different_pool_setup_refuses(self):
        for setup in (INSTALL, REGISTER, INSTALL + REGISTER + REGISTER,
                      INSTALL.replace("fnn-live-page-read-pool", "another-pool") + REGISTER):
            with self.subTest(setup=setup), self.assertRaises(ValueError):
                self.generate(LOADS + setup + PREPARE)

    def test_reordered_and_duplicate_capture_refuse(self):
        for body in ("\n".join(reversed(LOADS.splitlines())) + "\n" + PREPARE,
                     LOADS + PREPARE + PREPARE, LOADS + REGISTER + INSTALL + PREPARE):
            with self.subTest(body=body), self.assertRaises(ValueError):
                self.generate(body)

    def test_policy_setup_missing_or_changed_refuses(self):
        body = LOADS + INSTALL + REGISTER + PREPARE
        for altered in (body.replace("fnn-runtime-image-policy-prepare pool gate", "fnn-runtime-image-policy-prepare pool nil"),
                        body.replace("(cl-user::fnn-runtime-image-policy-register-image-hook)\n", ""),
                        body.replace(REGISTER, REGISTER + REGISTER)):
            with self.subTest(body=altered), self.assertRaises(ValueError):
                self.generate(altered)

    def test_changed_prepare_arguments_refuse(self):
        with self.assertRaises(ValueError):
            self.generate(LOADS + "(fnn-runtime-bootstrap-image-prepare t)\n")


if __name__ == "__main__":
    unittest.main()

"""Build selection safety only; no positive runtime allocation qualification."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "operation_source_driver", Path(__file__).resolve().parents[1] / "tools/operation_source_driver.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class DriverTests(unittest.TestCase):
    def test_actual_source_call_not_host_charge(self):
        text = module.driver([{"kind": ":owner-control-inspect", "book": "operation-diagnostics-source",
                               "producer": "fn-owner-inspect-compiled-source"}])
        self.assertIn("(fn-owner-inspect-compiled-source :owner-control-inspect)", text)
        self.assertIn("(list :owner-control-inspect status family roles prs)", text)
        self.assertIn("'(nil nil nil nil)", text)
        self.assertIn(":common-lisp-compliant", text)
        self.assertNotIn("qualified", text.splitlines()[-1])
    def test_no_readiness_or_arithmetic_input(self):
        row = {"kind": ":owner-control-inspect", "book": "operation-diagnostics-source",
               "producer": "fn-owner-inspect-compiled-source", "qualified": True}
        with self.assertRaises(ValueError):
            module.driver([row])
    def test_injection_duplicate_and_self_source_refused(self):
        row = {"kind": ":owner-control-inspect", "book": "operation-diagnostics-source",
               "producer": "fn-owner-inspect-compiled-source"}
        for changed in [dict(row, kind=":x) (value :forged)"),
                        dict(row, producer="fn-runtime-operation-compiled-source"),
                        dict(row, book='source") (value :forged)')]:
            with self.assertRaises(ValueError):
                module.driver([changed])
        with self.assertRaises(ValueError):
            module.driver([row, row])

if __name__ == "__main__":
    unittest.main()

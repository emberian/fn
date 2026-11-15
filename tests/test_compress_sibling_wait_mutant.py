"""Source transformation controls; no ACL2, native build or Git history needed."""
from pathlib import Path
import importlib.util
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("sibling_mutant", ROOT / "tests/compress_sibling_wait_mutant.py")
MUTANT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MUTANT)

# Actual pre-fix implementation, captured at 694b73f6e during authoring.
ORIGINAL_WAIT = "(defun fn2-compress-record-stack-wait\n (fn2-compress-operation fn2-compress-transport fn2-tls-transport fn2-tls-record)\n (declare (xargs :stobjs (fn2-compress-operation fn2-compress-transport fn2-tls-transport fn2-tls-record)\n  :verify-guards nil\n  :guard (and (fn2-compress-operation-wfp fn2-compress-operation)\n              (fn2-compress-transport-wfp fn2-compress-transport)\n              (fn2-tls-transport-wfp fn2-tls-transport) (fn2-tls-record-wfp fn2-tls-record))))\n (if (and (= (fn2-compress-operation-rows fn2-compress-operation) 1)\n          (= (fn2-compress-transport-rows fn2-compress-transport) 1)\n          (fn2-compress-transport-match-p\n           (fn2-compress-operation-cap 0 fn2-compress-operation)\n           (fn2-compress-operation-nonce 0 fn2-compress-operation)\n           (fn2-compress-operation-slot 0 fn2-compress-operation)\n           (fn2-compress-operation-generation 0 fn2-compress-operation)\n           (fn2-compress-operation-pending-serial 0 fn2-compress-operation) fn2-compress-transport)\n          (member-equal (fn2-compress-transport-pending 0 fn2-compress-transport) '(5 6))\n          (fn2-tls-transport-selected-p\n           (fn2-compress-operation-cap 0 fn2-compress-operation)\n           (fn2-compress-operation-nonce 0 fn2-compress-operation) fn2-tls-transport))\n     (fn2-tls-record-wait fn2-tls-transport fn2-tls-record)\n   (fn2-compress-record-wait fn2-compress-operation)))"


class SiblingWaitMutation(unittest.TestCase):
    def test_reconstructed_ast_is_exact_historical_implementation(self):
        source = (ROOT / "books/compress-close.lisp").read_text()
        self.assertEqual(MUTANT.original_wait_ast(source), MUTANT.read_forms(ORIGINAL_WAIT)[0])

    def test_all_emitted_forms_read_and_preserve_negative_assertion(self):
        emitted = list(MUTANT.mutant_forms())
        self.assertEqual(len(emitted), 6)
        self.assertTrue(all(len(MUTANT.read_forms(form)) == 1 for form in emitted))
        self.assertEqual(emitted[-1], "(assert-event (not (fn2-compress-spinning-owner-check)))")
        self.assertNotIn("subprocess", (ROOT / "tests/compress_sibling_wait_mutant.py").read_text())


if __name__ == "__main__":
    unittest.main()

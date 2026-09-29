"""tools/host_check.py --load: the raw host files' load check without an image build.

The classification is tested on a transcript; one case loads scratch raw
files into the real ACL2 (when one is on PATH) and requires each seeded
fault -- a call with the wrong arity, a macro used above its definition, a
function nothing defines, a form that errors -- to be named, and a call
into the certified world to be counted, not failed.
"""
from __future__ import annotations

import contextlib
import io
import pathlib
import shutil
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import host_check  # noqa: E402


class ClassifyTests(unittest.TestCase):
    WORLD = "(defun fn-outcome-code (x) x)\n(defconst *fn-lg-genesis* 1)\n"

    def classify(self, transcript: str):
        return host_check.classify_load(transcript, host_check.world_names(self.WORLD),
                                        self.WORLD)

    def test_world_names_are_counted_and_names_defined_nowhere_fail(self):
        findings, counts, done = self.classify(
            "noise\n"
            "FNLC-FILE host/native/io.lisp\n"
            "FNLC-CALLED host/native/io.lisp #3 ACL2 FN-OUTCOME-CODE\n"
            "FNLC-NEEDS host/native/io.lisp #3 ACL2 FN-OUTCOME-CODE +FNN-EXIT-OK+\n"
            "FNLC-WARN undefined variable: ACL2::+FNN-EXIT-OK+\n"
            "FNLC-WARN The variable X is defined but never used.\n"
            "FNLC-UNDEFINED variable ACL2 +FNN-EXIT-OK+\n"
            "FNLC-UNDEFINED variable ACL2 *FN-LG-GENESIS*\n"
            "FNLC-UNDEFINED function ACL2 FNN-TYPO\n"
            "FNLC-DONE\n")
        self.assertTrue(done)
        self.assertEqual(findings, ["undefined function fnn-typo: no raw file, book or "
                                    "ld host file defines it"])
        self.assertEqual(counts, {"files": 1, "world": 2, "world_calls": 1, "warnings": 1})

    def test_a_load_time_constant_of_the_world_is_the_worlds(self):
        # Lane generators G5: host/native/mux.lisp's defconstant reads
        # books/profile-limits.lisp's constant; loaded alone it is unbound,
        # and the constant it defines is the world's too.  An unbound name
        # no book defines still fails.
        definers = {"+fnn-mux-loops+": "host/native/mux.lisp",
                    "+fnn-mux-typo+": "host/native/mux.lisp"}
        findings, counts, _ = host_check.classify_load(
            "FNLC-FILE host/native/mux.lisp\n"
            "FNLC-ERROR host/native/mux.lisp #2 (DEFCONSTANT +FNN-MUX-LOOPS+): "
            "The variable *FN-LG-GENESIS* is unbound.\n"
            "FNLC-ERROR host/native/mux.lisp #3 (DEFCONSTANT +FNN-MUX-TYPO+): "
            "The variable *FN-NO-SUCH* is unbound.\n"
            "FNLC-UNDEFINED variable ACL2 +FNN-MUX-LOOPS+\n"
            "FNLC-DONE\n",
            host_check.world_names(self.WORLD), self.WORLD, definers)
        self.assertEqual(findings, ["error: host/native/mux.lisp #3 (DEFCONSTANT +FNN-MUX-TYPO+): "
                                    "The variable *FN-NO-SUCH* is unbound."])
        self.assertEqual(counts["world_calls"], 1)
        self.assertEqual(counts["world"], 1)

    def test_a_raw_function_a_comment_mentions_is_not_the_worlds(self):
        # Batch AX: fnn-control-live-status, defined only in the raw
        # host/native/control.lisp, was counted as the world's because an ld
        # host file's comment spells it; the DTN image does not load it.
        world = self.WORLD + "; the owner answers (fnn-control-live-status)\n"
        definers = {"fnn-control-live-status": "host/native/control.lisp",
                    "fn-outcome-code": "host/native/io.lisp"}
        findings, counts, _ = host_check.classify_load(
            "FNLC-FILE host/native/operator.lisp\n"
            "FNLC-CALLED host/native/operator.lisp #4 ACL2 FNN-CONTROL-LIVE-STATUS\n"
            "FNLC-UNDEFINED function ACL2 FNN-CONTROL-LIVE-STATUS\n"
            "FNLC-UNDEFINED function ACL2 FN-OUTCOME-CODE\n"
            "FNLC-DONE\n",
            host_check.world_names(world), world, definers)
        self.assertEqual(findings, [
            "load-time call of undefined fnn-control-live-status (host/native/operator.lisp "
            "#4), defined in host/native/control.lisp, which this build does not load",
            "undefined function fnn-control-live-status: defined in host/native/control.lisp, "
            "which this build does not load (a call reaching it faults at run time)"])
        # A raw file may also define a name a book defines (a raw
        # replacement): that one stays the world's.
        self.assertEqual(counts["world"], 1)

    def test_arity_macro_order_and_errors_fail(self):
        findings, _, done = self.classify(
            "FNLC-FILE host/native/a.lisp\n"
            "FNLC-WARN The function FNN-TWO is called with one argument, but wants "
            "exactly two.\n"
            "FNLC-WARN FNN-MAC is being redefined as a macro when it was previously "
            "assumed to be a function.\n"
            "FNLC-ERROR host/native/a.lisp #9 (DEFVAR *X*): division by zero\n"
            "FNLC-CALLED host/native/a.lisp #10 ACL2 FNN-NOWHERE\n"
            "FNLC-NEEDS host/native/a.lisp #10 ACL2 FNN-NOWHERE *Y*\n")
        self.assertFalse(done)
        self.assertEqual(len(findings), 4)
        self.assertTrue(findings[0].startswith("arity (in or before host/native/a.lisp)"))
        self.assertTrue(findings[1].startswith("macro used before its definition"))
        self.assertTrue(findings[2].startswith("error: host/native/a.lisp #9"))
        self.assertIn("fnn-nowhere", findings[3])

    def test_the_raw_order_is_build_lisps_and_skips_comments(self):
        order = host_check.raw_load_order()
        self.assertEqual(order[:2], ["host/native/crypto.lisp", "host/native/io.lisp"])
        self.assertEqual(len(order), len(set(order)))


@unittest.skipUnless(shutil.which("acl2"), "no acl2 on PATH")
class RealLoadTests(unittest.TestCase):
    def test_each_seeded_fault_is_named_and_the_world_is_not(self):
        scratch = ROOT / "build" / "host-check-load-test"
        scratch.mkdir(parents=True, exist_ok=True)
        self.addCleanup(shutil.rmtree, scratch, True)
        rel = scratch.relative_to(ROOT).as_posix()
        (scratch / "a.lisp").write_text(
            "(defun fnn-early (x) (fnn-mac (x) 1))\n"
            "(defun fnn-two (a b) (+ a b))\n"
            "(defun fnn-call () (fnn-two 1))\n"
            "(defun fnn-typo-caller () (fnn-defined-nowhere 3))\n"
            "(defconstant +fnn-ok+ (fn-outcome-code :ok))\n"
            "(defun fnn-uses-world () (list +fnn-ok+ (fn-outcome-code :refused)))\n")
        (scratch / "b.lisp").write_text(
            "(defmacro fnn-mac (args &body b) `(let ,(mapcar (lambda (a) (list a 0)) args) ,@b))\n"
            "(defvar *fnn-broken* (car 5))\n"
            "(defun fnn-fine (x) (fnn-two x x))\n")
        (scratch / "build.lisp").write_text(
            f'(progn! (set-raw-mode t)\n  (load "{rel}/a.lisp")\n  ; (load "{rel}/c.lisp")\n'
            f'  (load "{rel}/b.lisp"))\n')
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = host_check.main(["--load", "--build", f"{rel}/build.lisp"])
        text = out.getvalue()
        self.assertEqual(code, 1, text)
        self.assertIn("2 of 2 raw files loaded", text)
        self.assertIn("FAIL arity", text)
        self.assertIn("FNN-TWO is called with one argument", text)
        self.assertIn("FAIL macro used before its definition", text)
        self.assertIn("undefined function fnn-defined-nowhere", text)
        self.assertIn(f"FAIL error: {rel}/b.lisp #2 (DEFVAR *FNN-BROKEN*)", text)
        # fn-outcome-code is books/outcome-class's: counted, never failed,
        # and +fnn-ok+, which needed it at load time, with it.
        self.assertNotIn("fn-outcome-code", text.lower().split("host_check --load:")[0])
        self.assertNotIn("+fnn-ok+", text.lower())
        self.assertEqual(text.count("FAIL"), 4, text)

    def test_the_tree_loads_clean(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = host_check.main(["--load"])
        self.assertEqual(code, 0, out.getvalue())

    def test_the_dtn_tree_loads_clean(self):
        # Batch AX: the DTN image loaded operator.lisp, which called 21
        # functions only files the DTN build does not load define.
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = host_check.main(["--load", "--build", "host/native/build-dtn.lisp"])
        self.assertEqual(code, 0, out.getvalue())


if __name__ == "__main__":
    unittest.main()

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
class WorldTests(unittest.TestCase):
    """Item 40: --load over the build's certified prefix, saying which world."""

    def scratch(self) -> tuple[pathlib.Path, str]:
        scratch = ROOT / "build" / "host-check-world-test"
        scratch.mkdir(parents=True, exist_ok=True)
        self.addCleanup(shutil.rmtree, scratch, True)
        rel = scratch.relative_to(ROOT).as_posix()
        (scratch / "build.lisp").write_text(
            f'(include-book "{rel}/umbrella")\n(ld "{rel}/h.lisp" :ld-error-action :error)\n'
            f'(defttag :x)\n(progn! (set-raw-mode t) (load "{rel}/r.lisp"))\n')
        return scratch, rel

    def test_certified_prefix_is_loaded_first_and_named(self):
        scratch, rel = self.scratch()
        (scratch / "umbrella.cert").write_text("")
        forms, note = host_check.choose_world(f"{rel}/build.lisp", pathlib.Path("acl2"),
                                              bare=False)
        self.assertIsNotNone(forms)
        self.assertIn("CERTIFIED UMBRELLA", note)
        self.assertIn(f"{rel}/umbrella and 1 host lds", note)
        session = host_check.world_session(forms)
        self.assertIn(f'(value-triple (cw "{host_check.WORLD_LD} ~s0~%" "{rel}/h.lisp"))',
                      session)
        self.assertTrue(session.rstrip().endswith(f'(cw "{host_check.WORLD_OK}~%"))'))
        self.assertNotIn("defttag", session.lower())

    def test_missing_certificates_fall_back_bare_and_say_why(self):
        _, rel = self.scratch()
        calls = []

        class Done:
            stdout, stderr, returncode = "install-set: missing 1", "", 0

        def runner(argv):
            calls.append(argv)
            return Done()
        forms, note = host_check.choose_world(f"{rel}/build.lisp", pathlib.Path("acl2"),
                                              bare=False, runner=runner)
        if host_check.certificate_cache() is None:
            self.assertIn("no certificate cache", note)
        else:
            self.assertEqual(calls[0][-2:], ["install-set", f"{rel}/umbrella"])
            self.assertIn("have no certificate here", note)
        self.assertIsNone(forms)
        self.assertIn("BARE ACL2", note)
        self.assertIn("NOT evaluated", note)
        _, note = host_check.choose_world(f"{rel}/build.lisp", pathlib.Path("acl2"),
                                          bare=True)
        self.assertIn("BARE ACL2 (--bare)", note)

    def test_require_world_is_not_run_when_the_umbrella_is_absent(self):
        _, rel = self.scratch()
        (ROOT / rel / "r.lisp").write_text("(defun fnn-r () 1)\n")
        err = io.StringIO()
        original = host_check.install_world
        host_check.install_world = lambda forms, acl2, runner=None: "no cache (test)"
        self.addCleanup(setattr, host_check, "install_world", original)
        original_exe = host_check.executable
        host_check.executable = lambda: pathlib.Path("/bin/true")
        self.addCleanup(setattr, host_check, "executable", original_exe)
        original_stale = host_check.world_stale
        host_check.world_stale = lambda runner=None: []
        self.addCleanup(setattr, host_check, "world_stale", original_stale)
        with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
            code = host_check.main(["--load", "--require-world", "--build",
                                    f"{rel}/build.lisp"])
        self.assertEqual(code, 2)
        self.assertIn("NOT RUN -- BARE ACL2 -- the certified umbrella is not available: "
                      "no cache (test)", err.getvalue())

    def test_a_certificate_that_will_not_load_is_trouble_not_a_finding(self):
        output = ("ABORTING from raw Lisp\nError:  There is a problem with the certificate\n"
                  'ACL2 Error [Failure] in ( INCLUDE-BOOK "post-identity-catalog" ...):\n'
                  'ACL2 Error [Failure] in ( INCLUDE-BOOK "books/image-world" ...):\n')
        self.assertEqual(host_check.certificate_trouble(output),
                         "include-book post-identity-catalog failed on its certificate")
        self.assertEqual(host_check.certificate_trouble(
            f"{host_check.WORLD_OK}\n[Uncertified] later\n"), "")

    def test_certificate_trouble_reinstalls_one_set_then_falls_back(self):
        calls = []
        original = host_check.install_world
        host_check.install_world = lambda forms, acl2, runner=None: (
            calls.append(forms) or "missing 3 (test)")
        self.addCleanup(setattr, host_check, "install_world", original)
        trouble = ('ACL2 Error [Failure] in ( INCLUDE-BOOK "books/image-world" ...):\n'
                   "There is a problem with the certificate\n")
        sessions = []

        def fake_run(argv, label, **kwargs):
            sessions.append(kwargs["input"].decode())
            import subprocess as sp
            out = trouble if "INCLUDE-BOOK" in kwargs["input"].decode().upper() else \
                f"{host_check.LOAD_TAG}-DONE\n"
            return sp.CompletedProcess(argv, 0, out.encode())
        original_run = host_check.acl2_slots.run
        host_check.acl2_slots.run = fake_run
        self.addCleanup(setattr, host_check.acl2_slots, "run", original_run)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = host_check.load_check(pathlib.Path("acl2"), [], 5, None,
                                         [["include-book", "books/image-world"]], "U")
        text = out.getvalue()
        self.assertEqual(len(calls), 1)
        self.assertIn("reinstalled the prefix's roots as one set -- missing 3 (test)", text)
        self.assertIn("WORLD BARE ACL2 -- the certified umbrella did not load here", text)
        self.assertEqual(code, 0)
        self.assertEqual(len(sessions), 2)

    def test_over_the_world_a_raw_override_of_a_book_function_is_not_a_finding(self):
        warn = f"{host_check.LOAD_TAG}-WARN redefining ACL2::FN-SIG-VERIFY in DEFUN\n"
        done = f"{host_check.LOAD_TAG}-DONE\n"
        source = "(defun fn-sig-verify (x) x)"
        found, _, _ = host_check.classify_load(warn + done, {"fn-sig-verify"}, source,
                                               {}, world_loaded=True)
        self.assertEqual(found, [])
        found, _, _ = host_check.classify_load(warn + done, {"fn-sig-verify"}, source, {})
        self.assertEqual(len(found), 1)
        other = f"{host_check.LOAD_TAG}-WARN redefining ACL2::FNN-RAW-ONLY in DEFUN\n"
        found, _, _ = host_check.classify_load(other + done, set(), "", {},
                                               world_loaded=True)
        self.assertEqual(len(found), 1)

    def test_a_prefix_error_names_its_host_file(self):
        tag = host_check.WORLD_LD
        output = ("ACL2 !>\n"
                  f"{tag} host/a.lisp\n"
                  f"{tag} host/b.lisp\n"
                  "ACL2 Error [Failure] in ( DEFINTERFACE FN-X ...):  The declared\n"
                  "class ::ideal is not the entry's common-lisp-compliant.\n"
                  f"{host_check.WORLD_OK}\n")
        findings, reached = host_check.world_findings(output)
        self.assertTrue(reached)
        self.assertEqual(len(findings), 1)
        self.assertTrue(findings[0].startswith("world: in host/b.lisp: ACL2 Error"))
        self.assertIn("::ideal", findings[0])
        self.assertEqual(host_check.world_findings("ACL2 !>\n")[1], False)


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


class DeclaredInterfaceTests(unittest.TestCase):
    """The declared-interface step (obstructions-7 item 59): every declared
    entry a function of the world, every dispatched entry declared, counts per
    touched host file."""

    DECLS = [{"name": "fn-a", "source": "host/interfaces.lisp", "line": 3},
             {"name": "fn-gone", "source": "host/interfaces.lisp", "line": 4},
             {"name": "create-st", "source": "host/interfaces.lisp", "line": 5}]
    READING = {"dispatched": {"fn-a": {"host/x.lisp"}, "fn-b": {"host/x.lisp", "host/y.lisp"}},
               "direct": {}, "defined": {"fn-a"}, "entries": 2}

    def test_world_forms_ask_acl2_about_the_declared_functions(self):
        names = host_check.interface_names(self.DECLS)
        self.assertEqual(names, ["fn-a", "fn-gone"])
        forms = host_check.interface_world_forms(names)
        self.assertIn("function-symbolp", forms)
        self.assertIn("'(fn-a fn-gone)", forms)
        self.assertIn(host_check.IFACE_TAG, forms)
        self.assertEqual(host_check.interface_world_forms([]), "")

    def test_the_world_answer_is_read_back(self):
        tag = host_check.IFACE_TAG
        self.assertEqual(host_check.interface_world_undefined(f"x\n{tag} (FN-GONE |fn-q|)\n"),
                         ["fn-gone", "fn-q"])
        self.assertEqual(host_check.interface_world_undefined(f"{tag} NIL\n"), [])
        # Never ran (the prefix failed first): not "no finding".
        self.assertIsNone(host_check.interface_world_undefined("ACL2 Error\n"))

    def test_extraction_only_entries_are_checked_in_their_own_prefix(self):
        from ledger import Sym
        decls = self.DECLS + [{"name": "fn-xo-open-store",
                              "source": "host/interfaces-extract.lisp", "line": 11}]
        native = [[Sym("ld"), "host/interfaces.lisp"]]
        self.assertEqual(host_check.interface_names(decls, native), ["fn-a", "fn-gone"])
        extraction = native + [[Sym("ld"), "host/interfaces-extract.lisp"]]
        self.assertEqual(host_check.interface_names(decls, extraction),
                         ["fn-a", "fn-gone", "fn-xo-open-store"])

    def test_report_counts_per_touched_file_and_fails_stale_and_undeclared(self):
        lines, findings = host_check.interface_report(
            self.DECLS, self.READING, ["the raw host dispatches fn-b (host/x.lisp) and no "
                                       "definterface declares it"], ["host/x.lisp"], ["fn-gone"])
        self.assertIn("host/x.lisp: 2 dispatched, 1 declared, 1 undeclared (fn-b)", "\n".join(lines))
        self.assertIn("world: 1 declared name(s) not a function", lines[0])
        self.assertEqual(len(findings), 2)
        self.assertTrue(any("fn-gone is declared" in f and "not a function" in f
                            for f in findings))
        quiet, none = host_check.interface_report(self.DECLS, self.READING, [], [], [])
        self.assertEqual(none, [])
        self.assertIn("touches no host file", "\n".join(quiet))
        unevaluated, _ = host_check.interface_report(self.DECLS, self.READING, [], None, None)
        self.assertIn("world: not evaluated", unevaluated[0])
        self.assertIn("host/y.lisp: 1 dispatched, 0 declared", "\n".join(unevaluated))

    def test_load_check_puts_the_world_half_in_the_session_and_its_answer_in_findings(self):
        import inspect
        source = inspect.getsource(host_check.load_check)
        self.assertIn("interface_world_forms(interface_names(declared, world))", source)
        self.assertIn("interface_step(interface_world_undefined(output)", source)
        self.assertIn("static_always=False", source)

    def test_inside_load_static_findings_fail_only_for_touched_files(self):
        from unittest import mock
        import interface_emit
        static = ["the raw host dispatches fn-b (host/x.lisp) and no definterface declares it",
                  "the raw host dispatches fn-c (host/y.lisp) and no definterface declares it"]
        out = io.StringIO()
        with mock.patch.object(host_check, "touched_host_files", lambda root: ["host/x.lisp"]), \
                mock.patch.object(interface_emit, "declarations", lambda root: self.DECLS), \
                mock.patch.object(interface_emit, "host_reading", lambda root: self.READING), \
                mock.patch.object(interface_emit, "findings", lambda d, r, root: list(static)), \
                contextlib.redirect_stdout(out):
            found = host_check.interface_step([], echo=False, static_always=False)
        self.assertEqual(found, ["interfaces: " + static[0]])
        self.assertIn("warn interfaces: " + static[1], out.getvalue())

    def test_inside_load_an_untouched_branch_skips_the_static_half(self):
        from unittest import mock
        import interface_emit
        out = io.StringIO()
        with mock.patch.object(host_check, "touched_host_files", lambda root: []), \
                mock.patch.object(interface_emit, "declarations", lambda root: self.DECLS), \
                mock.patch.object(interface_emit, "host_reading",
                                  side_effect=AssertionError("static half ran")), \
                contextlib.redirect_stdout(out):
            found = host_check.interface_step(["fn-gone"], echo=False, static_always=False)
        self.assertEqual(len(found), 1)
        self.assertIn("static half skipped", out.getvalue())


class CommandModeTests(unittest.TestCase):
    def test_combined_modes_refuse_before_skipping_any_requested_check(self):
        import itertools
        from unittest import mock
        modes = ("--load", "--tables", "--alone", "--world", "--interfaces",
                 "--forward", "--books", "--read")
        for pair in itertools.combinations(modes, 2):
            with self.subTest(modes=pair), \
                    mock.patch.object(host_check, "books_main") as books, \
                    mock.patch.object(host_check, "read_check") as read, \
                    mock.patch.object(host_check, "executable") as executable, \
                    contextlib.redirect_stderr(io.StringIO()) as errors:
                with self.assertRaises(SystemExit) as refused:
                    host_check.main(list(pair))
                self.assertEqual(refused.exception.code, 2)
                self.assertIn("not allowed with argument", errors.getvalue())
                books.assert_not_called()
                read.assert_not_called()
                executable.assert_not_called()


if __name__ == "__main__":
    unittest.main()

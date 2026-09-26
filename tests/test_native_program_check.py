"""tools/native_program_check.py: the tree passes, and each mutation fails.

The mutations are applied to the host source TEXT handed to `check()`; no
file is changed.  Each one is a drift the check exists to catch.
"""
from pathlib import Path
import unittest

from tests.campaign import native_cuts
from tools import native_program_check as npc

ROOT = Path(__file__).resolve().parent.parent


def mutate(text: str, old: str, new: str, within: str | None = None) -> str:
    """Replace OLD by NEW once, inside the defun WITHIN when given."""
    if within is None:
        assert text.count(old) == 1, old
        return text.replace(old, new)
    body = native_cuts.host_function(text, within)
    assert body.count(old) == 1, (within, old)
    return text.replace(body, body.replace(old, new))


class NativeProgramCheckTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.host = (ROOT / npc.HOST).read_text()

    def verdicts(self, report):
        return {r.program: r.verdict for r in report.programs}

    def assert_fails(self, host, program, needle=None):
        report = npc.check(host_text=host)
        self.assertFalse(report.ok)
        result = next(r for r in report.programs if r.program == program)
        self.assertEqual(result.verdict, "FAIL")
        if needle is not None:
            self.assertTrue(any(needle in m for m in result.mismatches), result.mismatches)
        return report

    def test_current_tree_passes_every_program_in_the_cut_table(self):
        report = npc.check()
        named = {c.program for c in native_cuts.ALL_CUTS} | {
            c.follows for c in native_cuts.ALL_CUTS if c.follows}
        self.assertEqual(set(self.verdicts(report)), named)
        self.assertEqual(named, {"fn-bs-frontier-program", "fn-bs-record-program",
                                 "fn-bs-finish-program", "fn-bs-recover-program",
                                 "fn-bs-recover-stage-cleanup-program",
                             "fn-bs-marker-program"})
        self.assertTrue(report.ok, npc.render(report))
        for r in report.programs:
            self.assertEqual(r.matched, r.model_steps, r.program)
            self.assertGreater(r.model_steps, 0)

    def test_the_directory_alias_is_derived_not_assumed(self):
        # :frontier-directory (host) and :frontier-dir (model) both reach
        # fn-sf-frontier-dir-result; an undispatched host name does not.
        report = npc.check()
        frontier = next(r for r in report.programs if r.program == "fn-bs-frontier-program")
        self.assertIn(":frontier-directory :error -> *fn-bs-frontier-on-dir-error*",
                      frontier.error_arms)
        self.assertEqual(frontier.injection_only, ["frontier-barrier"])

    def test_swapped_cut_and_link_fails(self):
        host = mutate(self.host, "          (fnn-at store :record-linked)\n", "",
                      within="fnn-publish")
        host = mutate(host, "(handler-case (fnn-link stage final)",
                      "(fnn-at store :record-linked)\n          (handler-case (fnn-link stage final)",
                      within="fnn-publish")
        report = self.assert_fails(host, "fn-bs-record-program")
        self.assertEqual(self.verdicts(report)["fn-bs-frontier-program"], "PASS")

    def test_deleted_helper_cut_fails_both_callers(self):
        host = mutate(self.host, "(fnn-at store written)\n", "",
                      within="fnn-write-staged-at")
        report = self.assert_fails(host, "fn-bs-record-program")
        self.assertEqual(self.verdicts(report)["fn-bs-frontier-program"], "FAIL")

    def test_wrong_directory_barrier_fails(self):
        host = mutate(self.host, "(fnn-fsync-dir (fnn-transactions store))",
                      "(fnn-fsync-dir (fnn-store-root store))", within="fnn-publish")
        self.assert_fails(host, "fn-bs-record-program", ":fsync-dir :root")

    def test_error_arm_with_no_model_constant_fails(self):
        host = mutate(self.host, "(fnn-os-error (e) (fnn-observe store :record-link :error) (error e))",
                      "(fnn-os-error (e) (fnn-observe store :record-link :error)"
                      " (fnn-observe store :record-file :error) (error e))",
                      within="fnn-publish")
        self.assert_fails(host, "fn-bs-record-program", "no model constant")

    def test_model_event_name_the_kernel_does_not_dispatch_fails(self):
        # The model's name for the host's operation is not a host operation.
        host = mutate(self.host, "(fnn-observe store :record-directory :ok)",
                      "(fnn-observe store :record-dir :ok)", within="fnn-publish")
        self.assert_fails(host, "fn-bs-record-program", "does not dispatch")

    def test_declared_model_cut_off_its_program_fails(self):
        host = mutate(self.host, "'(:frontier-created :frontier-written",
                      "'(:frontier-barrier :frontier-created :frontier-written")
        self.assert_fails(host, "fn-bs-frontier-program", "frontier-barrier")

    def test_recovery_sweep_before_a_barrier_fails(self):
        host = mutate(self.host, "(fnn-at store :recover-replayed)",
                      "(fnn-at store :recover-replayed)\n    (fnn-sweep-staging store)",
                      within="fnn-recover")
        self.assert_fails(host, "fn-bs-recover-program", "sequel")


class UnbalancedFormTests(unittest.TestCase):
    """PKT-345: an unbalanced form is located, never a bare StopIteration."""

    def test_parse_at_names_the_file_and_the_forms_first_line(self):
        text = npc.Text('(defun ok (x) x)\n\n(defun broken (x)\n  (let ((y x))\n    y)\n', [(0, "host/x.lisp")])
        offset = text.index("(defun broken")
        with self.assertRaises(npc.Unbalanced) as raised:
            npc.parse_at(text, offset)
        self.assertEqual(str(raised.exception),
                         "unbalanced: host/x.lisp:6, form starting at host/x.lisp:3 never closes")
        self.assertEqual(npc.parse_at(text, 0), ["defun", "ok", ["x"], "x"])
        self.assertEqual(npc.parse_at(npc.Text('(f ")" "(")', []), 0), ["f", ")", "("])

    def test_a_joined_text_reports_the_book_the_form_is_in(self):
        joined = npc.Text("(a)\n(b)\n" + "\n" + "(c\n(d)\n", [(0, "books/one.lisp"), (9, "books/two.lisp")])
        with self.assertRaises(npc.Unbalanced) as raised:
            npc.parse_at(joined, joined.index("(c"))
        self.assertIn("form starting at books/two.lisp:1", str(raised.exception))

    def test_a_stray_close_is_located(self):
        with self.assertRaises(npc.Unbalanced) as raised:
            npc.parse_at(npc.Text("\n) x", [(0, "f.lisp")]), 0)
        self.assertIn("f.lisp:1: a close parenthesis with no open form", str(raised.exception))

    def test_check_reports_an_unbalanced_host_defun(self):
        host = (ROOT / npc.HOST).read_text()
        # rep-wave-d-3's case: the defun loses its last close parenthesis.
        start = host.index("\n(defun fnn-state-checkpoint-plan ") + 1
        end = host.index("\n(defun ", start)
        body = host[start:end].rstrip()
        self.assertTrue(body.endswith(")"))
        broken = npc.Text(host[:start] + body[:-1] + "\n" + host[end:], [(0, npc.HOST)])
        self.assertEqual(npc.balance(npc.Text(host, [(0, npc.HOST)])), [])
        problems = npc.balance(broken)
        self.assertEqual(len(problems), 1, problems)
        line = host.count("\n", 0, start) + 1
        self.assertIn("form starting at {}:{} never closes".format(npc.HOST, line), problems[0])
        self.assertIn("a form opens at column 0 inside it at {}:".format(npc.HOST), problems[0])

    def test_balance_mode_exit_codes(self):
        import subprocess, sys, tempfile
        with tempfile.TemporaryDirectory() as temporary:
            good = Path(temporary) / "good.lisp"
            bad = Path(temporary) / "bad.lisp"
            good.write_text('(defun a (x) "(" x) ; )\n#| ( |#\n(b #\\( |c(| ")")\n')
            bad.write_text("(defun a (x)\n  x\n(defun b (y) y)\n")
            ok = subprocess.run([sys.executable, str(ROOT / "tools" / "native_program_check.py"),
                                 "--balance", str(good)], capture_output=True, text=True, timeout=60)
            self.assertEqual(ok.returncode, 0, ok.stdout)
            no = subprocess.run([sys.executable, str(ROOT / "tools" / "native_program_check.py"),
                                 "--balance", str(good), str(bad)], capture_output=True, text=True, timeout=60)
            self.assertEqual(no.returncode, 1)
            self.assertIn("form starting at {}:1 never closes".format(bad), no.stdout)
            self.assertIn("column 0 inside it at {}:3".format(bad), no.stdout)


if __name__ == "__main__":
    unittest.main()

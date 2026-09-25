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


if __name__ == "__main__":
    unittest.main()

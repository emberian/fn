"""obstructions-5 item 41: on a box, `sbcl` is the toolchain's, by absolute path.

hbox's system /usr/bin/sbcl (2.2.9) sat on PATH ahead of the toolchain's
/tank/fn/sbcl/bin/sbcl (2.6.8); tooling-truth-2 traced a KNOWN_RED list to
tools running `sbcl` by name.
"""
import contextlib
import io
import os
import sys
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import farm  # noqa: E402
import native_env  # noqa: E402

TOOLCHAIN = "/tank/fn/sbcl/bin/sbcl"


class HostsTests(unittest.TestCase):
    def test_every_box_names_the_toolchain_sbcl(self):
        for box, settings in farm.HOSTS.items():
            self.assertEqual(settings.get("sbcl"), TOOLCHAIN, box)
        self.assertEqual(native_env.host_sbcls(), [TOOLCHAIN])

    def test_a_farm_run_puts_it_first_on_path(self):
        script = farm.remote_script("hbox", Path("/tank/fn/tree"), "run-1", ["books/x"], 4, 900, [])
        self.assertIn(f"FN_SBCL={TOOLCHAIN} PATH=/tank/fn/sbcl/bin:$PATH", script)


class RefusalTests(unittest.TestCase):
    real = staticmethod(lambda p: p)

    def test_off_a_box_nothing_is_checked(self):
        self.assertIsNone(native_env.sbcl_refusal(None, "/usr/bin/sbcl", None, self.real))

    def test_the_system_sbcl_first_on_path_is_refused_by_name(self):
        why = native_env.sbcl_refusal(TOOLCHAIN, "/usr/bin/sbcl", None, self.real)
        self.assertIn("/usr/bin/sbcl", why)
        self.assertIn("native_env.py sbcl --export", why)

    def test_a_wrong_fn_sbcl_is_refused(self):
        why = native_env.sbcl_refusal(TOOLCHAIN, TOOLCHAIN, "/usr/bin/sbcl", self.real)
        self.assertIn("FN_SBCL is /usr/bin/sbcl", why)

    def test_no_sbcl_on_path_is_refused(self):
        self.assertIn("no `sbcl` on PATH", native_env.sbcl_refusal(TOOLCHAIN, None, None,
                                                                   self.real))

    def test_the_toolchain_passes(self):
        self.assertIsNone(native_env.sbcl_refusal(TOOLCHAIN, TOOLCHAIN, TOOLCHAIN, self.real))

    def test_toolchain_sbcl_is_the_first_present_host_path(self):
        self.assertEqual(native_env.toolchain_sbcl([TOOLCHAIN], exists=lambda p: True), TOOLCHAIN)
        self.assertIsNone(native_env.toolchain_sbcl([TOOLCHAIN], exists=lambda p: False))


class CommandTests(unittest.TestCase):
    def run_main(self, *argv, which=None, found=TOOLCHAIN, environ=None):
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(native_env, "toolchain_sbcl", lambda: found), \
                mock.patch.object(native_env.shutil, "which", lambda name: which), \
                mock.patch.object(native_env.os.path, "realpath", lambda p: p), \
                mock.patch.dict(os.environ, environ or {}, clear=False), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            if not environ:
                os.environ.pop("FN_SBCL", None)
            code = native_env.main(list(argv))
        return code, out.getvalue(), err.getvalue()

    def test_export_line(self):
        code, out, _ = self.run_main("sbcl", "--export")
        self.assertEqual((code, out.strip()),
                         (0, f"export FN_SBCL={TOOLCHAIN} PATH=/tank/fn/sbcl/bin:$PATH"))

    def test_off_a_box_prints_nothing(self):
        self.assertEqual(self.run_main("sbcl", found=None)[:2], (0, ""))

    def test_check_refuses_the_system_sbcl_exit_2(self):
        code, _, err = self.run_main("sbcl-check", which="/usr/bin/sbcl")
        self.assertEqual(code, 2)
        self.assertIn("REFUSED", err)

    def test_check_passes_the_toolchain(self):
        self.assertEqual(self.run_main("sbcl-check", which=TOOLCHAIN)[0], 0)


class WiringTests(unittest.TestCase):
    """The three entry points run the check (text, since each runs on a box)."""

    def test_hbox_native_exports_and_checks_before_any_step(self):
        text = (ROOT / "tools" / "hbox_native.sh").read_text()
        export = text.index('native_env.py sbcl --export')
        check = text.index("step sbcl-check python3 tools/native_env.py sbcl-check")
        self.assertLess(export, check)
        self.assertLess(check, text.index("step install "))

    def test_remote_check_exports_and_checks(self):
        text = (ROOT / "tools" / "remote_check.sh").read_text()
        self.assertIn('native_env.py sbcl --export', text)
        self.assertIn("native_env.py sbcl-check", text)

    def test_makefile_exports_fn_sbcl_on_a_box(self):
        text = (ROOT / "Makefile").read_text()
        self.assertIn("TOOLCHAIN_SBCL := $(shell $(PYTHON) tools/native_env.py sbcl", text)
        self.assertIn("export FN_SBCL := $(TOOLCHAIN_SBCL)", text)


if __name__ == "__main__":
    unittest.main()

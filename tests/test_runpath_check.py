"""tools/runpath_check.py: the tree passes; each kind of Python on the path fails."""
from __future__ import annotations

import io
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import runpath_check  # noqa: E402


def elf_with_needed(names: list[str]) -> bytes:
    """A minimal ELF64LE object: section 1 dynamic (DT_NEEDED...), section 2 its strtab."""
    strtab = b"\0"
    offsets = []
    for name in names:
        offsets.append(len(strtab))
        strtab += name.encode() + b"\0"
    dynamic = b"".join(struct.pack("<qQ", 1, off) for off in offsets) + struct.pack("<qQ", 0, 0)
    header_size = 64
    dyn_off = header_size
    str_off = dyn_off + len(dynamic)
    sh_off = str_off + len(strtab)
    ident = b"\x7fELF" + bytes([2, 1, 1]) + bytes(9)
    header = ident + struct.pack("<HHIQQQIHHHHHH", 3, 62, 1, 0, 0, sh_off, 0, 64, 0, 0, 64, 3, 0)

    def section(sh_type, offset, size, link):
        return struct.pack("<IIQQQQIIQQ", 0, sh_type, 0, 0, offset, size, link, 0, 8, 0)

    sections = section(0, 0, 0, 0) + section(6, dyn_off, len(dynamic), 2) + section(3, str_off, len(strtab), 0)
    return header + dynamic + strtab + sections


class RunpathCheckTests(unittest.TestCase):
    def run_main(self, argv):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = runpath_check.main(argv)
        return code, out.getvalue(), err.getvalue()

    def release(self, tmp: Path) -> Path:
        top = tmp / "fn-0123456789ab"
        (top / "bin").mkdir(parents=True)
        (top / "libexec/fn/runtime").mkdir(parents=True)
        (top / "libexec/fn/lib").mkdir(parents=True)
        (top / "share/fn/rc.d").mkdir(parents=True)
        (top / "libexec/fn/lib/libzstd.so.7.0").write_bytes(elf_with_needed(["libc.so.103.0"]))
        (top / "libexec/fn/lib/libsodium.so.11.1").write_bytes(elf_with_needed(["libc.so.103.0"]))
        (top / "libexec/fn/fn-host.core").write_bytes(
            b"\0" * 64 + b"libsodium.so\0libssl.so\0libfn-mldsa65.so\0"
            + "libcrypto.so.3".encode("utf-32-le") + b"\0" * 8)
        (top / "libexec/fn/lib/libfn-mldsa65.so").write_bytes(elf_with_needed(["libc.so.103.0"]))
        shutil.copy(ROOT / "packaging/fn", top / "bin/fn")
        os.chmod(top / "bin/fn", 0o755)
        launcher = runpath_check.freeze_launcher_template(ROOT)
        (top / "libexec/fn/fn-host").write_text(launcher)
        os.chmod(top / "libexec/fn/fn-host", 0o755)
        (top / "libexec/fn/runtime/sbcl").write_bytes(elf_with_needed(["libc.so.103.0", "libzstd.so.7.0"]))
        os.chmod(top / "libexec/fn/runtime/sbcl", 0o755)
        rc = (ROOT / "packaging/fn.rc.in").read_text().replace("@PREFIX@", "/usr/local/fn-0123456789ab")
        (top / "share/fn/rc.d/fn").write_text(rc)
        return top

    def test_static_tree_is_clean(self):
        code, out, err = self.run_main([])
        self.assertEqual(code, 0, err)
        self.assertIn("fnn-workflow-ion-run-helper", out)

    def test_release_tree_is_clean(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            code, out, err = self.run_main(["--tree", str(top)])
            self.assertEqual(code, 0, err)
            self.assertIn("libexec/fn/runtime/sbcl: ELF; needs libc.so.103.0 libzstd.so.7.0", out)
            self.assertIn("share/fn/rc.d/fn: starts /usr/local/fn-0123456789ab/bin/fn", out)
            self.assertIn("the system's: libcrypto.so.3 libssl.so", out)

    def assert_finding(self, top: Path, fragment: str):
        code, _out, err = self.run_main(["--tree", str(top)])
        self.assertEqual(code, 1, err)
        self.assertIn(fragment, err)

    def test_planted_python_symlink_fails(self):
        # HST-018's witness: a scratch copy with bin/python3 -> the system's.
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            os.symlink("/usr/bin/python3", top / "bin/python3")
            self.assert_finding(top, "bin/python3: links to /usr/bin/python3")

    def test_symlink_leaving_the_release_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            os.symlink("../../../../etc/ssl/libssl.so.3", top / "libexec/fn/lib/libssl.so.3")
            self.assert_finding(top, "links outside the release")

    def test_needed_library_not_carried_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            (top / "libexec/fn/lib/libzstd.so.7.0").unlink()
            self.assert_finding(top, "DT_NEEDED libzstd.so.7.0 is neither carried")

    def test_core_dlopen_name_not_carried_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            with open(top / "libexec/fn/fn-host.core", "ab") as core:
                core.write("libpython3.12.so.1.0".encode("utf-32-le") + b"\0" * 4)
            self.assert_finding(top, "may dlopen libpython3.12.so.1.0")

    def test_arithmetic_expansion_runs_no_command(self):
        # packaging/fn's heap step: `$(( (core_octets + 1048575) / 1048576 + 128 ))'.
        self.assertEqual(runpath_check.split_commands(
            "boot=$(( (core_octets + 1048575) / 1048576 + 128 ))"), [])
        self.assertEqual(runpath_check.split_commands(
            "n=$(( 1 + 2 )); /usr/local/bin/helper $(( n / 2 ))"), ["/usr/local/bin/helper"])

    def test_absolute_command_outside_the_release_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            text = (top / "bin/fn").read_text().replace(
                'exec "$image" --fn "$@"', '/usr/local/bin/helper\nexec "$image" --fn "$@"')
            (top / "bin/fn").write_text(text)
            self.assert_finding(top, "runs /usr/local/bin/helper, outside the release")

    def test_python_shebang_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            (top / "libexec/fn/helper").write_text("#!/usr/bin/env python3\nprint(1)\n")
            code, _, err = self.run_main(["--tree", str(top)])
            self.assertEqual(code, 1)
            self.assertIn("libexec/fn/helper: interpreter /usr/bin/env python3", err)

    def test_python_command_in_launcher_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            text = (top / "bin/fn").read_text().replace('exec "$image"', 'python3 -c pass\nexec "$image"')
            (top / "bin/fn").write_text(text)
            code, _, err = self.run_main(["--tree", str(top)])
            self.assertEqual(code, 1)
            self.assertIn("bin/fn: runs python3", err)

    def test_libpython_needed_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            (top / "libexec/fn/runtime/sbcl").write_bytes(elf_with_needed(["libpython3.13.so.1.0"]))
            code, _, err = self.run_main(["--tree", str(top)])
            self.assertEqual(code, 1)
            self.assertIn("DT_NEEDED libpython3.13.so.1.0", err)

    def test_python_source_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            (top / "share/fn/probe.py").write_text("print(1)\n")
            code, _, err = self.run_main(["--tree", str(top)])
            self.assertEqual(code, 1)
            self.assertIn("share/fn/probe.py: Python source", err)

    def test_service_starting_python_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            rc = (top / "share/fn/rc.d/fn").read_text().replace(
                'daemon="/usr/local/fn-0123456789ab/bin/fn"', 'daemon="/usr/local/bin/python3"')
            (top / "share/fn/rc.d/fn").write_text(rc)
            code, _, err = self.run_main(["--tree", str(top)])
            self.assertEqual(code, 1)
            self.assertIn("starts /usr/local/bin/python3", err)

    def test_sbcl_fasl_header_passes_and_other_interpreters_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            contrib = top / "libexec/fn/runtime/sbcl-home/contrib"
            contrib.mkdir(parents=True)
            (contrib / "sb-posix.fasl").write_bytes(b"#!/usr/obj/ports/sbcl/src/runtime/sbcl --script\n\0\1")
            code, out, err = self.run_main(["--tree", str(top)])
            self.assertEqual(code, 0, err)
            self.assertIn("1 SBCL contrib fasls", out)
            (top / "libexec/fn/tool").write_text("#!/usr/bin/perl\n")
            code, _, err = self.run_main(["--tree", str(top)])
            self.assertEqual(code, 1)
            self.assertIn("libexec/fn/tool: interpreter /usr/bin/perl is neither /bin/sh nor SBCL", err)

    def test_unlisted_process_site_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / "host", root / "host")
            shutil.copytree(ROOT / "packaging", root / "packaging")
            with open(root / "host/native/io.lisp", "a") as handle:
                handle.write('\n(defun fnn-probe () (sb-ext:run-program "/usr/bin/python3" nil))\n')
            code, _, err = self.run_main(["--root", str(root)])
            self.assertEqual(code, 1)
            self.assertIn("unlisted process site host/native/io.lisp", err)
            self.assertIn("in fnn-probe", err)

    def test_comment_mentioning_run_program_passes(self):
        text = runpath_check.strip_lisp_comments(';; sb-ext:run-program here\n(defun f () "run-program")\n')
        self.assertNotIn("sb-ext:run-program", text)


if __name__ == "__main__":
    unittest.main()

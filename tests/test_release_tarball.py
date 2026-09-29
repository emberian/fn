"""The release tarball as a stranger receives it (HST-017, HST-018, SCN-134).

On Linux no bundled ELF object may need a glibc symbol version above
tools/runpath_check.py's GLIBC_FLOOR (the release runs on Debian 12).

Needs a release built by packaging/release-tarball.sh on this platform:

    FN_RELEASE_TARBALL=/abs/out/fn-6.6.0-linux-x86_64.tar.gz \\
        python3 -m unittest -v tests.test_release_tarball

(OUT_DIR/SHA256SUMS beside it).  The install refuses a node whose store
names another format word, synthesized by tests/foreign_format_store.py with
the release's own bin/fn (no fixture store is kept for it).
Without FN_RELEASE_TARBALL every case is skipped (not a pass).
"""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import runpath_check  # noqa: E402
import release_sequence  # noqa: E402
sys.path.insert(0, str(ROOT))
from tests import foreign_format_store as foreign  # noqa: E402

TARBALL = os.environ.get("FN_RELEASE_TARBALL")
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
                    "libexec/fn/lib/libfn-deflate.so",
                    "libexec/fn/lib/libfn-blake3.so",
                    "share/fn/fn.toml.example", "share/fn/docs/fn-faq-3.txt",
                    "share/fn/release-gate.txt", "share/fn/runpath-check.txt"):
            self.assertTrue((self.top / rel).exists(), rel)
        self.assertTrue(list((self.top / "libexec/fn/lib").glob("libsodium.so.*")))
        service = ("share/fn/rc.d/fn.rc.in" if platform.system() == "OpenBSD"
                   else "share/fn/systemd/fn.service.in")
        self.assertTrue((self.top / service).is_file(), service)
        self.assertFalse((self.top / "libexec/fn/fn-host-developer").exists())

    def test_the_clients_ship_beside_the_node_and_apart_from_it(self):
        # The command-line clients (packaging/install-clients.sh): Python in
        # clients/ only, a launcher each, no service.  The web page is the
        # node's own face (install.sh --reader, share/fn/caddy/fn-web.caddy):
        # no Python reader ships.
        for name in ("fn-client", "fn-agent", "fn-consumer", "fn-verify"):
            self.assertTrue(os.access(self.top / "clients/bin" / name, os.X_OK), name)
        for name in ("fn-reader", "fn-web"):
            self.assertFalse((self.top / "clients/bin" / name).exists(), name)
        for rel in ("clients/lib/fn_client.py", "clients/lib/nntp_session.py",
                    "clients/README.txt", "share/fn/caddy/fn-web.caddy", "share/fn/docs/web.md"):
            self.assertTrue((self.top / rel).is_file(), rel)
        self.assertFalse((self.top / "clients/share").exists())
        python = {p.relative_to(self.top).as_posix() for p in self.top.rglob("*.py")}
        self.assertTrue(python and all(rel.startswith("clients/lib/") for rel in python),
                        python)
        record = (self.top / "share/fn/runpath-check.txt").read_text()
        self.assertIn("clients/: 5 Python programs", record)
        # A client runs under the login PATH, which on OpenBSD holds the
        # package's python3 in /usr/local/bin (CLEAN_ENV's PATH does not):
        # the precondition and the run use the same PATH.
        client_env = dict(CLEAN_ENV, PATH=CLEAN_ENV["PATH"] + ":/usr/local/bin")
        if shutil.which("python3", path=client_env["PATH"]):
            shown = subprocess.run([str(self.top / "clients/bin/fn-client"), "--help"],
                                   env=client_env, capture_output=True, text=True, timeout=60)
            self.assertEqual(shown.returncode, 0, shown.stderr)

    def test_inner_sums_cover_every_file(self):
        listed = sums(self.top / "SHA256SUMS")
        files = {p.relative_to(self.top).as_posix() for p in self.top.rglob("*") if p.is_file()}
        files.discard("SHA256SUMS")
        self.assertEqual(set(listed), files)
        for rel, digest in listed.items():
            self.assertEqual(sha256(self.top / rel), digest, rel)

    def test_version_prints_the_release_and_the_source_revision(self):
        rev = (self.top / "libexec/fn/source-revision").read_text().strip()
        self.assertRegex(rev, r"^[0-9a-f]{40}$")
        out = subprocess.run([str(self.top / "bin/fn"), "--version"], env=CLEAN_ENV,
                             capture_output=True, text=True, timeout=120)
        self.assertEqual(out.returncode, 0, out.stderr)
        # `fn VERSION (REV12)': VERSION's release version, built into the
        # image, an entry of D37's release sequence.
        printed = re.fullmatch(r"fn ([0-9.]+) \(([0-9a-f]{12})\)\n", out.stdout)
        self.assertIsNotNone(printed, out.stdout)
        version, short = printed.groups()
        release_sequence.position(version)
        self.assertEqual(short, rev[:12])
        # A gated release is fn-VERSION-PLATFORM.tar.gz; a --frozen package
        # (not a release) is fn-VERSION+REV12-PLATFORM.tar.gz.
        self.assertRegex(self.tarball.name,
                         "^fn-" + re.escape(version) + "(\\+" + short + ")?"
                         + "-(linux-x86_64|openbsd-amd64)\\.tar\\.gz$")

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

    @unittest.skipUnless(platform.system() == "Linux", "the glibc floor is the Linux release's")
    def test_no_bundled_elf_needs_glibc_above_the_floor(self):
        # runpath_check.GLIBC_FLOOR (Debian 12's 2.36; lane release-glibc-floor).
        elves, above = [], []
        for path in sorted(p for p in self.top.rglob("*") if p.is_file() and not p.is_symlink()):
            with open(path, "rb") as handle:
                if handle.read(4) != b"\x7fELF":
                    continue
            facts = runpath_check.elf_facts(path.read_bytes())
            self.assertIsNotNone(facts, path)
            highest, over = runpath_check.glibc_above_floor(facts)
            elves.append(path.relative_to(self.top).as_posix())
            above += [f"{path.relative_to(self.top).as_posix()}: {need}" for need in over]
        self.assertIn("libexec/fn/runtime/sbcl", elves)
        self.assertIn("libexec/fn/lib/libsodium.so.23", elves)
        self.assertIn("libexec/fn/lib/libfn-mldsa65.so", elves)
        self.assertIn("libexec/fn/lib/libfn-deflate.so", elves)
        self.assertIn("libexec/fn/lib/libfn-blake3.so", elves)
        self.assertEqual(above, [])

    def install(self, prefix: Path, node: Path, *flags: str) -> subprocess.CompletedProcess:
        return subprocess.run(["sh", str(self.top / "install.sh"), "--prefix", str(prefix),
                               "--node", str(node), "--no-service", *flags], env=CLEAN_ENV,
                              capture_output=True, text=True, timeout=600)

    def release_name(self) -> str:
        """VERSION+REV from `bin/fn --version` (`fn VERSION (REV)`): the
        installed release's directory under PREFIX/releases."""
        printed = subprocess.run([str(self.top / "bin/fn"), "--version"], env=CLEAN_ENV,
                                 capture_output=True, text=True, timeout=600).stdout.split()
        self.assertEqual(printed[:1], ["fn"], printed)
        return "{}+{}".format(printed[1], printed[2].strip("()"))

    def test_install_makes_the_releases_layout_and_refuses_the_rest_by_name(self):
        with tempfile.TemporaryDirectory() as tmp:
            prefix, node = Path(tmp) / "opt/fn", Path(tmp) / "node"
            first = self.install(prefix, node)
            self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
            name = self.release_name()
            self.assertTrue((prefix / "releases" / name / "bin/fn").is_file())
            self.assertEqual(os.readlink(prefix / "current"), "releases/" + name)
            self.assertFalse((prefix / "previous").exists())
            if platform.system() == "OpenBSD":
                # rc.d(8) names the program and its flags apart
                # (share/fn/rc.d/fn.rc.in); the daemon runs through current.
                rc = (node / "fn.rc").read_text()
                self.assertIn(f'daemon="{prefix}/current/bin/fn"', rc)
                self.assertIn(f'daemon_flags="operator {node}/fn.toml run"', rc)
            else:
                unit = node / "fn.service"
                self.assertIn(f"{prefix}/current/bin/fn operator {node}/fn.toml run",
                              unit.read_text())
            # The same release again: refused by name (a node moves to a
            # release by --upgrade); as an upgrade: already installed; a
            # rollback with nothing before it: refused by name.
            again = self.install(prefix, node)
            self.assertEqual(again.returncode, 4, again.stdout + again.stderr)
            self.assertIn("is already installed at", again.stderr)
            (node / "fn.toml").write_text("")
            upgrade = self.install(prefix, node, "--upgrade")
            self.assertEqual(upgrade.returncode, 4, upgrade.stdout + upgrade.stderr)
            self.assertIn("is already installed at", upgrade.stderr)
            rollback = self.install(prefix, node, "--rollback")
            self.assertEqual(rollback.returncode, 4, rollback.stdout + rollback.stderr)
            self.assertIn("nothing to roll back to", rollback.stderr)
            # A prefix from before the layout (no releases/): refused by name.
            old = Path(tmp) / "opt/old"
            (old / "bin").mkdir(parents=True)
            before = self.install(old, node)
            self.assertEqual(before.returncode, 4, before.stdout + before.stderr)
            self.assertIn("holds no releases/", before.stderr)

    def test_install_refuses_a_store_of_another_format(self):
        with tempfile.TemporaryDirectory() as tmp:
            # The node is the builder's directory: another-format/fn.toml
            # and another-format/store.
            made, _, _ = foreign.make_store(None, Path(tmp), env=CLEAN_ENV,
                                            argv=[str(self.top / "bin/fn")])
            node = made.parent
            result = self.install(Path(tmp) / "opt/fn", node)
            self.assertEqual(result.returncode, 4, result.stdout + result.stderr)
            self.assertIn(foreign.LINE, result.stdout + result.stderr)
            self.assertIn("redeploy fresh", result.stderr)
            self.assertFalse((Path(tmp) / "opt/fn").exists())


if __name__ == "__main__":
    unittest.main()

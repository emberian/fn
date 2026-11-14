"""Manifest-selected artifacts outside the historical book scan are collected.

All payloads are synthetic temporary fixtures, never ACL2 certification evidence.
The real eligibility checks run; the final cache writer and every external
command are intercepted, so these tests neither run ACL2 nor publish artifacts.
"""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import certs
import farm


ROOTS = ("tests/machine-arms-unit", "sim/session", "meta/emit/served-export",
         "host/adapter-book")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fixture(root):
    base = root / "books/base.lisp"
    base.parent.mkdir(parents=True)
    base.write_text('(in-package "ACL2")\n(defun base () 1)\n')
    for name in ROOTS:
        source = root / f"{name}.lisp"
        source.parent.mkdir(parents=True, exist_ok=True)
        relative_base = "../../books/base" if name.startswith("meta/") else "../books/base"
        source.write_text(f'(in-package "ACL2")\n(include-book "{relative_base}")\n')
        for suffix in (".cert", ".port", ".fasl"):
            source.with_suffix(suffix).write_bytes(b"\f#Z synthetic fixture " + suffix.encode())
    sources = {str(path.relative_to(root)): digest(path) for path in root.rglob("*.lisp")}
    return {
        "status": "passed",
        "requested_books": list(ROOTS),
        "expected_success_markers": [f"fixture-{name}" for name in ROOTS],
        "observed_success_markers": [f"fixture-{name}" for name in ROOTS],
        "book_results": dict.fromkeys(ROOTS, "passed"),
        "acl2_exit_codes": dict.fromkeys(ROOTS, 0),
        "source_digests_sha256": sources,
        "source_digests_sha256_after": sources.copy(),
        "certificate_digests_sha256": {name: digest(root / f"{name}.cert") for name in ROOTS},
        "compiled_digests_sha256": {name: digest(root / f"{name}.fasl") for name in ROOTS},
        "acl2_compatibility": {"project_directories": {":FN": "."}, "core_sha256": "fixture"},
    }


class CollectionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.top = Path(self.temp.name)
        # No persistent hash/closure memo, subprocess, or final cache writes.
        for name in ("_hash_file", "_plan_file"):
            patch = mock.patch.object(certs, name, return_value=None)
            patch.start()
            self.addCleanup(patch.stop)
        patch = mock.patch.object(subprocess, "run", side_effect=AssertionError("external command"))
        patch.start()
        self.addCleanup(patch.stop)
        self.cache = self.top / "empty-cache"
        self.cache.mkdir()
        patch = mock.patch.object(certs, "write_entry", return_value="published")
        self.writer = patch.start()
        self.addCleanup(patch.stop)

    def publish(self, root, manifest, **kwargs):
        report = certs.publish(root, self.cache, [manifest], **kwargs)
        self.assertEqual(list(self.cache.iterdir()), [])
        return report

    def test_default_publish_includes_manifest_roots_and_retains_scan_diagnostics(self):
        root = self.top / "tree"
        manifest = fixture(root)
        report = self.publish(root, manifest)
        self.assertEqual(report.published, len(ROOTS))
        self.assertEqual({call.args[1] for call in self.writer.call_args_list}, set(ROOTS))
        self.assertEqual(report.uncached, ["books/base"])
        for call in self.writer.call_args_list:
            name, key, listing = call.args[1:4]
            self.assertEqual((key, listing), certs.closure_key(root, name, "plain"))

    def test_explicit_publish_stays_scoped(self):
        root = self.top / "tree"
        manifest = fixture(root)
        report = self.publish(root, manifest, names=[ROOTS[1]])
        self.assertEqual(report.books, 1)
        self.assertEqual([call.args[1] for call in self.writer.call_args_list], [ROOTS[1]])

    def test_manifest_selection_rejects_paths_outside_certifier_roots(self):
        root = self.top / "tree"
        manifest = fixture(root)
        for name in ("../outside", "/tmp/outside", "tests/../outside", "host/native/raw"):
            manifest["requested_books"].append(name)
            manifest["expected_success_markers"].append(name)
            manifest["observed_success_markers"].append(name)
            manifest["book_results"][name] = "passed"
            manifest["source_digests_sha256"][f"{name}.lisp"] = "fixture"
            manifest["certificate_digests_sha256"][name] = "fixture"
        report = self.publish(root, manifest)
        self.assertEqual(report.books, len(ROOTS) + 1)
        self.assertEqual({call.args[1] for call in self.writer.call_args_list}, set(ROOTS))

    def test_added_roots_keep_source_certificate_and_closure_refusals(self):
        for change in ("source", "certificate", "dependency", "after", "marker", "toolchain"):
            with self.subTest(change=change):
                root = self.top / change
                manifest = fixture(root)
                self.writer.reset_mock()
                if change == "source":
                    (root / f"{ROOTS[0]}.lisp").write_text('(in-package "ACL2")\n(defun changed () 2)\n')
                elif change == "certificate":
                    (root / f"{ROOTS[0]}.cert").write_bytes(b"\f#Z stale certificate fixture")
                elif change == "dependency":
                    (root / "books/base.lisp").write_text('(in-package "ACL2")\n(defun base () 2)\n')
                elif change == "after":
                    manifest["source_digests_sha256_after"][f"{ROOTS[0]}.lisp"] = "mismatch"
                elif change == "marker":
                    manifest["observed_success_markers"].remove(f"fixture-{ROOTS[0]}")
                else:
                    manifest["acl2_compatibility"] = {}
                report = self.publish(root, manifest)
                written = {call.args[1] for call in self.writer.call_args_list}
                self.assertNotIn(ROOTS[0], written)
                if change in ("dependency", "toolchain"):
                    self.assertEqual(written, set())
                else:
                    self.assertEqual(written, set(ROOTS[1:]))
                if change != "marker":
                    self.assertTrue(any(name.startswith(ROOTS[0]) for name in report.unverified))

    def test_fetch_collects_manifest_artifacts_before_real_verification(self):
        remote = self.top / "remote"
        manifest = fixture(remote)
        root = self.top / "local"
        shutil.copytree(remote, root, ignore=shutil.ignore_patterns("*.cert", "*.port", "*.fasl"))
        evidence = "build/acl2/fixture-run"
        (remote / evidence).mkdir(parents=True)
        (remote / evidence / "manifest.json").write_text(json.dumps(manifest))
        # One collected pair is stale: collection itself confers no eligibility.
        (remote / f"{ROOTS[0]}.cert").write_bytes(b"\f#Z stale fetched fixture")
        commands = []

        def run(command, check=True):
            commands.append(command)
            self.assertEqual(command[0], "rsync")
            source = Path(command[-2].split(":", 1)[1])
            target = Path(command[-1])
            self.assertTrue(source.is_relative_to(remote))
            target.mkdir(parents=True, exist_ok=True)
            for path in source.rglob("*"):
                if path.is_file() and path.suffix in (".cert", ".port", ".fasl"):
                    destination = target / path.relative_to(source)
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(path, destination)
            return subprocess.CompletedProcess(command, 0, "")

        def evidence_copy(host, remote_root, directory, local):
            shutil.copytree(remote_root / directory, local, dirs_exist_ok=True)
            return True

        def ssh(host, script, check=True):
            output = f"Certification evidence: {evidence}\n" if script.startswith("cat ") else "publish: fixture\n"
            return subprocess.CompletedProcess(["ssh"], 0, output)

        with mock.patch.object(farm, "run", side_effect=run), \
                mock.patch.object(farm, "ssh", side_effect=ssh), \
                mock.patch.object(farm, "fetch_evidence_dir", side_effect=evidence_copy), \
                mock.patch.object(farm, "MIRROR", side_effect=AssertionError("network mirror")), \
                mock.patch.object(certs, "cache_directory", return_value=self.cache), \
                contextlib.redirect_stdout(io.StringIO()):
            farm.fetch("fixture-box", "fixture", root, remote, cache="fixture-isolated-cache")
        self.assertEqual({call.args[1] for call in self.writer.call_args_list}, set(ROOTS[1:]))
        for name in ROOTS:
            for suffix in (".cert", ".port", ".fasl"):
                self.assertEqual((root / f"{name}{suffix}").read_bytes(),
                                 (remote / f"{name}{suffix}").read_bytes())
        self.assertEqual({Path(command[-2].split(":", 1)[1]).relative_to(remote).as_posix()
                          for command in commands},
                         {"books", "tests", "sim", "meta/emit", "host"})
        self.assertEqual(list(self.cache.iterdir()), [])


if __name__ == "__main__":
    unittest.main()

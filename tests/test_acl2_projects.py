"""Portable :FN book names: launch environment and cache generation boundary.

All certificates here are textual fixtures; no ACL2 process is started.
"""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import acl2_projects
import acl2_slots
import acl2_toolchain
import certify_books
from tests.test_certs import certs, worktree, manifest_for, install, entry, TEXT_CERT


class ProjectEnvironmentTests(unittest.TestCase):
    def test_two_trees_use_the_same_relative_mapping_despite_ambient_override(self):
        with tempfile.TemporaryDirectory() as temp:
            trees = [worktree(temp + suffix) for suffix in ("/a", "/b")]
            environments = [acl2_slots.acl2_environment(
                {"ACL2_PROJECTS": "/wrong/tree/projects"}, root=tree) for tree in trees]
            self.assertNotEqual(environments[0]["ACL2_PROJECTS"],
                                environments[1]["ACL2_PROJECTS"])
            for tree, env in zip(trees, environments):
                projects = Path(env["ACL2_PROJECTS"])
                self.assertEqual(projects, tree / "acl2-projects")
                self.assertEqual(projects.read_text(), ':FN "."\n')
                self.assertEqual((projects.parent / ".").resolve(), tree)

    def test_unknown_project_mapping_fails_before_launch(self):
        with tempfile.TemporaryDirectory() as temp:
            root = worktree(temp)
            (root / "acl2-projects").write_text(':FN "../another-tree"\n')
            with self.assertRaisesRegex(ValueError, "project-directory contract"):
                acl2_slots.acl2_environment(root=root)

    def test_plain_and_streamed_certification_share_the_project_environment(self):
        # Python stands in for the prover and reports the actual child env.
        driver = 'import os; print(os.environ["ACL2_PROJECTS"])\n'
        with tempfile.TemporaryDirectory() as temp:
            root = worktree(temp)
            with mock.patch.object(certify_books, "ROOT", root), \
                    mock.patch.dict(os.environ, {"ACL2_PROJECTS": "/wrong/tree"}):
                plain = certify_books.run_acl2(Path(sys.executable), driver, 10)
                streamed = certify_books.run_acl2(
                    Path(sys.executable), driver, 10,
                    log_path=root / "book.certify.log", book="books/base")
            self.assertEqual(plain.returncode, 0, plain.stdout)
            self.assertEqual(streamed.returncode, 0, streamed.stdout)
            self.assertEqual(plain.stdout.decode().strip(), str(root / "acl2-projects"))
            self.assertEqual(streamed.stdout, plain.stdout)

    def test_native_build_exports_the_same_mapping_to_its_child(self):
        # Execute the real builder's launch setup, before libraries or image
        # work, in another tree. The child prints its inherited mapping.
        script = (ROOT / "tools/build_native_host.sh").read_text()
        setup = script[:script.index("# FN_NATIVE_BUILD")]
        with tempfile.TemporaryDirectory() as temp:
            root = worktree(temp)
            (root / "tools").mkdir()
            shutil.copy(ROOT / "tools/acl2_projects.py", root / "tools/acl2_projects.py")
            shutil.copy(ROOT / "tools/acl2_toolchain.py", root / "tools/acl2_toolchain.py")
            fake = root / "fake-acl2"
            fake.write_text('#!/bin/sh\nprintf "%s\\n" "$ACL2_PROJECTS"\n')
            fake.chmod(0o755)
            result = subprocess.run(
                ["sh", "-c", setup + '\n"$ACL2"\n', str(root / "tools/build_native_host.sh")],
                capture_output=True, text=True, timeout=10,
                env={**os.environ, "FN_ACL2": str(fake), "ACL2_PROJECTS": "/wrong/tree"})
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), str(root / "acl2-projects"))


class ProjectCacheTests(unittest.TestCase):
    def test_two_origins_compose_sysfile_certificates_without_rewriting(self):
        with tempfile.TemporaryDirectory() as temp:
            first = worktree(temp + "/a", certified=["books/base"])
            second = worktree(temp + "/b", certified=["books/mid"])
            target = worktree(temp + "/target")
            cache = Path(temp) / "cache"
            artifacts = {}
            for tree, name in ((first, "books/base"), (second, "books/mid")):
                text = TEXT_CERT + f'(((:FN . "{name}.lisp") "{name}" "{name}" NIL . 42)'
                if name == "books/mid":
                    text += ' ((:FN . "books/base.lisp") "books/base" "books/base" NIL . 42)'
                text += ')\n0\n'
                (tree / f"{name}.cert").write_text(text)
                artifacts[name] = text.encode()
                report = certs.publish(tree, cache, [manifest_for(tree, [name], write=False)],
                                       [name], origin_kind="run")
                self.assertEqual(report.published, 1)
            report = install(target, cache, ["books/mid"])
            self.assertEqual((report.installed, report.uncached), (2, []))
            self.assertEqual(len(report.origins), 2)
            for name, data in artifacts.items():
                self.assertEqual((target / f"{name}.cert").read_bytes(), data)
            again = install(target, cache, ["books/mid"])
            self.assertEqual((again.installed, again.kept), (0, 2))

    def test_old_manifest_cannot_publish_absolute_names_under_new_keys(self):
        with tempfile.TemporaryDirectory() as temp:
            root = worktree(temp, certified=["books/base"])
            manifest = manifest_for(root, ["books/base"], write=False)
            legacy = dict(manifest["acl2_compatibility"])
            legacy.pop("project_directories")
            manifest["acl2_compatibility"] = legacy
            report = certs.publish(root, root / "cache", [manifest], ["books/base"])
            self.assertEqual(report.published, 0)
            self.assertIn("predates the :FN", report.unverified[0])
            self.assertEqual(report.cache_entries, [])

    def test_key_and_install_receipt_change_once_but_not_between_trees(self):
        with tempfile.TemporaryDirectory() as temp:
            first, second = (worktree(temp + suffix) for suffix in ("/a", "/b"))
            current = certs.closure_key(first, "books/base")[0]
            self.assertEqual(current, certs.closure_key(second, "books/base")[0])
            args = (first, {"books/base": "digest"}, ["books/base"], (), "toolchain", None)
            receipt = certs._install_key(*args)
            with mock.patch.object(certs, "KEY_VERSION", "fn-cert-key-v3 forms+world"):
                self.assertNotEqual(current, certs.closure_key(first, "books/base")[0])
                self.assertNotEqual(receipt, certs._install_key(*args))

    def test_rekey_cannot_promote_an_old_namespace(self):
        with tempfile.TemporaryDirectory() as temp:
            root = worktree(temp, certified=["books/base"])
            cache = root / "cache"
            certs.publish(root, cache, [manifest_for(root, ["books/base"], write=False)],
                          ["books/base"])
            current = entry(cache, root, "books/base")
            old = cache / certs.legacy_byte_key(root, "books/base") / current.name
            old.parent.mkdir()
            current.rename(old)
            meta = json.loads((old / "meta.json").read_text())
            meta["toolchain"].pop("project_directories")
            meta["closure"] = certs.closure_listing(certs.closure(root, "books/base"))
            (old / "meta.json").write_text(json.dumps(meta))
            self.assertEqual(certs.rekey(root, cache, ["books/base"]).rekeyed, 0)
            self.assertFalse(current.exists())

    def test_launcher_cannot_override_the_registered_namespace(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            runtime, core, launcher = (root / s for s in ("sbcl", "core", "acl2"))
            runtime.write_bytes(b"runtime")
            core.write_bytes(b"core")
            command = f'exec "{runtime}" --core "{core}" "$@"\n'
            launcher.write_text("#!/bin/sh\n" + command)
            current = acl2_toolchain.fingerprint(launcher)
            self.assertTrue(current.qualified, current.reason)
            self.assertEqual(current.compatibility["project_directories"], {":FN": "."})
            legacy = dict(current.compatibility)
            legacy.pop("project_directories")
            self.assertNotEqual(current.identity, acl2_toolchain.stable_identity(legacy))
            launcher.write_text("#!/bin/sh\nexport ACL2_PROJECTS=/foreign/projects\n" + command)
            refused = acl2_toolchain.fingerprint(launcher)
            self.assertFalse(refused.qualified)
            self.assertIn("must inherit", refused.reason)


if __name__ == "__main__":
    unittest.main()

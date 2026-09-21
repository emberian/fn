"""The reusable ACL2 identity binds the launcher, core and Lisp runtime."""
from pathlib import Path
import tempfile
import unittest

from tools import acl2_toolchain


class FingerprintTests(unittest.TestCase):
    def fixture(self, root: Path, nested: bool = False) -> Path:
        runtime = root / "sbcl"
        runtime.write_bytes(b"runtime-v1")
        runtime.chmod(0o755)
        core = root / "saved_acl2.core"
        core.write_bytes(b"core-v1")
        saved = root / "saved_acl2"
        saved.write_text(
            '#!/bin/sh\nexec "{}" --dynamic-space-size 32 --core "{}" "$@"\n'
            .format(runtime, core))
        saved.chmod(0o755)
        if not nested:
            return saved
        outer = root / "acl2"
        outer.write_text('#!/bin/bash\nexec "{}" "$@"\n'.format(saved))
        outer.chmod(0o755)
        return outer

    def test_generated_launcher_is_qualified_and_nested_wrapper_is_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            direct = self.fixture(root)
            one = acl2_toolchain.fingerprint(direct)
            self.assertTrue(one.qualified, one.reason)
            self.assertEqual(len(one.compatibility["launcher_chain_sha256"]), 1)
            outer = root / "acl2"
            outer.write_text('#!/bin/bash\nexec "{}" "$@"\n'.format(direct))
            outer.chmod(0o755)
            nested = acl2_toolchain.fingerprint(outer)
            self.assertTrue(nested.qualified, nested.reason)
            self.assertEqual(len(nested.compatibility["launcher_chain_sha256"]), 2)
            self.assertNotEqual(one.identity, nested.identity)

    def test_unchanged_wrapper_does_not_hide_changed_core_or_runtime(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            launcher = self.fixture(root)
            before = acl2_toolchain.fingerprint(launcher)
            (root / "saved_acl2.core").write_bytes(b"core-v2")
            core_changed = acl2_toolchain.fingerprint(launcher)
            self.assertNotEqual(before.identity, core_changed.identity)
            (root / "saved_acl2.core").write_bytes(b"core-v1")
            (root / "sbcl").write_bytes(b"runtime-v2")
            runtime_changed = acl2_toolchain.fingerprint(launcher)
            self.assertNotEqual(before.identity, runtime_changed.identity)

    def test_unknown_launcher_is_explicitly_unqualified(self):
        with tempfile.TemporaryDirectory() as directory:
            launcher = Path(directory) / "acl2"
            launcher.write_text("#!/bin/sh\necho not-a-saved-image\n")
            launcher.chmod(0o755)
            found = acl2_toolchain.fingerprint(launcher)
            self.assertFalse(found.qualified)
            self.assertIsNone(found.identity)
            self.assertEqual(found.provenance["status"], "unqualified")
            self.assertIn("unknown ACL2 launcher command", found.reason)

    def test_launcher_source_is_bounded_and_never_executed_to_infer_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            marker = root / "must-not-exist"
            launcher = root / "acl2"
            launcher.write_text(
                '#!/bin/sh\nprintf owned > "{}"\n'.format(marker))
            launcher.chmod(0o755)
            found = acl2_toolchain.fingerprint(launcher)
            self.assertFalse(found.qualified)
            self.assertFalse(marker.exists())

            launcher.write_bytes(b"#!/bin/sh\n#" +
                                 b"x" * acl2_toolchain.MAX_LAUNCHER_BYTES)
            found = acl2_toolchain.fingerprint(launcher)
            self.assertFalse(found.qualified)
            self.assertIn("parse bound", found.reason)

    def test_comment_or_echo_cannot_disguise_an_exec(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            runtime = root / "sbcl"
            runtime.write_bytes(b"runtime")
            core = root / "core"
            core.write_bytes(b"core")
            for command in (
                    '# exec "{}" --core "{}"'.format(runtime, core),
                    'echo exec "{}" --core "{}"'.format(runtime, core),
                    'exec "{}" --core "{}"; touch elsewhere'.format(
                        runtime, core)):
                launcher = root / "acl2"
                launcher.write_text("#!/bin/sh\n" + command + "\n")
                found = acl2_toolchain.fingerprint(launcher)
                self.assertFalse(found.qualified)


if __name__ == "__main__":
    unittest.main()

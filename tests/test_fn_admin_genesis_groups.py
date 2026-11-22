"""The real fn init and serve commands hand the same genesis configuration to the node."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class GenesisGroups(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        (self.root / "tools").mkdir()
        (self.root / "host").mkdir()
        shutil.copy(ROOT / "fn", self.root / "fn")
        (self.root / "host/build-blake3.sh").write_text("exit 0\n")
        (self.root / "tools/image-node.lsp").touch()
        launcher = self.root / "tools/acl2"
        launcher.write_text(
            f"#!{sys.executable}\n"
            "import json, os\n"
            "from pathlib import Path\n"
            "if os.environ['FN2_IMAGE_MODE'] == 'init':\n"
            "    Path(os.environ['FN2_IMAGE']).touch()\n"
            "print(json.dumps(os.environ.get('FN2_GROUPS')))\n"
        )
        launcher.chmod(0o700)

    def launch(self, mode, groups, *options):
        env = {"PATH": os.environ["PATH"], "PYTHONPATH": str(ROOT / "tools")}
        if groups is not None:
            env["FN2_GROUPS"] = groups
        result = subprocess.run(
            [sys.executable, str(self.root / "fn"), mode, "test.img", *options],
            cwd=self.root, env=env, capture_output=True, text=True, timeout=10,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def test_inherited_text_survives_reopen_and_explicit_override(self):
        original = " tech.first, tech.second\ntech.first\t"
        self.assertEqual(self.launch("init", original), original)
        self.assertEqual(self.launch("serve", "other.group"), original)
        self.assertEqual(self.launch("serve", None, "--group", "override"), "override")

    def test_profile_default_survives_reopen(self):
        self.assertIsNone(self.launch("init", None))
        self.assertIsNone(self.launch("serve", "other.group"))

    def test_explicit_empty_survives_reopen(self):
        self.assertEqual(self.launch("init", ""), "")
        self.assertEqual(self.launch("serve", "other.group"), "")

    def test_old_numbered_hint_restores_group_order(self):
        (self.root / "test.img").touch()
        (self.root / "test.img.groups").write_text("1\tsecond\n2\tfirst\n")
        self.assertEqual(self.launch("serve", None), "second\nfirst")


if __name__ == "__main__":
    unittest.main()

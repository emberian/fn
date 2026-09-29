"""tools/extract/world.py: --digest (world_image.sh's key) and world-host's prologue."""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools" / "extract"))
import world  # noqa: E402


def tree(directory: str) -> Path:
    root = Path(directory).resolve()
    (root / "tools" / "extract").mkdir(parents=True)
    (root / "books").mkdir()
    (root / "host").mkdir()
    (root / "books" / "base.lisp").write_text('(in-package "ACL2")\n')
    (root / "books" / "umbrella.lisp").write_text('(include-book "base")\n')
    (root / "tools" / "extract" / "world.lisp").write_text(
        '(include-book "../../books/umbrella")\n')
    (root / "tools" / "extract" / "world-host.lisp").write_text(
        '(ld "../../host/a-host.lisp" :ld-error-action :error)\n')
    (root / "host" / "a-host.lisp").write_text('(ld "b-host.lisp")\n')
    (root / "host" / "b-host.lisp").write_text("(defun b ())\n")
    for name in ("base", "umbrella"):
        (root / "books" / f"{name}.cert").write_text(f"cert {name}\n")
    return root


class DigestTests(unittest.TestCase):
    def test_the_key_moves_with_every_input_and_nothing_is_written(self):
        with tempfile.TemporaryDirectory() as directory:
            root = tree(directory)
            before = {p: p.read_bytes() for p in root.rglob("*") if p.is_file()}
            key = world.digest(root)
            self.assertEqual(key, world.digest(root))
            self.assertRegex(key, r"^[0-9a-f]{64}$")
            self.assertNotEqual(key, world.digest(root, acl2="/other/acl2"))
            for path, change in (("host/b-host.lisp", "(defun b (x) x)\n"),
                                 ("books/base.cert", "cert base v2\n"),
                                 ("tools/extract/world-host.lisp", "; edited\n")):
                target = root / path
                old = target.read_text()
                target.write_text(change)
                self.assertNotEqual(world.digest(root), key, path)
                target.write_text(old)
            self.assertEqual(world.digest(root), key)
            (root / "books" / "base.fasl").write_bytes(b"fasl")
            self.assertNotEqual(world.digest(root), key)
            after = {p: p.read_bytes() for p in root.rglob("*") if p.is_file()}
            self.assertEqual(set(after) - set(before), {root / "books" / "base.fasl"})

    def test_the_command_prints_the_key_and_writes_nothing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = tree(directory)
            done = subprocess.run([sys.executable, str(ROOT / "tools/extract/world.py"),
                                   "--digest", str(root), "--acl2", "/x/acl2"],
                                  capture_output=True, text=True, timeout=120)
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertEqual(done.stdout.strip(), world.digest(root, "/x/acl2"))
            # The repository's generated files were not rewritten either.
            self.assertEqual(subprocess.run(
                [sys.executable, str(ROOT / "tools/extract/world.py"), "--check"],
                capture_output=True, text=True, timeout=120).returncode, 0)


class HostPrologueTests(unittest.TestCase):
    def test_world_host_assigns_the_closure_reference_itself_when_unset(self):
        text = (ROOT / "tools/extract/world-host.lisp").read_text()
        first_ld = text.index("(ld ")
        prologue = text.index("(if (boundp-global 'fn-image-world-books state)")
        self.assertLess(prologue, first_ld)
        self.assertIn("(f-put-global 'fn-image-world-compiler (@ compiler-enabled) state)",
                      text[prologue:first_ld])
        self.assertIn("(value :fn-image-world-prologue-already-run)", text[prologue:first_ld])


if __name__ == "__main__":
    unittest.main()

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


class VariantTests(unittest.TestCase):
    def test_dtn_world_and_raw_roots_follow_dtn_build(self):
        import core_build
        import host_tokens
        generated = world.render("dtn")
        text = generated[ROOT / "tools/extract/world-dtn.lisp"]
        host = generated[ROOT / "tools/extract/world-host-dtn.lisp"]
        self.assertIn('(include-book "../../books/image-world-dtn")', text)
        self.assertIn("from host/native/build-dtn.lisp:", host)
        block = core_build.raw_block(ROOT, "host/native/build-dtn.lisp")
        self.assertIn('(load "host/native/bp-control-client.lisp")', block)
        self.assertNotIn('(load "host/native/pull-service.lisp")', block)
        self.assertNotEqual(host_tokens.tokens(ROOT),
                            host_tokens.tokens(ROOT, "host/native/build-dtn.lisp"))

    def test_production_name_refuses_developer_before_runtime_or_output(self):
        import os
        with tempfile.TemporaryDirectory() as directory:
            env = dict(os.environ, FN_CORE_NAME="fn-host-dtn",
                       FN_NATIVE_PROFILE="developer", FN_CORE_OUT=directory + "/out")
            done = subprocess.run(["sh", str(ROOT / "tools/extract/core.sh"), str(ROOT)],
                                  env=env, capture_output=True, text=True)
            self.assertEqual(done.returncode, 2)
            self.assertIn("requires production profile", done.stderr)
            self.assertFalse((Path(directory) / "out").exists())

    def test_named_product_refuses_other_variant_before_output(self):
        import os
        for name, variant in (("fn-host-developer", "dtn"), ("fn-host-dtn", "default"),
                              ("fn-core", "unknown")):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                env = dict(os.environ, FN_CORE_NAME=name, FN_EXTRACT_VARIANT=variant,
                           FN_CORE_OUT=directory + "/out")
                done = subprocess.run(["sh", str(ROOT / "tools/extract/core.sh"), str(ROOT)],
                                      env=env, capture_output=True, text=True)
                self.assertEqual(done.returncode, 2)
                self.assertIn("variant", done.stderr)
                self.assertFalse((Path(directory) / "out").exists())

    def test_same_launcher_path_new_toolchain_is_a_new_world(self):
        with tempfile.TemporaryDirectory() as directory:
            root = tree(directory)
            self.assertNotEqual(world.digest(root, "/acl2", toolchain_identity="first"),
                                world.digest(root, "/acl2", toolchain_identity="second"))

    def test_saved_world_binding_refuses_unknown_and_every_mismatched_input(self):
        import json
        import world_binding
        with tempfile.TemporaryDirectory() as directory:
            image = Path(directory) / "world"
            core = Path(str(image) + ".core")
            image.write_bytes(b"launcher")
            core.write_bytes(b"saved core")
            with self.assertRaises(FileNotFoundError):
                world_binding.check(image, "source", "dtn")
            world_binding.record(image).write_text(json.dumps(
                world_binding.binding(image, "source", "dtn")))
            world_binding.check(image, "source", "dtn")
            for key, variant in (("other-source", "dtn"), ("source", "default")):
                with self.assertRaises(ValueError):
                    world_binding.check(image, key, variant)
            for artifact in (image, core):
                original = artifact.read_bytes()
                artifact.write_bytes(original + b"mutation")
                with self.assertRaises(ValueError):
                    world_binding.check(image, "source", "dtn")
                artifact.write_bytes(original)
                world_binding.check(image, "source", "dtn")

    def test_cache_key_is_selected_world_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = tree(directory)
            for source, target in zip(world.world_paths(), world.world_paths("dtn")):
                (root / target).write_bytes((root / source).read_bytes())
            default = world.digest(root)
            dtn = world.digest(root, variant="dtn")
            self.assertNotEqual(default, dtn)
            path = root / "tools/extract/world-host-dtn.lisp"
            path.write_text(path.read_text() + "; DTN-only change\n")
            self.assertEqual(default, world.digest(root))
            self.assertNotEqual(dtn, world.digest(root, variant="dtn"))
            with self.assertRaises(ValueError):
                world.digest(root, variant="unknown")


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

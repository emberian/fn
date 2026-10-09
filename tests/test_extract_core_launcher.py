"""Packaging shape and shell argument safety for the extracted SBCL launcher."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("core_launcher", ROOT / "tools/extract/core_launcher.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class CoreLauncherTests(unittest.TestCase):
    def test_runtime_overrides_and_product_arguments_survive(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = root / "sbcl"
            runtime.write_text('#!/bin/sh\nprintf "%s\\n" "$SBCL_HOME" "$@"\n')
            runtime.chmod(0o755)
            launcher = root / "fn-core"
            launcher.write_text(module.launcher(str(runtime), str(root), str(root / "fn-core.core"),
                                                "32000", "1024KB", "65536"))
            result = subprocess.run(["sh", str(launcher), "--fn", "store", "path with spaces", "status"],
                                    env={"SBCL_USER_ARGS": "--dynamic-space-size 2048"},
                                    capture_output=True, text=True, check=True)
            words = result.stdout.splitlines()
            self.assertEqual(words[0], str(root))
            self.assertEqual(words[-4:], ["--fn", "store", "path with spaces", "status"])
            self.assertIn("(cl-user::xl-toplevel)", words)
            self.assertNotIn("(acl2::sbcl-restart)", words)
            self.assertEqual(words.count("--dynamic-space-size"), 2)
            self.assertLess(words.index("32000"), words.index("2048"))

    def decide_world(self, probe_stdout, probe_rc=0):
        """A recording runtime beside a launcher NAME and its core NAME.core:
        `--fn heap ...` answers PROBE_STDOUT, anything else prints its argv."""
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        runtime = root / "sbcl"
        runtime.write_text('#!/bin/sh\nfor a in "$@"; do [ "$a" = heap ] && '
                           '{ echo "$PROBE"; exit "$PROBE_RC"; }; done\nprintf "%s\\n" "$@"\n')
        runtime.chmod(0o755)
        (root / "fn-core.core").write_bytes(b"\0" * 3 * 1048576)
        launcher = root / "fn-core"
        launcher.write_text(module.launcher(str(runtime), str(root), str(root / "fn-core.core"),
                                            "1772", "1024KB", "20480"))
        launcher.chmod(0o755)
        env = {"PATH": "/usr/bin:/bin", "PROBE": probe_stdout, "PROBE_RC": str(probe_rc)}
        return launcher, env

    def test_a_command_starts_at_the_heap_and_stack_the_core_decides(self):
        # ADMISSION-RESERVES-NOT-REOPEN: fn-core decides per command, as the image does
        launcher, env = self.decide_world("heap=3000 MB profile=development machine=9 MB stack=512 KB threads=1")
        result = subprocess.run(["sh", str(launcher), "--fn", "operator", "/cfg", "run"],
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        words = result.stdout.splitlines()
        sizes = [words[i + 1] for i, w in enumerate(words) if w == "--dynamic-space-size"]
        stacks = [words[i + 1] for i, w in enumerate(words) if w == "--control-stack-size"]
        self.assertEqual((sizes, stacks), (["1772", "3000"], ["1024KB", "512KB"]))
        self.assertEqual(words[-4:], ["--fn", "operator", "/cfg", "run"])

    def test_the_probes_refusal_stops_the_start_by_name(self):
        launcher, env = self.decide_world("refused machine-cannot-hold-profile need=9 MB", 1)
        result = subprocess.run(["sh", str(launcher), "--fn", "operator", "/cfg", "run"],
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "")
        self.assertIn("fn: refused machine-cannot-hold-profile", result.stderr)

    def figures(self, words):
        sizes = [words[i + 1] for i, w in enumerate(words) if w == "--dynamic-space-size"]
        stacks = [words[i + 1] for i, w in enumerate(words) if w == "--control-stack-size"]
        return sizes, stacks

    def test_a_callers_stack_alone_runs_on_the_decided_heap(self):
        # LAUNCHER-STACK-ARGS-REPLACE-DECIDED-HEAP: a stack-only SBCL_USER_ARGS
        # (tests/test_native_served_line_stack.py, 1 MiB) once skipped the
        # decision, so the start ran at the launcher's 1772 and the store's
        # cold startup refused; now the decided figures come first and the
        # caller's stack last, which SBCL takes
        launcher, env = self.decide_world("heap=3000 MB profile=development machine=9 MB stack=512 KB threads=1")
        env["SBCL_USER_ARGS"] = "--control-stack-size 1MB"
        result = subprocess.run(["sh", str(launcher), "--fn", "operator", "/cfg", "run"],
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        sizes, stacks = self.figures(result.stdout.splitlines())
        self.assertEqual((sizes, stacks), (["1772", "3000"], ["1024KB", "512KB", "1MB"]))

    def test_a_callers_stack_alone_is_still_refused_where_the_heap_is(self):
        # composing never skips the probe: a profile the machine cannot hold
        # is refused by name with or without a caller's stack
        launcher, env = self.decide_world("refused machine-cannot-hold-profile need=9 MB", 1)
        env["SBCL_USER_ARGS"] = "--control-stack-size 1MB"
        result = subprocess.run(["sh", str(launcher), "--fn", "operator", "/cfg", "run"],
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "")
        self.assertIn("fn: refused machine-cannot-hold-profile", result.stderr)

    def test_the_tests_named_heap_keeps_a_callers_stack(self):
        launcher, env = self.decide_world("refused never-probed", 1)
        env.update(SBCL_USER_ARGS="--control-stack-size 1MB", FN_TEST_HEAP_MB="700")
        result = subprocess.run(["sh", str(launcher), "--fn", "operator", "/cfg", "run"],
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.figures(result.stdout.splitlines()),
                         (["1772", "700"], ["1024KB", "1MB"]))

    def test_a_callers_heap_is_its_own_figure_and_runs_no_probe(self):
        launcher, env = self.decide_world("refused never-probed", 1)
        env["SBCL_USER_ARGS"] = "--dynamic-space-size 2048 --control-stack-size 1MB"
        result = subprocess.run(["sh", str(launcher), "--fn", "operator", "/cfg", "run"],
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.figures(result.stdout.splitlines()),
                         (["1772", "2048"], ["1024KB", "1MB"]))

    def test_the_developer_launchers_named_heap_keeps_a_callers_stack(self):
        # packaging/fn's developer branch: FN_TEST_HEAP_MB once replaced the
        # caller's SBCL_USER_ARGS whole, dropping its stack
        with tempfile.TemporaryDirectory() as tmp:
            image = Path(tmp) / "fn-host"
            image.write_text('#!/bin/sh\nprintf "%s\\n" "$SBCL_USER_ARGS"\n')
            image.chmod(0o755)
            (Path(tmp) / "fn-host.core").write_bytes(b"\0")
            result = subprocess.run(["sh", str(ROOT / "packaging" / "fn"), "operator", "/cfg", "run"],
                                    env={"PATH": "/usr/bin:/bin", "FN_NATIVE_HOST": str(image),
                                         "FN_TEST_HEAP_MB": "700",
                                         "SBCL_USER_ARGS": "--control-stack-size 1MB"},
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.split(),
                             ["--control-stack-size", "1MB", "--dynamic-space-size", "700"])

    def test_the_image_and_fn_core_carry_the_same_decision(self):
        prelude = module.decision_prelude()
        self.assertIn('fn_decide_heap "$0" "$@"', prelude)
        build = (ROOT / "tools/build_native_host.sh").read_text()
        self.assertIn("cat packaging/launcher-decide.sh", build)
        self.assertIn("/^# BEGIN fn_decide_heap/,/^# END fn_decide_heap/p", build)

    def test_frozen_product_fingerprint_resolves_only_the_known_here_prefix(self):
        import sys
        sys.path.insert(0, str(ROOT / "tools/extract"))
        from owner import fingerprint
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "runtime").mkdir()
            (root / "runtime/sbcl").write_bytes(b"runtime")
            (root / "fn-host.core").write_bytes(b"core")
            image = root / "fn-host"
            image.write_text('#!/bin/sh\nexec "$here/runtime/sbcl" --core "$here/fn-host.core" "$@"\n')
            result = fingerprint(image)
            self.assertEqual(set(result["artifacts"]),
                             {str(image), str(root / "runtime/sbcl"), str(root / "fn-host.core")})
            self.assertEqual(result["source_provenance"], "unknown")

    def test_refuses_paths_the_packaging_parser_cannot_relocate(self):
        for bad in ('/tmp/with space', '/tmp/$(touch bad)', '/tmp/a"b', '/tmp/a\nb'):
            with self.subTest(path=bad), self.assertRaises(ValueError):
                module.launcher(bad, "/home", "/core", "2048", "1024KB")

    def test_refuses_shell_syntax_in_runtime_options(self):
        with self.assertRaises(ValueError):
            module.launcher("/runtime", "/home", "/core", "2048;touch", "1024KB")

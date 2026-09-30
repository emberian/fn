"""Real artifact changes and actual process boundary, with a recording runtime."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "tools/extract/bound_launch.py"
spec = importlib.util.spec_from_file_location("bound_launch", TOOL)
launch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(launch)


class BoundLaunchTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.paths = {role: self.root / role for role in launch.ROLES}
        for role, path in self.paths.items():
            path.write_text(role)
        self.paths["runtime"].write_text(
            '#!' + sys.executable + '\nimport json,os,sys\n'
            'print(json.dumps({"argv":sys.argv[1:],"home":os.environ["SBCL_HOME"],'
            '"override":os.environ.get("SBCL_USER_ARGS"),'
            '"fn":{k:v for k,v in os.environ.items() if k.startswith("FN_")}}))\n')
        self.paths["runtime"].chmod(0o755)
        self.paths["launcher"].write_text(
            "#!/bin/sh\n# literal generated product shape\n"
            "export SBCL_HOME='%s'\n" % self.root
            + 'exec "%s" --tls-limit 65536 --dynamic-space-size 4096 '
              '--control-stack-size 64 --disable-ldb --core "%s" --noinform '
              '${SBCL_USER_ARGS} --end-runtime-options --no-userinit --no-sysinit '
              "--eval '(cl-user::xl-toplevel)' --disable-debugger --end-toplevel-options \"$@\"\n"
            % (self.paths["runtime"], self.paths["core"]))
        self.geometry = {"tls_limit": 65536, "dynamic_space_bytes": 4096 * 2**20,
                         "control_stack_bytes": 64 * 2**20}
        self.capsule = {"schema": 1, "coordinate": {
            role + "_sha256": launch.digest(self.paths[role])
            for role in ("runtime", "source_manifest", "profile")}}
        self.capsule["coordinate"]["options"] = self.geometry
        # A matching file export does not supply any qualified unit.
        self.capsule["units"] = []
        self.paths["capsule"].write_text(json.dumps(self.capsule))
        self.binding = {"schema": 1, "options": self.geometry,
                        "artifacts": {role: {"path": role, "sha256": launch.digest(path)}
                                      for role, path in self.paths.items()}}
        self.manifest = self.root / "binding.json"
        self.pin()

    def pin(self):
        self.manifest.write_text(json.dumps(self.binding))
        self.expected = launch.digest(self.manifest)

    def run_cli(self, *extra, override="", environment=None):
        # The positive fixture declares its environment. In particular macOS
        # harness MallocNanoZone is tested as an explicit refusal below.
        env = {"PATH": os.defpath, "SBCL_USER_ARGS": override}
        env.update(environment or {})
        return subprocess.run([sys.executable, str(TOOL), "--binding", str(self.manifest),
                               "--expected-sha256", self.expected, *extra],
                              env=env,
                              capture_output=True, text=True, timeout=10)

    def bind_environment(self):
        self.library = self.root / "libfn-blake3.dylib"
        self.library.write_bytes(b"recording library artifact, not executable code")
        self.binding["foreign_libraries"] = {"FN_BLAKE3_LIBRARY": {
            "path": self.library.name, "sha256": launch.digest(self.library)}}
        self.binding["environment"] = {"FN_NATIVE_PROFILE": "production"}
        self.capsule["coordinate"]["environment"] = self.binding["environment"].copy()
        self.capsule["coordinate"]["foreign_libraries"] = {
            "FN_BLAKE3_LIBRARY": launch.digest(self.library)}
        self.paths["capsule"].write_text(json.dumps(self.capsule))
        self.binding["artifacts"]["capsule"]["sha256"] = launch.digest(self.paths["capsule"])
        self.pin()

    def test_bound_library_and_profile_reach_actual_process(self):
        self.bind_environment()
        for inherited in ({}, {"FN_NATIVE_PROFILE": "production",
                              "FN_BLAKE3_LIBRARY": str(self.library)}):
            run = self.run_cli(environment=inherited)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(json.loads(run.stdout)["fn"], {
                "FN_NATIVE_PROFILE": "production", "FN_BLAKE3_LIBRARY": str(self.library.resolve())})

    def test_changed_or_missing_library_refuses_before_process(self):
        self.bind_environment()
        self.library.write_bytes(b"changed")
        run = self.run_cli()
        self.assertEqual(run.returncode, 2)
        self.assertIn("foreign-library digest mismatch", run.stderr)
        self.assertEqual(run.stdout, "")
        self.library.unlink()
        run = self.run_cli()
        self.assertEqual(run.returncode, 2)
        self.assertEqual(run.stdout, "")

    def test_foreign_library_or_profile_override_refuses(self):
        self.bind_environment()
        other = self.root / "different-library"
        other.write_bytes(self.library.read_bytes())
        for env in ({"FN_BLAKE3_LIBRARY": str(other)}, {"FN_BLAKE3_LIBRARY": ""},
                    {"FN_NATIVE_PROFILE": "developer"}):
            with self.subTest(environment=env):
                run = self.run_cli(environment=env)
                self.assertEqual(run.returncode, 2)
                self.assertEqual(run.stdout, "")

    def test_unbound_effectful_environment_refuses(self):
        for key in ("FN_BLAKE3_LIBRARY", "FN_BP_TEST_PROFILE", "FN_EXTRACT_VARIANT",
                    "LD_LIBRARY_PATH", "DYLD_INSERT_LIBRARIES", "MALLOC_CONF",
                    "MallocNanoZone", "GLIBC_TUNABLES", "ASAN_OPTIONS", "SBCL_FAKE"):
            with self.subTest(key=key):
                # Direct resolver covers loader variables macOS may strip when
                # spawning a platform executable; subprocess covers its path too.
                with self.assertRaises(launch.BindingError):
                    launch.resolve_plan(self.manifest, self.expected, environment={key: "1"})
                if not key.startswith("DYLD_"):
                    run = self.run_cli(environment={key: "1"})
                    self.assertEqual(run.returncode, 2)
                    self.assertEqual(run.stdout, "")

    def test_environment_capsule_mismatch_refuses_even_when_rehashed(self):
        self.bind_environment()
        self.capsule["coordinate"]["environment"]["FN_NATIVE_PROFILE"] = "developer"
        self.paths["capsule"].write_text(json.dumps(self.capsule))
        self.binding["artifacts"]["capsule"]["sha256"] = launch.digest(self.paths["capsule"])
        self.pin()
        run = self.run_cli()
        self.assertEqual(run.returncode, 2)
        self.assertIn("capsule export", run.stderr)
        self.assertEqual(run.stdout, "")

    def test_library_selectors_cannot_be_bound_as_unhashed_scalars(self):
        self.binding["environment"] = {"FN_BLAKE3_LIBRARY": "/unhashed"}
        self.pin()
        run = self.run_cli()
        self.assertEqual(run.returncode, 2)
        self.assertIn("invalid bound FN selector", run.stderr)

    def emit_package(self, *extra):
        self.output = self.root / "package-binding.json"
        command = [sys.executable, str(TOOL.with_name("bind_package.py")),
                   "--output", str(self.output)]
        for role, path in self.paths.items():
            command.extend(["--" + role.replace("_", "-"), str(path)])
        return subprocess.run(command + list(extra), env={"PATH": os.defpath},
                              capture_output=True, text=True, timeout=10)

    def test_emitted_package_binding_launches_actual_recording_runtime(self):
        self.bind_environment()
        run = self.emit_package("--environment", "FN_NATIVE_PROFILE=production",
                                "--library", "FN_BLAKE3_LIBRARY=" + str(self.library))
        self.assertEqual(run.returncode, 0, run.stderr)
        result = json.loads(run.stdout)
        self.assertEqual(result["qualification"], "not-established")
        self.assertEqual(result["sha256"], launch.digest(self.output))
        self.manifest, self.expected = self.output, result["sha256"]
        launched = self.run_cli()
        self.assertEqual(launched.returncode, 0, launched.stderr)
        self.assertEqual(json.loads(launched.stdout)["fn"]["FN_BLAKE3_LIBRARY"],
                         str(self.library.resolve()))
        self.assertEqual(self.capsule["units"], [])

    def test_emitter_never_replaces_existing_binding(self):
        run = self.emit_package()
        self.assertEqual(run.returncode, 0, run.stderr)
        before = self.output.read_bytes()
        run = self.emit_package()
        self.assertEqual(run.returncode, 2)
        self.assertEqual(self.output.read_bytes(), before)

    def test_emitter_requires_actual_matching_capsule_export(self):
        self.capsule["coordinate"]["profile_sha256"] = "0" * 64
        self.paths["capsule"].write_text(json.dumps(self.capsule))
        run = self.emit_package()
        self.assertEqual(run.returncode, 2)
        self.assertIn("capsule export", run.stderr)
        self.assertFalse(self.output.exists())
        self.assertEqual(list(self.root.glob(".fn-binding-*")), [])

    def test_emitter_requires_all_artifacts_to_exist(self):
        self.paths["capsule"].unlink()
        run = self.emit_package()
        self.assertEqual(run.returncode, 2)
        self.assertFalse(self.output.exists())

    def test_emitter_refuses_duplicate_or_unbound_selectors(self):
        for args in (("--environment", "FN_A=one", "--environment", "FN_A=two"),
                     ("--environment", "FN_BLAKE3_LIBRARY=/unhashed"),
                     ("--environment", "LD_PRELOAD=/unbound")):
            with self.subTest(args=args):
                run = self.emit_package(*args)
                self.assertEqual(run.returncode, 2)
                self.assertFalse(self.output.exists())

    def test_actual_process_gets_only_fixed_geometry_and_literal_app_arguments(self):
        run = self.run_cli("--", "--fn", "store", "path with spaces", "$(literal)",
                           override="--dynamic-space-size 4GB --control-stack-size 65536KB")
        self.assertEqual(run.returncode, 0, run.stderr)
        result = json.loads(run.stdout)
        self.assertEqual(result["argv"][-4:], ["--fn", "store", "path with spaces", "$(literal)"])
        self.assertEqual(result["argv"].count("--dynamic-space-size"), 1)
        self.assertEqual(result["home"], str(self.root))
        self.assertIsNone(result["override"])

    def test_each_real_artifact_mutation_refuses_before_process(self):
        for role, path in self.paths.items():
            with self.subTest(role=role):
                old = path.read_bytes()
                path.write_bytes(old + b"changed")
                run = self.run_cli()
                self.assertEqual(run.returncode, 2)
                self.assertEqual(run.stdout, "")
                self.assertIn("digest mismatch", run.stderr)
                path.write_bytes(old)

    def test_binding_itself_is_pinned(self):
        self.manifest.write_text(self.manifest.read_text() + " ")
        self.assertEqual(self.run_cli().returncode, 2)

    def test_missing_artifact_refuses_before_process(self):
        self.paths["profile"].unlink()
        run = self.run_cli()
        self.assertEqual(run.returncode, 2)
        self.assertEqual(run.stdout, "")

    def test_options_cannot_change_geometry_or_inject_runtime_code(self):
        for args in ("--dynamic-space-size 2048", "--tls-limit 1",
                     "--control-stack-size 32", "--eval (quit)", "--core /other",
                     "--tls-limit 65536 --tls-limit 65536", "--tls-limit",
                     "--dynamic-space-size 4096;touch", "--tls-limit 65536KB"):
            with self.subTest(args=args):
                run = self.run_cli(override=args)
                self.assertEqual(run.returncode, 2, run.stdout + run.stderr)
                self.assertEqual(run.stdout, "")

    def test_launcher_geometry_must_match_pinned_binding(self):
        path = self.paths["launcher"]
        path.write_text(path.read_text().replace("--dynamic-space-size 4096", "--dynamic-space-size 2048"))
        self.binding["artifacts"]["launcher"]["sha256"] = launch.digest(path)
        self.pin()
        with self.assertRaisesRegex(launch.BindingError, "geometry"):
            launch.resolve(self.manifest, self.expected)

    def test_launcher_cannot_select_an_unbound_core(self):
        path = self.paths["launcher"]
        path.write_text(path.read_text().replace(str(self.paths["core"]), "/other/core"))
        self.binding["artifacts"]["launcher"]["sha256"] = launch.digest(path)
        self.pin()
        with self.assertRaisesRegex(launch.BindingError, "different runtime or core"):
            launch.resolve(self.manifest, self.expected)

    def test_capsule_coordinate_must_match_even_if_rehashed(self):
        self.capsule["coordinate"]["profile_sha256"] = "0" * 64
        self.paths["capsule"].write_text(json.dumps(self.capsule))
        self.binding["artifacts"]["capsule"]["sha256"] = launch.digest(self.paths["capsule"])
        self.pin()
        with self.assertRaisesRegex(launch.BindingError, "capsule export"):
            launch.resolve(self.manifest, self.expected)

    def test_identity_check_does_not_claim_units_qualified(self):
        run = self.run_cli("--check")
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)["qualification"], "not-established")
        self.assertEqual(self.capsule["units"], [])

    def test_unrecognized_launcher_code_is_not_executed(self):
        for text in ("#!/bin/sh\ntouch /tmp/never\n", self.paths["launcher"].read_text().replace(
                "(cl-user::xl-toplevel)", "(evil)")):
            with self.subTest(text=text), self.assertRaises(launch.BindingError):
                launch.parse_launcher(text)


if __name__ == "__main__":
    unittest.main()

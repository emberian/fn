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
import core_launcher  # noqa: E402  (bound_launch put tools/extract on sys.path)

MIB = 2**20
# The recording runtime: `--fn heap -- ...` is the core's heap probe (its
# answer from probe.json beside it, every call logged in probes.log); any
# other command prints what it was started with.
RUNTIME = (
    "import json,os,sys\n"
    "from pathlib import Path\n"
    "here=Path(sys.argv[0]).parent; a=sys.argv[1:]\n"
    "if a[a.index('--fn')+1:a.index('--fn')+2]==['heap'] if '--fn' in a else False:\n"
    "    open(here/'probes.log','a').write(json.dumps(a)+'\\n')\n"
    "    p=json.loads((here/'probe.json').read_text()) if (here/'probe.json').exists() else {}\n"
    "    print(p.get('stdout','heap=2048 MB profile=small machine=9000 MB stack=1024 KB threads=1'))\n"
    "    sys.exit(p.get('rc',0))\n"
    "print(json.dumps({'argv':a,'home':os.environ['SBCL_HOME'],"
    "'override':os.environ.get('SBCL_USER_ARGS'),"
    "'fn':{k:v for k,v in os.environ.items() if k.startswith('FN_')}}))\n")


class BoundLaunchTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.paths = {role: self.root / role for role in launch.ROLES}
        for role, path in self.paths.items():
            path.write_text(role)
        self.paths["runtime"].write_text('#!' + sys.executable + '\n' + RUNTIME)
        self.paths["runtime"].chmod(0o755)
        self.paths["launcher"].write_text(core_launcher.launcher(
            str(self.paths["runtime"]), str(self.root), str(self.paths["core"]),
            "4096", "64", "65536"))
        self.geometry = {"tls_limit": 65536, "dynamic_space_ceiling_bytes": 8192 * MIB}
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
                   "--output", str(self.output), "--heap-ceiling-mb", "8192"]
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

    def test_a_callers_figure_within_the_ceiling_is_its_own_and_args_stay_literal(self):
        run = self.run_cli("--", "--fn", "store", "path with spaces", "$(literal)",
                           override="--dynamic-space-size 4GB --control-stack-size 65536KB")
        self.assertEqual(run.returncode, 0, run.stderr)
        result = json.loads(run.stdout)
        argv = result["argv"]
        self.assertEqual(argv[-4:], ["--fn", "store", "path with spaces", "$(literal)"])
        self.assertEqual(argv.count("--dynamic-space-size"), 1)
        self.assertEqual(argv[argv.index("--dynamic-space-size") + 1], "4GB")
        self.assertEqual(argv[argv.index("--control-stack-size") + 1], "65536KB")
        self.assertEqual(result["home"], str(self.root))
        self.assertIsNone(result["override"])
        self.assertFalse((self.root / "probes.log").exists())

    def test_a_command_starts_at_the_heap_and_stack_the_core_decides(self):
        run = self.run_cli("--", "--fn", "operator", "/cfg", "run")
        self.assertEqual(run.returncode, 0, run.stderr)
        argv = json.loads(run.stdout)["argv"]
        self.assertEqual(argv[argv.index("--dynamic-space-size") + 1], "2048")
        self.assertEqual(argv[argv.index("--control-stack-size") + 1], "1024KB")
        self.assertEqual(argv[-4:], ["--fn", "operator", "/cfg", "run"])
        probes = [json.loads(line) for line in (self.root / "probes.log").read_text().splitlines()]
        self.assertEqual(len(probes), 1)
        probe = probes[0]
        # at the core's size plus two 64 MiB nurseries, packaging/fn's boot figure
        boot = (self.paths["core"].stat().st_size + MIB - 1) // MIB + 128
        self.assertEqual(probe[probe.index("--dynamic-space-size") + 1], str(boot))
        self.assertEqual(probe[-6:], ["--fn", "heap", "--", "operator", "/cfg", "run"])

    def test_a_decided_heap_above_the_ceiling_is_a_named_refusal(self):
        (self.root / "probe.json").write_text(json.dumps(
            {"stdout": "heap=9000 MB profile=development machine=126288 MB stack=1024 KB threads=1"}))
        run = self.run_cli("--", "--fn", "operator", "/cfg", "run")
        self.assertEqual(run.returncode, 1, run.stderr)
        self.assertEqual(run.stdout, "")
        self.assertIn("fn: refused heap-above-ceiling decided=9000 MB ceiling=8192 MB", run.stderr)

    def test_the_probes_refusal_is_the_launchs_and_a_silent_probe_is_a_fault(self):
        (self.root / "probe.json").write_text(json.dumps(
            {"stdout": "refused machine-cannot-hold-profile need=9 MB machine=1 MB", "rc": 1}))
        run = self.run_cli("--", "--fn", "operator", "/cfg", "run")
        self.assertEqual((run.returncode, run.stdout), (1, ""))
        self.assertIn("fn: refused machine-cannot-hold-profile", run.stderr)
        (self.root / "probe.json").write_text(json.dumps({"stdout": "", "rc": 139}))
        run = self.run_cli("--", "--fn", "operator", "/cfg", "run")
        self.assertEqual((run.returncode, run.stdout), (4, ""))
        self.assertIn("heap-probe-did-not-run exit=139", run.stderr)

    def test_the_heap_command_itself_runs_at_the_launchers_default(self):
        run = self.run_cli("--", "--fn", "heap", "--", "operator", "/cfg", "run")
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertTrue(run.stdout.startswith("heap="))
        probe = json.loads((self.root / "probes.log").read_text().splitlines()[0])
        self.assertEqual(probe[probe.index("--dynamic-space-size") + 1], "4096")

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

    def test_options_cannot_pass_the_bounds_or_inject_runtime_code(self):
        for args in ("--dynamic-space-size 8193", "--dynamic-space-size 9GB", "--tls-limit 1",
                     "--eval (quit)", "--core /other",
                     "--tls-limit 65536 --tls-limit 65536", "--tls-limit",
                     "--dynamic-space-size 4096;touch", "--tls-limit 65536KB"):
            with self.subTest(args=args):
                run = self.run_cli(override=args)
                self.assertEqual(run.returncode, 2, run.stdout + run.stderr)
                self.assertEqual(run.stdout, "")

    def test_launcher_geometry_must_match_pinned_binding(self):
        path = self.paths["launcher"]
        original = path.read_text()
        for old, new in (("--dynamic-space-size 4096", "--dynamic-space-size 16384"),
                         ("--tls-limit 65536", "--tls-limit 4096")):
            with self.subTest(new=new):
                path.write_text(original.replace(old, new))
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
        launcher = self.paths["launcher"].read_text()
        exec_only = "#!/bin/sh\n" + launcher[launcher.index("export SBCL_HOME="):]
        for text in ("#!/bin/sh\ntouch /tmp/never\n", launcher.replace(
                "(cl-user::xl-toplevel)", "(evil)"), exec_only,
                launcher.replace("fn_decide_command_heap \"$@\"", "touch /tmp/never")):
            with self.subTest(text=text), self.assertRaises(launch.BindingError):
                launch.parse_launcher(text)


if __name__ == "__main__":
    unittest.main()

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
            '"override":os.environ.get("SBCL_USER_ARGS")}))\n')
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

    def run_cli(self, *extra, override=""):
        return subprocess.run([sys.executable, str(TOOL), "--binding", str(self.manifest),
                               "--expected-sha256", self.expected, *extra],
                              env=dict(os.environ, SBCL_USER_ARGS=override),
                              capture_output=True, text=True, timeout=10)

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

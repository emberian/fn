"""tools/hbox_native.sh's box script, read through --dry-run (no ssh)."""
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "hbox_native.sh"


def dry(*args):
    return subprocess.run(
        ["sh", str(SCRIPT), "--dry-run", "--name", "t", "--label", "l", *args],
        cwd=ROOT, capture_output=True, text=True, timeout=30)


def image_lines(out):
    return [line for line in out.splitlines() if line.startswith("step image-")]


class HboxNativeDryRunTests(unittest.TestCase):
    def test_default_builds_the_developer_image_only(self):
        answer = dry("HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        lines = image_lines(answer.stdout)
        self.assertEqual(len(lines), 1)
        self.assertIn("FN_NATIVE_PROFILE=developer FN_NATIVE_WORLD=full FN_NATIVE_BUILD=host/native/build.lisp "
                      "FN_NATIVE_IMAGE=build/fn-host-developer", lines[0])
        self.assertNotIn("--profile dtn", answer.stdout)
        self.assertNotIn("FN_NATIVE_BP_HOST", answer.stdout)

    def test_a_big_memory_scope_waits_on_the_box_wide_lock(self):
        big = dry("--mem", "80G", "HEAD", "tests.test_native_owner")
        self.assertEqual(big.returncode, 0, big.stderr)
        line = [l for l in big.stdout.splitlines() if l.startswith("tstep test-")][0]
        self.assertIn("flock /tank/fn/scratch/.hbox-native-bigmem.lock env", line)
        small = dry("--mem", "24G", "HEAD", "tests.test_native_owner")
        self.assertNotIn("flock", [l for l in small.stdout.splitlines()
                                   if l.startswith("tstep test-")][0])

    def test_each_image_gets_the_runbooks_triple(self):
        answer = dry("--images", "production,developer,dtn,dtn-developer",
                     "HEAD", "tests.test_bp_service_native")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        text = "\n".join(image_lines(answer.stdout))
        # tools/runbooks/hbox-image-build.sh's four build lines.
        for triple in (
                "FN_NATIVE_PROFILE=production FN_NATIVE_WORLD=stripped FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host ",
                "FN_NATIVE_PROFILE=developer FN_NATIVE_WORLD=full FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer ",
                "FN_NATIVE_PROFILE=production FN_NATIVE_WORLD=stripped FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn ",
                "FN_NATIVE_PROFILE=developer FN_NATIVE_WORLD=full FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn-developer "):
            self.assertIn(triple, text)
        # Both DTN images: the tests keep their own default.
        self.assertNotIn("FN_NATIVE_BP_HOST", answer.stdout)

    def test_a_dtn_image_acquires_and_certifies_the_dtn_profile_first(self):
        answer = dry("--images", "dtn-developer", "HEAD", "tests.test_bp_service_native")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        lines = answer.stdout.splitlines()
        index = {name: next(i for i, line in enumerate(lines) if needle in line)
                 for name, needle in (
                     ("roots", "roots --profile dtn >>"),
                     ("certify", "step certify "),
                     ("acquire", "step acquire-dtn "),
                     ("validate", "step validate-dtn "),
                     ("image", "step image-dtn-developer "),
                     ("bp-host", "export FN_NATIVE_BP_HOST=$T/build/fn-host-dtn-developer"),
                     ("test", "tstep test-tests.test_bp_service_native "))}
        self.assertEqual(sorted(index, key=index.get),
                         ["roots", "certify", "acquire", "validate", "image", "bp-host", "test"])

    def test_the_prof_image_follows_this_runs_certify(self):
        # served-columns: a profiling image built in a copied tree lacked
        # books its world loads; here it follows the run's own certify.
        answer = dry("--images", "developer,prof", "HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        lines = answer.stdout.splitlines()
        certify = next(i for i, line in enumerate(lines) if line.startswith("step certify "))
        validate = next(i for i, line in enumerate(lines) if line.startswith("step validate "))
        prof = [i for i, line in enumerate(lines) if line.startswith("step image-prof ")]
        self.assertEqual(len(prof), 1)
        self.assertLess(certify, validate)
        self.assertLess(validate, prof[0])
        self.assertIn("swarm-build sh tools/profile/build_native_profile.sh build/fn-host-prof",
                      lines[prof[0]])
        self.assertIn("FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k", lines[prof[0]])

    def test_run_log_carries_the_boxs_load(self):
        # feed-queue: one case read 20.9 s and then 2.7 s on a loaded box.
        answer = dry("HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        script = answer.stdout
        self.assertIn('echo "== load at start: $(uptime)"', script)
        finish = script[script.index("finish() {"):]
        self.assertIn('echo "== load at end: $(uptime)"', finish.split("}")[0])
        tstep = script[script.index("tstep() {"):]
        self.assertIn("/proc/loadavg", tstep.split("\n}")[0])

    def test_explicit_env_is_exported_and_wins(self):
        answer = dry("--images", "dtn-developer", "--env", "FN_NATIVE_BP_HOST=/x/y",
                     "--env", "FN_OTHER=1", "HEAD", "tests.test_bp_service_native")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertIn("export FN_NATIVE_BP_HOST=/x/y", answer.stdout)
        self.assertIn("export FN_OTHER=1", answer.stdout)
        self.assertNotIn("fn-host-dtn-developer\n", answer.stdout.split("step image-")[0])
        self.assertEqual(answer.stdout.count("export FN_NATIVE_BP_HOST"), 1)

    def test_refusals(self):
        for args in (["--images", "dtn,bogus"], ["--env", "lower=1"],
                     ["--env", "FN_X=a b"], ["--env", "FN_X=$(id)"]):
            answer = dry(*args, "HEAD", "tests.test_native_owner")
            self.assertEqual(answer.returncode, 2, (args, answer.stdout))


    def test_options_may_follow_rev_and_modules(self):
        # PKT-490 (3): `hbox_native.sh HEAD MODULE --images ...` was refused
        # as a bad module name.
        after = dry("HEAD", "tests.test_bp_service_native", "--images", "dtn-developer")
        before = dry("--images", "dtn-developer", "HEAD", "tests.test_bp_service_native")
        self.assertEqual(after.returncode, 0, after.stderr)
        self.assertEqual(after.stdout, before.stdout)

    def test_a_reader_of_an_unbuilt_image_is_refused_by_name(self):
        # PKT-437 (2): the default run builds only the developer image, and
        # this module reads FN_NATIVE_HOST (the production image).
        answer = dry("HEAD", "tests.test_native_hybrid_author")
        self.assertEqual(answer.returncode, 2, answer.stdout)
        self.assertEqual(answer.stdout, "")
        self.assertIn("tests.test_native_hybrid_author reads FN_NATIVE_HOST: build the "
                      "production image with --images developer,production", answer.stderr)
        # Named by --env instead of built: no refusal.
        given = dry("--env", "FN_NATIVE_HOST=/x/fn-host", "HEAD", "tests.test_native_hybrid_author")
        self.assertEqual(given.returncode, 0, given.stderr)

    def test_each_module_gets_the_variables_it_reads(self):
        answer = dry("--images", "developer,production", "HEAD",
                     "tests.test_native_hybrid_author", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        lines = answer.stdout.splitlines()
        hybrid = next(line for line in lines
                      if line.startswith("tstep test-tests.test_native_hybrid_author "))
        for assignment in ("FN_NATIVE_HOST=$T/build/fn-host ", "FN_RUN_HYBRID_E2E=1 ",
                           "FN_TEST_OPENSSL=$FN_TEST_OPENSSL_BIN "):
            self.assertIn(assignment, hybrid)
        self.assertIn("test_budget.py --one tests.test_native_hybrid_author", hybrid)
        owner = next(line for line in lines if line.startswith("tstep test-tests.test_native_owner "))
        self.assertIn("FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer ", owner)
        self.assertNotIn("FN_NATIVE_HOST=", owner)
        # The images are checked on the box before the first test.
        need = lines.index("need tests.test_native_hybrid_author FN_NATIVE_HOST $T/build/fn-host")
        self.assertLess(need, lines.index(hybrid))

    def test_an_image_read_through_an_imported_helper_is_set_and_never_refused(self):
        # PKT-490 (2): tests.test_native_bounds_join reads FN_NATIVE_HOST only
        # through test_native_operator_verbs' IMAGE (exposure-reply-size set it
        # by hand).  Built: it is set.  Not built: a note, not a refusal.
        both = dry("--images", "developer,production", "HEAD", "tests.test_native_bounds_join")
        self.assertEqual(both.returncode, 0, both.stderr)
        join = next(line for line in both.stdout.splitlines()
                    if line.startswith("tstep test-tests.test_native_bounds_join "))
        self.assertIn("FN_NATIVE_HOST=$T/build/fn-host ", join)
        self.assertIn("FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer ", join)
        developer = dry("HEAD", "tests.test_native_bounds_join")
        self.assertEqual(developer.returncode, 0, developer.stderr)
        self.assertIn("reads FN_NATIVE_HOST through a tests/ helper", developer.stdout + developer.stderr)
        self.assertNotIn("FN_NATIVE_HOST=", next(
            line for line in developer.stdout.splitlines()
            if line.startswith("tstep test-tests.test_native_bounds_join ")))

    def test_every_image_or_opt_in_variable_a_native_module_reads_is_classified(self):
        import sys
        sys.path.insert(0, str(ROOT))
        from tools import native_env
        known = set(native_env.IMAGES) | set(native_env.FIXED) | set(native_env.MANUAL)
        unclassified = sorted(
            name for name in native_env.readers()
            if (name.endswith("_HOST") or name.startswith("FN_RUN_")) and name not in known)
        self.assertEqual(unclassified, [])
        # FN_NATIVE_HOST is only ever the production image (operator-daily-2).
        self.assertEqual(native_env.IMAGES["FN_NATIVE_HOST"], ("production",))

    def test_a_test_tool_reaches_a_module_that_runs_a_helpers_tests(self):
        # operator_verdicts subclasses control_filing's tests, whose signed
        # withdrawal makes ML-DSA-65 keys with FN_TEST_OPENSSL; without it
        # the system openssl (3.3.1, no ML-DSA) failed it (dev-health).
        answer = dry("--images", "developer,production", "HEAD",
                     "tests.test_native_operator_verdicts")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        line = next(line for line in answer.stdout.splitlines()
                    if line.startswith("tstep test-tests.test_native_operator_verdicts "))
        self.assertIn("FN_TEST_OPENSSL=$FN_TEST_OPENSSL_BIN ", line)
        self.assertNotIn("FN_RUN_HYBRID_E2E", line)


class IdentityTests(unittest.TestCase):
    """The production image's four identity variables (wire-bounds typed them)."""

    def test_identity_hashes_launcher_core_and_the_runtime_it_execs(self):
        import hashlib
        import sys
        import tempfile
        sys.path.insert(0, str(ROOT))
        from tools import native_env
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            runtime = base / "sbcl"
            runtime.write_bytes(b"runtime")
            image = base / "fn-host"
            image.write_text(f'#!/bin/sh\nexec "{runtime}" --core "$0.core" "$@"\n')
            Path(str(image) + ".core").write_bytes(b"core")
            found = native_env.image_identity(image, "abc123")
            answer = subprocess.run(
                [sys.executable, str(ROOT / "tools" / "native_env.py"), "identity",
                 "--image", str(image), "--source", "abc123", "--export"],
                capture_output=True, text=True, timeout=30)
        sha = lambda data: hashlib.sha256(data).hexdigest()  # noqa: E731
        self.assertEqual(found, {
            "FN_NATIVE_LAUNCHER_SHA256": sha(image_text(runtime).encode()),
            "FN_NATIVE_RUNTIME_SHA256": sha(b"runtime"),
            "FN_NATIVE_CORE_SHA256": sha(b"core"),
            "FN_NATIVE_IMAGE_SOURCE_SHA": "abc123"})
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertIn(f"export FN_NATIVE_CORE_SHA256={sha(b'core')}", answer.stdout)
        self.assertEqual(len(answer.stdout.splitlines()), 4)

    def test_the_box_computes_identity_with_the_worktrees_source(self):
        answer = dry("--images", "developer,production", ".", "tests.test_native_peering")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        line = next(line for line in answer.stdout.splitlines()
                    if "native_env.py identity" in line)
        self.assertIn('--image "build/fn-host"', line)
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                              text=True).stdout.strip()
        self.assertIn(f"--source {head}", line)
        self.assertNotIn("FN_NATIVE_IMAGE_SOURCE_SHA=.", answer.stdout)

    def test_a_reader_of_identity_without_a_production_image_is_refused(self):
        answer = dry("--images", "developer", "HEAD", "tests.test_native_admin")
        self.assertEqual(answer.returncode, 2)
        self.assertIn("reads FN_NATIVE_LAUNCHER_SHA256: build the production image",
                      answer.stderr)

    def test_the_run_is_a_copy_so_an_edit_mid_run_cannot_reach_it(self):
        # The script's head up to HERE=, then two probes, in a scratch tree:
        # it runs from a private copy, HERE is still the tree, and the copy
        # is gone when it exits.
        import os
        import shutil
        text = SCRIPT.read_text()
        head = text[:text.index("\nHERE=") + 1] + text[text.index("\nHERE=") + 1:].split("\n", 1)[0]
        tree = ROOT / "build" / "hbox-native-copy-test"
        (tree / "tools").mkdir(parents=True, exist_ok=True)
        self.addCleanup(shutil.rmtree, tree, True)
        (tree / "tools" / "hbox_native.sh").write_text(
            head + '\necho "COPY=$FN_HBOX_NATIVE_COPY"\necho "RUNNING=$0"\necho "HERE=$HERE"\n')
        shutil.copy(ROOT / "tools" / "wait_for.sh", tree / "tools" / "wait_for.sh")
        env = {k: v for k, v in os.environ.items() if not k.startswith("FN_HBOX_NATIVE_")}
        probe = subprocess.run(["sh", str(tree / "tools" / "hbox_native.sh")], cwd=ROOT,
                               capture_output=True, text=True, timeout=30, env=env)
        fields = dict(line.split("=", 1) for line in probe.stdout.splitlines() if "=" in line)
        self.assertEqual(probe.returncode, 0, probe.stderr)
        self.assertTrue(fields["RUNNING"].startswith(fields["COPY"] + "/"), fields)
        self.assertNotIn(str(tree), fields["COPY"])
        self.assertEqual(fields["HERE"], str(tree.resolve()))
        self.assertFalse(Path(fields["COPY"]).exists())


class HarnessBudgetTests(unittest.TestCase):
    def test_one_place_names_the_harness_stores_budget(self):
        import sys
        sys.path.insert(0, str(ROOT))
        from tools import native_env
        self.assertEqual(native_env.harness_store_env({})["FN_INIT_BUDGET_MB"],
                         native_env.HARNESS_INIT_BUDGET_MB)
        self.assertEqual(native_env.harness_store_env({"FN_INIT_BUDGET_MB": "5"})
                         ["FN_INIT_BUDGET_MB"], "5")
        # No harness types the figure itself (four did, 2026-09-27).
        typed = subprocess.run(["git", "grep", "-n", "-E", "FN_INIT_BUDGET_MB.{0,40}9830[4]",
                                "--", "tools", "tests"],
                               cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(typed.stdout, "")


def image_text(runtime):
    return f'#!/bin/sh\nexec "{runtime}" --core "$0.core" "$@"\n'


if __name__ == "__main__":
    unittest.main()

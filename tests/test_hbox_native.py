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
        self.assertIn("FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp "
                      "FN_NATIVE_IMAGE=build/fn-host-developer", lines[0])
        self.assertNotIn("--profile dtn", answer.stdout)
        self.assertNotIn("FN_NATIVE_BP_HOST", answer.stdout)

    def test_each_image_gets_the_runbooks_triple(self):
        answer = dry("--images", "production,developer,dtn,dtn-developer",
                     "HEAD", "tests.test_bp_service_native")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        text = "\n".join(image_lines(answer.stdout))
        # tools/runbooks/hbox-image-build.sh's four build lines.
        for triple in (
                "FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host ",
                "FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer ",
                "FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn ",
                "FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn-developer "):
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
                           "FN_TEST_OPENSSL=$FN_OPENSSL_PREFIX/bin/openssl "):
            self.assertIn(assignment, hybrid)
        self.assertIn("test_budget.py --one tests.test_native_hybrid_author", hybrid)
        owner = next(line for line in lines if line.startswith("tstep test-tests.test_native_owner "))
        self.assertIn("FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer ", owner)
        self.assertNotIn("FN_NATIVE_HOST=", owner)
        # The images are checked on the box before the first test.
        need = lines.index("need tests.test_native_hybrid_author FN_NATIVE_HOST $T/build/fn-host")
        self.assertLess(need, lines.index(hybrid))

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


if __name__ == "__main__":
    unittest.main()

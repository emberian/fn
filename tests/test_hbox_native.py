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
    def test_an_image_set_links_prebuilt_images_instead_of_building(self):
        sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                             text=True, check=True).stdout.strip()
        answer = dry("--image-set", sha, "--images", "developer,production", "HEAD",
                     "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertEqual(image_lines(answer.stdout),
                         [f"step image-set python3 $S/bin/image_set.py link --base /tank/fn/images {sha} $T "
                          "developer production"])
        self.assertNotIn("certify_books", answer.stdout)
        self.assertIn(f"--source {sha}", answer.stdout)
        refused = dry("--image-set", sha, "--images", "prof", "HEAD", "tests.test_native_owner")
        self.assertEqual(refused.returncode, 2)
        self.assertIn("an image set holds", refused.stderr)
        self.assertEqual(dry("--image-set", "nope", "HEAD", "tests.test_native_owner")
                         .returncode, 2)

    def test_reuse_image_links_an_earlier_runs_images_instead_of_building(self):
        answer = dry("--reuse-image", "crem/native-crem3-786b", "--images",
                     "developer,production", "HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertEqual(image_lines(answer.stdout),
                         ["step image-reuse python3 $S/bin/image_set.py link-run "
                          "/tank/fn/scratch/crem/native-crem3-786b $T developer production"])
        self.assertNotIn("certify_books", answer.stdout)
        # The identity source is the reused run's, read on the box.
        self.assertIn("--source $(cat build/REUSED_SOURCE)", answer.stdout)
        # A bare native-LABEL is under this run's --name.
        bare = dry("--reuse-image", "native-x", "HEAD", "tests.test_native_owner")
        self.assertIn("link-run /tank/fn/scratch/t/native-x $T", bare.stdout)
        for bad, why in ((["--reuse-image", "t/native-l"], "this run's own tree"),
                         (["--reuse-image", "../etc"], "--reuse-image takes"),
                         (["--reuse-image", "x/native-y", "--image-set", "a" * 40],
                          "give one"),
                         (["--reuse-image", "x/native-y", "--images", "prof"],
                          "an image set holds")):
            refused = dry(*bad, "HEAD", "tests.test_native_owner")
            self.assertEqual(refused.returncode, 2, bad)
            self.assertIn(why, refused.stderr)

    def test_no_build_reships_the_tree_but_keeps_its_certificates(self):
        # A --no-build re-ship deleted the tree's .cert files; REPL sessions
        # there then refused include-book (2026-09-28).
        import os
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "calls"
            for tool in ("ssh", "rsync"):
                stub = Path(directory) / tool
                stub.write_text('#!/bin/sh\necho "%s $*" >> %s\ncat > /dev/null\nexit 0\n'
                                % (tool, log))
                stub.chmod(0o755)
            env = {**os.environ, "PATH": f"{directory}:{os.environ['PATH']}"}
            env["FN_HBOX"] = "hbox"
            for rev, keeps in ((".", "--exclude=*.cert"), ("HEAD", "! -name '*.cert'")):
                log.write_text("")
                done = subprocess.run(["sh", str(SCRIPT), "--detach", "--no-build", "--name", "t",
                                       "--label", "l", rev, "tests.test_native_owner"],
                                      cwd=ROOT, env=env, capture_output=True, text=True,
                                      timeout=120)
                self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
                self.assertIn(keeps, log.read_text())
                log.write_text("")
                subprocess.run(["sh", str(SCRIPT), "--detach", "--name", "t", "--label", "l",
                                rev, "tests.test_native_owner"], cwd=ROOT, env=env,
                               capture_output=True, text=True, timeout=120)
                self.assertNotIn(".cert", log.read_text())

    def test_default_builds_the_developer_image_only(self):
        answer = dry("HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        lines = image_lines(answer.stdout)
        self.assertEqual(len(lines), 1)
        self.assertIn("FN_NATIVE_PROFILE=developer FN_NATIVE_WORLD=full FN_NATIVE_BUILD=host/native/build.lisp "
                      "FN_NATIVE_IMAGE=build/fn-host-developer", lines[0])
        self.assertNotIn("--profile dtn", answer.stdout)
        self.assertNotIn("FN_NATIVE_BP_HOST", answer.stdout)

    def test_bp_service_native_takes_the_dtn_developer_image(self):
        import sys
        sys.path.insert(0, str(ROOT))
        from tools import native_env
        lines, _refused, _notes = native_env.plan(
            ["developer", "production", "dtn", "dtn-developer"], {},
            ["tests.test_bp_service_native"])
        self.assertIn("FN_NATIVE_BP_HOST=$T/build/fn-host-dtn-developer", " ".join(lines))

    def test_a_big_memory_scope_waits_on_the_box_wide_lock(self):
        big = dry("--mem", "80G", "HEAD", "tests.test_native_owner")
        self.assertEqual(big.returncode, 0, big.stderr)
        line = [l for l in big.stdout.splitlines() if l.startswith("tstep test-")][0]
        self.assertIn("flock /tank/fn/scratch/.hbox-native-bigmem.lock env", line)
        small = dry("--mem", "24G", "HEAD", "tests.test_native_owner")
        self.assertNotIn("flock", [l for l in small.stdout.splitlines()
                                   if l.startswith("tstep test-")][0])

    def test_jobs_runs_modules_in_parallel_and_tallies_in_order(self):
        # G3: --jobs N runs the modules N at a time against one image set;
        # each writes its own exit code, the tally keeps the named order.
        answer = dry("--jobs", "3", "HEAD", "tests.test_native_owner", "tests.test_native_web")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        script = answer.stdout
        self.assertIn("seq 1 2 | xargs -P 3 -n 1 sh $S/module.sh", script)
        self.assertIn("echo $rc > $S/rc/$name", script)
        self.assertIn("for name in test-tests.test_native_owner test-tests.test_native_web ;", script)
        self.assertIn("--jobs auto", dry("HEAD", "tests.test_native_owner").stdout)
        serial = dry("HEAD", "tests.test_native_owner")
        self.assertIn("xargs -P 1 ", serial.stdout)
        self.assertIn("--jobs 5 ", dry("--certify-jobs", "5", "HEAD", "tests.test_native_owner").stdout)
        for bad in ("0", "x", ""):
            self.assertEqual(dry("--jobs", bad, "HEAD", "tests.test_native_owner").returncode, 2)

    def test_the_developer_images_identity_is_exported_when_built(self):
        answer = dry("HEAD", "tests.test_native_owner")
        self.assertIn("if [ -x build/fn-host-developer ]; then", answer.stdout)
        self.assertIn("identity --image build/fn-host-developer --prefix FN_NATIVE_DEVELOPER_ --export",
                      answer.stdout)
        import tempfile
        with tempfile.TemporaryDirectory() as temp:
            image = Path(temp) / "fn-host-developer"
            image.write_text("#!/bin/sh\n")
            Path(str(image) + ".core").write_bytes(b"core")
            out = subprocess.run(
                ["python3", str(ROOT / "tools" / "native_env.py"), "identity", "--image", str(image),
                 "--prefix", "FN_NATIVE_DEVELOPER_", "--export"],
                capture_output=True, text=True, timeout=30)
        self.assertEqual(out.returncode, 0, out.stderr)
        names = [line.split("=")[0] for line in out.stdout.splitlines()]
        self.assertEqual(names, ["export FN_NATIVE_DEVELOPER_LAUNCHER_SHA256",
                                 "export FN_NATIVE_DEVELOPER_CORE_SHA256"])

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
        # Both DTN images: test_bp_service_native takes the dtn-developer one
        # (tools/native_env.py PREFER: its fault-injection cases).
        self.assertIn("FN_NATIVE_BP_HOST=$T/build/fn-host-dtn-developer", answer.stdout)

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

    def test_without_images_the_list_is_what_the_modules_read(self):
        # This module reads FN_NATIVE_HOST (the production image): without
        # --images the run builds it rather than refusing (three lanes lost a
        # launch each to the refusal, 2026-09-29).
        answer = dry("HEAD", "tests.test_native_hybrid_author")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertIn("images derived from what the modules read: --images "
                      "developer,production; added production "
                      "(tests.test_native_hybrid_author reads FN_NATIVE_HOST)", answer.stderr)
        self.assertEqual(len(image_lines(answer.stdout)), 2)
        # A module that reads only the developer image changes nothing.
        plain = dry("HEAD", "tests.test_native_owner")
        self.assertNotIn("images derived", plain.stderr)

    def test_a_reader_of_an_unbuilt_image_is_refused_by_name(self):
        # PKT-437 (2): an explicit --images developer, and this module reads
        # FN_NATIVE_HOST (the production image).
        answer = dry("--images", "developer", "HEAD", "tests.test_native_hybrid_author")
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
        both = dry("--images", "developer,production", "--allow-skips", "HEAD",
                   "tests.test_native_bounds_join")
        self.assertEqual(both.returncode, 0, both.stderr)
        join = next(line for line in both.stdout.splitlines()
                    if line.startswith("tstep test-tests.test_native_bounds_join "))
        self.assertIn("FN_NATIVE_HOST=$T/build/fn-host ", join)
        self.assertIn("FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer ", join)
        # Since dev 96b3eb2e4 the module USES tests.native_profile_fixture's
        # IMAGE (FN_NATIVE_HOST), so the derived list adds production; the
        # dtn-developer image it reads only through an imported helper stays
        # a note, never a refusal.
        derived = dry("--allow-skips", "HEAD", "tests.test_native_bounds_join")
        self.assertEqual(derived.returncode, 0, derived.stderr)
        text = derived.stdout + derived.stderr
        self.assertIn("added production (tests.test_native_bounds_join reads FN_NATIVE_HOST "
                      "(through tests.native_profile_fixture.IMAGE, which it uses))", text)
        self.assertIn("FN_NATIVE_HOST=$T/build/fn-host ", next(
            line for line in derived.stdout.splitlines()
            if line.startswith("tstep test-tests.test_native_bounds_join ")))
        self.assertIn("reads FN_NATIVE_DTN_DEVELOPER_HOST through a tests/ helper", text)
        self.assertNotIn("FN_NATIVE_DTN_DEVELOPER_HOST=", next(
            line for line in derived.stdout.splitlines()
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
        shutil.copy(ROOT / "tools" / "boxes.sh", tree / "tools" / "boxes.sh")
        shutil.copy(ROOT / "tools" / "native_box.sh", tree / "tools" / "native_box.sh")
        shutil.copy(ROOT / "tools" / "image_set.py", tree / "tools" / "image_set.py")
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


class GatedModuleTests(unittest.TestCase):
    """obstructions-5 item 45: a module whose opt-in gate is unset is refused
    at launch, naming the variable, unless --allow-skips (operability-4 built
    25 minutes of images twice for a module that then skipped)."""

    def test_an_unset_gate_is_refused_by_name(self):
        done = dry(".", "tests.test_native_consumer_e2")
        self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
        self.assertIn("gated by FN_RUN_CONSUMER_E2E", done.stderr)
        self.assertIn("--allow-skips", done.stderr)

    def test_allow_skips_notes_it_and_goes_on(self):
        done = dry(".", "tests.test_native_consumer_e2", "--allow-skips")
        self.assertNotIn("gated by", done.stderr)
        self.assertIn("reads FN_RUN_CONSUMER_E2E (not set", done.stderr)

    def test_the_gate_given_by_env_runs(self):
        done = dry(".", "tests.test_native_consumer_e2", "--env", "FN_RUN_CONSUMER_E2E=1")
        self.assertNotIn("gated by FN_RUN_CONSUMER_E2E", done.stderr)
        # It reads a second gate; each unset one is named.
        self.assertIn("gated by FN_RUN_CONSUMER_POLL_E2E", done.stderr)
        done = dry(".", "tests.test_native_consumer_e2", "--env", "FN_RUN_CONSUMER_E2E=1",
                   "--env", "FN_RUN_CONSUMER_POLL_E2E=1")
        self.assertNotIn("gated by", done.stderr)

    def test_plan_unit(self):
        import sys
        sys.path.insert(0, str(ROOT / "tools"))
        import native_env
        _, refusals, _ = native_env.plan(["developer"], {}, ["tests.test_native_consumer_e2"])
        self.assertTrue(any("gated by FN_RUN_CONSUMER_E2E" in r for r in refusals), refusals)
        _, refusals, notes = native_env.plan(["developer"], {}, ["tests.test_native_consumer_e2"],
                                             allow_skips=True)
        self.assertFalse(any("gated by" in r for r in refusals), refusals)


class BoxRowTests(unittest.TestCase):
    """Each build box's row (obstructions-7 item 67): hbox_native used hbox's
    cache and swarm-build whatever box FN_HBOX named (compress-8)."""

    def row(self, box, home=None):
        out = subprocess.run(["sh", str(ROOT / "tools" / "native_box.sh"), box, str(ROOT)]
                             + ([home] if home else []),
                             capture_output=True, text=True, timeout=60)
        self.assertEqual(out.returncode, 0, out.stderr)
        return dict(line.split("=", 1) for line in out.stdout.splitlines())

    def test_hbox_row(self):
        row = self.row("hbox")
        self.assertEqual(row, {"BASE": "'/tank/fn/scratch'", "CACHE": "'/tank/fn/certcache'",
                               "WRAP": "'swarm-build'", "IMAGES_BASE": "'/tank/fn/images'",
                               "OPENSSL": "'bundled'"})
        script = dry("--box", "hbox", "HEAD", "tests.test_native_owner").stdout
        self.assertIn("S=/tank/fn/scratch/t/native-l", script)
        self.assertIn("CACHE=/tank/fn/certcache", script)
        self.assertIn("step certify swarm-build python3", script)
        self.assertIn("openssl-3.5.8/bin/openssl", script)
        self.assertIn("flock /tank/fn/scratch/.hbox-native-bigmem.lock",
                      dry("--box", "hbox", "--mem", "64G", "HEAD", "tests.test_native_owner").stdout)

    def test_persvati_row(self):
        row = self.row("persvati")
        self.assertEqual(row, {"BASE": "'~/fn-gates'", "CACHE": "'~/fn-certcache'",
                               "WRAP": "''", "IMAGES_BASE": "''", "OPENSSL": "'system'"})
        resolved = self.row("persvati", "/home/u")
        self.assertEqual((resolved["BASE"], resolved["CACHE"]),
                         ("'/home/u/fn-gates'", "'/home/u/fn-certcache'"))
        answer = dry("--box", "persvati", "HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        script = answer.stdout
        self.assertIn("S=~/fn-gates/t/native-l", script)
        self.assertIn("CACHE=~/fn-certcache", script)
        self.assertNotIn("swarm-build", script)
        self.assertNotIn("openssl-3.5.8", script)
        self.assertIn("command -v openssl", script)
        # No published image sets there: refused up front, naming hbox.
        refused = dry("--box", "persvati", "--image-set", "a" * 40, "HEAD",
                      "tests.test_native_owner")
        self.assertEqual(refused.returncode, 2)
        self.assertIn("published on hbox", refused.stderr)

    def test_auto_and_unknown(self):
        # A dry run never ssh-es to pick: auto reads as hbox.
        self.assertIn("S=/tank/fn/scratch/", dry("--box", "auto", "HEAD",
                                                 "tests.test_native_owner").stdout)
        self.assertEqual(dry("--box", "laptop", "HEAD", "tests.test_native_owner").returncode, 2)
        out = subprocess.run(["sh", str(ROOT / "tools" / "native_box.sh"), "laptop", str(ROOT)],
                             capture_output=True, text=True, timeout=60)
        self.assertEqual(out.returncode, 2)


class DetachedByDefaultTests(unittest.TestCase):
    """A run survives its lane (obstructions-7 item 58): the start returns
    detached, the record names box, dir, pid and log, and `status` / `attach`
    read it from any later session."""

    def test_start_detaches_and_records_the_pid(self):
        import os
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "calls"
            for tool in ("ssh", "rsync"):
                stub = Path(directory) / tool
                stub.write_text('#!/bin/sh\necho "%s $*" >> %s\ncase "$*" in *nohup*) echo 4242 ;; '
                                'esac\ncat > /dev/null\nexit 0\n'
                                % (tool, log))
                stub.chmod(0o755)
            env = {**os.environ, "PATH": f"{directory}:{os.environ['PATH']}", "FN_HBOX": "hbox"}
            label = "detach-test-%d" % os.getpid()
            record = ROOT / "build" / "hbox-native" / f"{label}.run"
            self.addCleanup(lambda: record.unlink(missing_ok=True))
            started = subprocess.run(["sh", str(SCRIPT), "--no-build", "--name", "t", "--label", label,
                                      "HEAD", "tests.test_native_owner"],
                                     cwd=ROOT, env=env, capture_output=True, text=True, timeout=120,
                                     stdin=subprocess.DEVNULL)
            self.assertEqual(started.returncode, 0, started.stdout + started.stderr)
            self.assertIn(f"re-attach with: tools/hbox_native.sh attach {label}", started.stdout)
            fields = dict(line.split("=", 1) for line in record.read_text().splitlines())
            self.assertEqual(fields["box"], "hbox")
            self.assertEqual(fields["pid"], "4242")
            self.assertEqual(fields["dir"], f"/tank/fn/scratch/t/native-{label}")
            self.assertEqual(fields["log"], fields["dir"] + "/run.log")
            # No wait_for poll happened: the start did not attach.
            self.assertNotIn("test -f", log.read_text())
            status = subprocess.run(["sh", str(SCRIPT), "status", label], cwd=ROOT, env=env,
                                    capture_output=True, text=True, timeout=60,
                                    stdin=subprocess.DEVNULL)
            self.assertEqual(status.returncode, 0, status.stderr)
            self.assertIn("pid=4242", status.stdout)
            self.assertIn("kill -0 '4242'", log.read_text())

    def test_attach_without_a_record_names_the_runs_here(self):
        answer = subprocess.run(["sh", str(SCRIPT), "attach", "no-such-label"], cwd=ROOT,
                                capture_output=True, text=True, timeout=60)
        self.assertEqual(answer.returncode, 2)
        self.assertIn("no record", answer.stderr)
        self.assertIn("no-such-label.run", answer.stderr)
        # --wait keeps the old attach-at-once behaviour; the dry run takes it.
        self.assertEqual(dry("--wait", "HEAD", "tests.test_native_owner").returncode, 0)


class HelperImageUseTests(unittest.TestCase):
    """obstructions-7 item 62: a helper's image read counts for a module
    through the helper names the module uses; a scope's reads are
    alternatives; unmet -> refused up front, not 25 minutes of build then
    every test skipped."""

    def fake_tree(self, directory):
        import sys
        sys.path.insert(0, str(ROOT / "tools"))
        import native_env
        base = Path(directory)
        files = {
            "tests.test_x": "from tests.helper import starts_dtn, harmless\n"
                            "import tests.other as other\n"
                            "def test_a():\n    starts_dtn()\n    other.both()\n",
            "tests.helper": "import os\nfrom tests.deep import deep_start\n"
                            "def starts_dtn():\n    return deep_start()\n"
                            "def harmless():\n    return 1\n"
                            "def unused():\n    return native_image(\"FN_NATIVE_HOST\")\n",
            "tests.deep": "def deep_start():\n    return native_image(\"FN_NATIVE_DTN_HOST\")\n",
            "tests.other": "def both():\n    image = native_image(\"FN_NATIVE_DEVELOPER_HOST\")\n"
                           "    return image or native_image(\"FN_NATIVE_DTN_DEVELOPER_HOST\")\n",
        }
        paths = {}
        for name, text in files.items():
            path = base / (name.replace(".", "_") + ".py")
            path.write_text(text)
            paths[name] = path

        def module_file(name):
            if name in paths:
                return paths[name]
            raise SystemExit("none")
        return native_env, module_file

    def test_scopes_follow_the_names_the_module_uses(self):
        import tempfile
        from unittest import mock
        with tempfile.TemporaryDirectory() as directory:
            native_env, module_file = self.fake_tree(directory)
            with mock.patch.object(native_env, "module_file", module_file):
                scopes = native_env.helper_scopes("tests.test_x")
        self.assertEqual(scopes, [
            ("tests.deep", "deep_start", frozenset({"FN_NATIVE_DTN_HOST"})),
            ("tests.other", "both", frozenset({"FN_NATIVE_DEVELOPER_HOST",
                                               "FN_NATIVE_DTN_DEVELOPER_HOST"}))])
        # `unused` reads FN_NATIVE_HOST, but test_x never refers to it.

    def test_plan_refuses_an_unmet_scope_and_accepts_an_alternative(self):
        import tempfile
        from unittest import mock
        with tempfile.TemporaryDirectory() as directory:
            native_env, module_file = self.fake_tree(directory)
            with mock.patch.object(native_env, "module_file", module_file):
                _, refusals, notes = native_env.plan(["developer"], {}, ["tests.test_x"])
                self.assertEqual(len(refusals), 1, refusals)
                self.assertIn("FN_NATIVE_DTN_HOST (through tests.deep.deep_start", refusals[0])
                self.assertIn("--images developer,dtn", refusals[0])
                # The developer image meets `both` (its dtn-developer read is
                # the fallback): noted, not refused.
                self.assertTrue(any("FN_NATIVE_DTN_DEVELOPER_HOST" in n for n in notes), notes)
                _, refusals, _ = native_env.plan(["developer", "dtn"], {}, ["tests.test_x"])
                self.assertEqual(refusals, [])


if __name__ == "__main__":
    unittest.main()

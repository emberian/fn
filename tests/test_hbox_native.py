"""tools/hbox_native.sh's box script, read through --dry-run (no ssh)."""
import os
import subprocess
import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tests.scratch_git import run as scratch_git

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "hbox_native.sh"



def cleanup_recorded_group(process, pid_file):
    """Reap this test's group; macOS EPERM can mean only zombies remain."""
    import signal
    if process.poll() is not None or not pid_file.exists():
        return
    pid = int(pid_file.read_text())
    assert pid == process.pid, (pid, process.pid)
    try:
        os.killpg(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    except PermissionError:
        if sys.platform != "darwin":
            raise
    process.wait(timeout=5)



def isolated_launcher(root):
    """Real launcher and Git revision, with generated state in its own tree."""
    import shutil
    tree = root / "worktree"
    (tree / "tools").mkdir(parents=True)
    for tool in (ROOT / "tools").iterdir():
        if tool.name == "hbox_native.sh":
            shutil.copy(tool, tree / "tools" / tool.name)
        else:
            (tree / "tools" / tool.name).symlink_to(tool)
    for name in ("tests", "books", "host", "specs", "fixtures", "planning"):
        (tree / name).symlink_to(ROOT / name)
    git = ["git", "-C", str(tree), "-c", "user.name=fixture", "-c", "user.email=fixture@invalid",
           "-c", "gc.auto=0", "-c", "maintenance.auto=false"]
    scratch_git([*git, "init", "-q"], check=True, capture_output=True)
    scratch_git([*git, "commit", "--allow-empty", "-q", "-m", "fixture"], check=True, capture_output=True)
    return tree / "tools/hbox_native.sh"


def install_identity_stub(root):
    (root / "fakeidentity.py").write_text('''import hashlib, os, re, sys
command = sys.argv[1]
launch_id = re.search(r"in '([0-9a-f]{32}) '", command).group(1)
run_dir = re.search(r"cat ([^ ]+)/run.identity", command).group(1)
if os.environ.get("FN_TEST_ID_MISMATCH"):
    launch_id = "b" * 32 if launch_id != "b" * 32 else "c" * 32
prefix = "fn-native-" + hashlib.sha256(os.fsencode(run_dir)).hexdigest() + "-4242-888"
print(launch_id + " 4242 888 " + prefix)
''')


def dry(*args, env=None):
    return subprocess.run(
        ["sh", str(SCRIPT), "--dry-run", "--name", "t", "--label", "l", *args],
        cwd=ROOT, capture_output=True, text=True, timeout=30,
        env=None if env is None else {**os.environ, **env})


def image_lines(out):
    """The image saves, serial (step) or parallel (pstep), as `step image-...`
    lines; the shared foreign-library step before parallel saves is not one."""
    return [line[1:] if line.startswith("pstep ") else line for line in out.splitlines()
            if line.startswith(("step image-", "pstep image-")) and not line.startswith("step image-libs")]


class RecordedGroupCleanupTests(unittest.TestCase):
    def test_macos_zombie_group_is_reaped_and_other_permission_errors_propagate(self):
        import tempfile
        from unittest.mock import Mock, patch
        with tempfile.TemporaryDirectory() as directory:
            recorded = Path(directory) / "test.pid"
            recorded.write_text("4242")
            for platform, error in (("darwin", PermissionError()), ("linux", ProcessLookupError())):
                process = Mock(pid=4242); process.poll.return_value = None
                with self.subTest(platform=platform), patch.object(sys, "platform", platform), \
                     patch.object(os, "killpg", side_effect=error):
                    cleanup_recorded_group(process, recorded)
                    process.wait.assert_called_once_with(timeout=5)
            process = Mock(pid=4242); process.poll.return_value = None
            with patch.object(sys, "platform", "linux"), patch.object(os, "killpg", side_effect=PermissionError()):
                with self.assertRaises(PermissionError): cleanup_recorded_group(process, recorded)
                process.wait.assert_not_called()


class HboxNativeDryRunTests(unittest.TestCase):
    def test_node_dead_result_is_failed_in_module_line_and_status(self):
        import json
        import re
        import tempfile
        answer = dry("HEAD", "tests.test_native_owner")
        tstep = re.search(r"^tstep\(\) \{.*?^\}\n", answer.stdout, re.M | re.S).group(0)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / "tools").mkdir(); (root / "logs").mkdir(); (root / "rc").mkdir()
            record = {"module": "fixture", "tests": 1, "failures": 0, "errors": 0, "executed": 0,
                      "skipped": 1, "skips": [], "timings": [], "node_dead": [["row", "node dead: never greeted"]]}
            tool = root / "tools/test_budget.py"
            tool.write_text("import os,sys\nif sys.argv[1] == '--verdict':\n"
                " os.execv(sys.executable, [sys.executable, REAL, *sys.argv[1:]])\n"
                "print(RESULT); sys.exit(4)\n".replace("REAL", repr(str(ROOT / "tools/test_budget.py")))
                .replace("RESULT", repr("FN_TEST_BUDGET_RESULT " + json.dumps(record))))
            run = root / "module.sh"
            run.write_text(tstep + '\ntstep test-fixture python3 tools/test_budget.py --one fixture\n')
            done = subprocess.run(["sh", str(run)], cwd=root, capture_output=True, text=True, timeout=10,
                env={**os.environ, "S": str(root), "L": str(root / "logs"), "FN_NATIVE_SCOPE_UNIT": "fixture", "FN_NATIVE_MEMORY": "24G"})
            self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
            self.assertIn("exit 1", done.stdout)
            self.assertIn("FAILED (node dead)", done.stdout)
            self.assertEqual((root / "rc/test-fixture").read_text(), "1\n")

    def test_dead_run_profiling_image_is_an_optional_default(self):
        answer = dry("--box", "hbox", "--images", "developer,prof", "HEAD",
                     "tests.test_native_dead_run", env={"FN_DEAD_RUN_PROF_HOST": ""})
        self.assertEqual(answer.returncode, 0, answer.stdout + answer.stderr)
        self.assertNotIn("is gated by FN_DEAD_RUN_PROF_HOST", answer.stderr)
        self.assertIn("step image-prof", answer.stdout)
        self.assertIn("--one tests.test_native_dead_run", answer.stdout)

    def test_module_scope_names_are_recorded_at_the_unit_start(self):
        import re
        import tempfile
        answer = dry("--box", "hbox", "--jobs", "3", "HEAD",
                     "tests.test_native_owner", "tests.test_native_web")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertIn("export FN_NATIVE_SCOPE_UNIT=$FN_NATIVE_SCOPE_PREFIX-1.scope", answer.stdout)
        self.assertIn("export FN_NATIVE_SCOPE_UNIT=$FN_NATIVE_SCOPE_PREFIX-2.scope", answer.stdout)
        self.assertIn("unit=$FN_NATIVE_SCOPE_UNIT", answer.stdout)
        wrapper = re.search(r"^cat > \$S/scope.sh <<'SCOPERUN'\n(.*?)^SCOPERUN$",
                            answer.stdout, re.M | re.S).group(1)
        self.assertLess(wrapper.index('>> "$S/scopes"'), wrapper.index("exec systemd-run"))
        self.assertIn('systemd-run --user --scope --unit="$FN_NATIVE_SCOPE_UNIT"', wrapper)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            script = root / "scope.sh"
            script.write_text(wrapper)
            fake = root / "systemd-run"
            fake.write_text('#!/bin/sh\npython3 -c "import os; os.fstat(8)" 2>/dev/null && exit 9\n'
                            'cat "$S/scopes"\nprintf "%s\\n" "$*"\n')
            fake.chmod(0o755)
            unit = "fn-native-test-888-1.scope"
            # Open fd 8 before entering the generated wrapper; its child must
            # not inherit the run's lifetime lock description.
            done = subprocess.run(["sh", "-c", 'exec 8> "$S/run.lock"; exec sh "$S/scope.sh" "$@"',
                                   "scope-test", "-p", "MemoryMax=40G", "--", "true"],
                env={**os.environ, "PATH": str(root) + os.pathsep + os.environ["PATH"],
                     "S": str(root), "FN_NATIVE_SCOPE_UNIT": unit},
                capture_output=True, text=True, timeout=30)
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertEqual((root / "scopes").read_text(), unit + "\n")
            self.assertIn("--unit=" + unit, done.stdout)
            self.assertIn("MemoryMax=40G", done.stdout)
        big = dry("--box", "hbox", "--mem", "40G", "HEAD", "tests.test_native_owner")
        line = next(line for line in big.stdout.splitlines() if line.startswith("tstep test-"))
        self.assertLess(line.index("flock "), line.index("sh $S/scope.sh"))

    def test_modules_choose_their_own_units_and_override_is_visible(self):
        modules = ["tests.test_native_pack_chain", "tests.test_native_bounds_join",
                   "tests.test_native_heap_from_profile", "tests.test_native_owner"]
        answer = dry("--box", "hbox", "--allow-skips", "--images", "developer,production",
                     "--jobs", "3", "HEAD", *modules)
        self.assertEqual(answer.returncode, 0, answer.stderr)
        steps = [line for line in answer.stdout.splitlines() if line.startswith("tstep test-")]
        for module, unit, big in zip(modules, ("48G", "40G", "2G", "24G"), (True, True, False, False)):
            line = next(line for line in steps if "test-" + module + " " in line)
            self.assertIn("MemoryMax=" + unit, line)
            self.assertEqual("flock /tank/fn/scratch/.hbox-native-bigmem.lock env" in line, big)
            self.assertIn("export FN_NATIVE_MEMORY=" + unit, answer.stdout)
        self.assertIn("MemoryMax=$FN_NATIVE_MEMORY", answer.stdout)
        self.assertIn("xargs -P 3", answer.stdout)
        overridden = dry("--box", "hbox", "--allow-skips", "--images", "developer,production",
                         "--mem", "40960M", "HEAD", *modules)
        self.assertEqual(overridden.returncode, 0, overridden.stderr)
        for module, unit in zip(modules, ("48G", "40G", "2G", "24G")):
            self.assertIn(f"{module} memory override {unit} -> 40960M", overridden.stderr)
        for line in overridden.stdout.splitlines():
            if line.startswith("tstep test-"):
                self.assertIn("MemoryMax=40960M", line)
                self.assertIn(".hbox-native-bigmem.lock", line)
        invalid = dry("--mem", "48G;touch x", "HEAD", "tests.test_native_owner")
        self.assertEqual(invalid.returncode, 2)

    def test_both_certify_steps_are_guarded_and_opt_in_is_in_the_script(self):
        answer = dry("--box", "hbox", "HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        text = answer.stdout
        self.assertIn("== certify plan: N books to certify of M in the roots' closure", text)
        self.assertIn("[ $rc -eq 0 ] || finish $rc", text)
        self.assertLess(text.index("certify_plan incremental"), text.index("step certify "))
        self.assertLess(text.index("certify_plan closure"), text.index("step certify-origin "))
        self.assertNotIn("--box hbox --allow-certify", text)
        allowed = dry("--box", "hbox", "--allow-certify", "HEAD", "tests.test_native_owner")
        self.assertIn("--box hbox --allow-certify", allowed.stdout)
        # The scope ruling excludes any new coordination lock or farm wait.
        self.assertNotIn("FN_FARM_RUN_LOCK_FD", text)

    def test_reader_index_runs_against_the_integrated_image(self):
        answer = dry("--box", "persvati", "--images", "developer,production", "HEAD",
                     "tests.test_native_reader_index")
        self.assertEqual(answer.returncode, 0, answer.stdout + answer.stderr)
        steps = [line for line in answer.stdout.splitlines()
                 if line.startswith("tstep ") and "tests.test_native_reader_index" in line]
        self.assertEqual(len(steps), 1, answer.stdout)
        self.assertIn("FN_RUN_NATIVE_READER_INDEX=1", steps[0])
        self.assertNotIn("not set: opt-in for the integrated reader-index gate",
                         answer.stdout + answer.stderr)

    def test_the_prof_image_alone_builds_and_finishes(self):
        answer = dry("--box", "hbox", "--build-only", "--images", "prof", "HEAD")
        self.assertEqual(answer.returncode, 0, answer.stdout[-2000:] + answer.stderr)
        lines = answer.stdout.splitlines()
        self.assertIn("step image-prof", " ".join(lines))
        self.assertIn("finish 0", lines)

    def test_a_build_only_dry_run_exits_zero(self):
        # with no modules `grep -c .` exited 1 under set -e after the build-only finish
        answer = dry("--box", "hbox", "--build-only", "--images", "developer", "HEAD")
        self.assertEqual(answer.returncode, 0, answer.stderr)

    def test_an_env_value_may_hold_commas_but_not_shell_syntax(self):
        answer = dry("--box", "hbox", "--env", "FN_TEST_LIST=a,b,c", "HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertIn("export FN_TEST_LIST=a,b,c", answer.stdout)
        for value in ("a;b", "a b", "a`b`", "a'b"):
            refused = dry("--box", "hbox", "--env", f"FN_TEST_LIST={value}", "HEAD", "tests.test_native_owner")
            self.assertEqual(refused.returncode, 2, value)
            self.assertIn("--env value may hold only", refused.stderr)

    def test_several_images_save_in_parallel_after_the_libraries_and_one_image_stays_serial(self):
        answer = dry("--box", "hbox", "--images", "developer,production,dtn", "HEAD", "tests.test_native_owner")
        lines = answer.stdout.splitlines()
        saves = [i for i, line in enumerate(lines) if line.startswith("pstep image-")]
        self.assertEqual(len(saves), 3, answer.stdout + answer.stderr)
        libs = lines.index(next(l for l in lines if l.startswith("step image-libs")))
        waits = [i for i, line in enumerate(lines) if line == "pwait"]
        self.assertTrue(libs < saves[0] and waits and waits[0] > saves[-1])
        single = dry("--box", "hbox", "--images", "developer", "HEAD", "tests.test_native_owner")
        self.assertFalse([l for l in single.stdout.splitlines() if l.startswith("pstep ") or l == "pwait"])
        serial = dry("--box", "hbox", "--images", "developer,production", "HEAD", "tests.test_native_owner",
                     env={"FN_NATIVE_SERIAL_IMAGES": "1"})
        self.assertFalse([l for l in serial.stdout.splitlines() if l.startswith("pstep image-")])

    def test_acquire_without_a_complete_origin_certifies_the_closure_once_and_retries(self):
        import re
        import tempfile
        answer = dry("--box", "hbox", "--allow-certify", "--images", "developer,production,dtn-developer", "HEAD",
                     "tests.test_native_log")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        out = answer.stdout
        self.assertIn("acquire_step acquire default", out)
        self.assertIn("acquire_step acquire-dtn dtn", out)
        self.assertLess(out.index("step certify "), out.index("acquire_step acquire default"))
        function = re.search(r"^ORIGIN_DONE=0\nacquire_step\(\) \{.*?^\}\n", out, re.S | re.M).group(0)
        guard = re.search(r"^certify_plan\(\) \{.*?^\}\n", out, re.S | re.M).group(0)
        # The decision, run against stubs: python3 acquire exits 3
        # (proof_artifacts.NO_SET: no complete installable set) until
        # certify-origin has run; every call is logged.  An ACL2 load that
        # rejected a set exits 1 and must not trigger the closure certify.
        harness = """
S=. T=. L=$PWD/logs CACHE=c ACL2=a toolchain=identity
mkdir -p $L; echo books/x > $L/roots.txt
finish() { echo "FINISH $1"; exit $1; }
step() { name=$1; shift; echo "STEP $name $*"; touch $L/certified; }
python3() {
    case "$*" in
      *native_certify_plan.py*)
          echo "== certify plan: 1 books to certify of 1 in the roots' closure"
          case "$*" in *--allow-certify*) return 0;; *) echo "refused closure certify"; return 16;; esac;;
      *acquire*) echo "ACQ $*" >> $L/calls
          if [ "$MODE" = rejected ]; then echo "profile=default result=no complete current artifact set passed an ACL2 load rejected=1"; return 1; fi
          if [ "$MODE" = fast ] || [ -f $L/certified ] && [ "$MODE" != stillred ]; then echo ok; return 0; fi
          echo "profile=default result=none of the 2 complete candidate artifact sets could be installed rejected=0"; return 3;;
      *loadfail*) return 1;;
    esac
}
""" + guard + function + """
acquire_step acquire default
acquire_step acquire-dtn dtn
echo REACHED
"""
        def run(mode, allow=True):
            with tempfile.TemporaryDirectory() as d:
                script = harness if allow else harness.replace(" --allow-certify ", " ")
                done = subprocess.run(["sh", "-c", script], cwd=d, capture_output=True, text=True,
                                      env={**os.environ, "MODE": mode}, timeout=30)
                calls = Path(d, "logs", "calls").read_text().count("ACQ")
                return done, calls
        done, calls = run("fast")
        self.assertIn("REACHED", done.stdout)
        self.assertNotIn("STEP certify-origin", done.stdout)
        self.assertEqual(calls, 2, done.stdout)
        done, calls = run("red-until-certified")
        self.assertIn("REACHED", done.stdout, done.stdout + done.stderr)
        self.assertEqual(done.stdout.count("STEP certify-origin"), 1, done.stdout)
        self.assertIn("--closure", done.stdout)
        self.assertEqual(calls, 3, done.stdout)  # fail, retry ok, dtn ok
        done, calls = run("stillred")
        self.assertIn("FINISH 3", done.stdout)
        self.assertNotIn("REACHED", done.stdout)
        self.assertEqual(done.stdout.count("STEP certify-origin"), 1)
        self.assertEqual(calls, 2)
        done, calls = run("rejected")
        self.assertIn("FINISH 1", done.stdout)
        self.assertNotIn("STEP certify-origin", done.stdout)
        self.assertEqual(calls, 1)
        done, calls = run("red-until-certified", allow=False)
        self.assertEqual(done.returncode, 16, done.stdout + done.stderr)
        self.assertIn("FINISH 16", done.stdout)
        self.assertNotIn("STEP certify-origin", done.stdout)
        self.assertEqual(calls, 1)

    def test_default_prefix_does_not_require_unrequested_dtn_certificates(self):
        answer = dry("--box", "hbox", "HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        checks = [line for line in answer.stdout.splitlines() if line.startswith("step host-ld")]
        self.assertEqual(len(checks), 1)
        self.assertIn("host_translate_check.py --build host/native/build.lisp", checks[0])

    def test_dtn_prefix_is_checked_after_its_artifacts_are_acquired(self):
        answer = dry("--box", "hbox", "--images", "developer,dtn-developer", "HEAD",
                     "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        checks = [line for line in answer.stdout.splitlines() if line.startswith("step host-ld")]
        self.assertEqual(len(checks), 2)
        self.assertIn("host_translate_check.py --build host/native/build-dtn.lisp", checks[1])
        self.assertLess(answer.stdout.index("step validate-dtn"),
                        answer.stdout.index("step host-ld-dtn"))

    def test_static_preflight_receipts_and_historical_fallback(self):
        import tempfile
        answer = dry("--box", "hbox", "HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        start = answer.stdout.index("static_gate() {")
        function = answer.stdout[start:answer.stdout.index("\n}\n", start) + 3]
        script = 'python3() { printf "%s\\n" "$@"; return 7; }\n' + function
        script += '\nstatic_gate interfaces-check tools/interface_emit.py --check\n'
        with tempfile.TemporaryDirectory() as directory:
            fallback = subprocess.run(["sh", "-c", script], cwd=directory,
                                      capture_output=True, text=True)
            self.assertEqual(fallback.returncode, 7)
            self.assertEqual(fallback.stdout.splitlines(), ["tools/interface_emit.py", "--check"])
            tool = Path(directory) / "tools/native_preflight.py"
            tool.parent.mkdir()
            tool.touch()
            cached = subprocess.run(["sh", "-c", script], cwd=directory,
                                    capture_output=True, text=True)
            self.assertEqual(cached.returncode, 7)
            self.assertEqual(cached.stdout.splitlines(), ["tools/native_preflight.py", "--cache",
                "/tank/fn/scratch/.native-preflight-cache", "--gate", "interfaces-check"])

    def test_one_world_gate_runs_before_certification(self):
        answer = dry("--box", "hbox", "HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        gate = 'step one-world static_gate one-world tools/one_world_check.py'
        self.assertEqual(answer.stdout.count(gate), 1)
        self.assertLess(answer.stdout.index(gate), answer.stdout.index('step certify '))

    def test_the_box_artifacts_are_made_in_the_shipped_tree_and_stamped_with_its_source(self):
        # build/box/ is never committed (tools/box_artifacts.py), so a shipped
        # tree makes it: the wire grammar after the certify step, the stamp
        # before any module; the registry is no file (interface_emit.registry)
        sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                             text=True, check=True).stdout.strip()
        built = dry("--box", "hbox", "HEAD", "tests.test_native_owner")
        self.assertEqual(built.returncode, 0, built.stderr)
        out = built.stdout
        wire = out.index("step box-wire swarm-build python3 tools/protocol_emit.py --wire --write")
        self.assertLess(out.index("step certify "), wire)
        self.assertLess(wire, out.index("acquire_step acquire default"))
        stamp = out.index("step box-stamp")
        self.assertIn(f"write_stamp(Path('.'), '{sha}', 'hbox', '{sha}')", out[stamp:])
        self.assertLess(stamp, out.index("tstep "))
        self.assertNotIn("--write-registry", out)
        linked = dry("--image-set", sha, "--images", "developer", "HEAD", "tests.test_native_owner")
        self.assertEqual(linked.returncode, 0, linked.stderr)
        out = linked.stdout
        self.assertNotIn("certify_books", out)
        self.assertNotIn("--write-registry", out)
        wire = out.index("step box-wire swarm-build python3 tools/protocol_emit.py --wire --write")
        self.assertLess(out.index("if [ -f books/wire-export.cert ]"), wire)
        self.assertIn("rm -f build/box/wire-grammar.json", out)
        self.assertLess(wire, out.index("step box-stamp"))
        self.assertLess(out.index("step box-stamp"), out.index("tstep "))

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

    def test_a_built_batch_is_stamped_after_its_saves_and_a_linked_set_is_not(self):
        """CONVERGE-20261007-1 red #3: a run that builds and tests without
        publishing stamps build/ (tools/image_set.py stamp) after every save
        and before any module, so a composed fixture binds its launchers."""
        answer = dry("--box", "hbox", "--images", "developer,production", "HEAD",
                     "tests.test_native_consumer_exchange_two_nodes")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        lines = answer.stdout.splitlines()
        stamp = [i for i, line in enumerate(lines)
                 if line == "step stamp-images python3 tools/image_set.py stamp $T"]
        self.assertEqual(len(stamp), 1, answer.stdout)
        saves = [i for i, line in enumerate(lines) if line.startswith(("step image-", "pstep image-"))]
        waits = [i for i, line in enumerate(lines) if line == "pwait"]
        tests = [i for i, line in enumerate(lines) if line.startswith("tstep test-")]
        self.assertTrue(saves and tests and max(saves + waits) < stamp[0] < min(tests))
        sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                             text=True, check=True).stdout.strip()
        linked = dry("--image-set", sha, "--images", "developer", "HEAD", "tests.test_native_owner")
        self.assertNotIn("stamp-images", linked.stdout)

    def test_overlay_plans_here_and_derives_cores_after_the_link(self):
        sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                             text=True, check=True).stdout.strip()
        answer = dry("--image-set", sha, "--overlay", "--images", "developer", "HEAD",
                     "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        lines = answer.stdout.splitlines()
        link = next(i for i, line in enumerate(lines) if line.startswith("step image-set"))
        overlay = next(i for i, line in enumerate(lines) if line.startswith("step overlay"))
        self.assertLess(link, overlay)
        self.assertIn("$S/bin/native_overlay.py build $S/overlay --image-set "
                      f"/tank/fn/images/{sha} --tree $T --images developer", lines[overlay])
        self.assertIn("native_overlay: plan", answer.stdout + answer.stderr)
        refused = dry("--overlay", "HEAD", "tests.test_native_owner")
        self.assertEqual(refused.returncode, 2)
        self.assertIn("give --image-set SHA", refused.stderr)

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
        import os
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            launcher = isolated_launcher(Path(directory))
            log = Path(directory) / "calls"
            for tool in ("ssh", "rsync"):
                stub = Path(directory) / tool
                install_identity_stub(Path(directory))
                stub.write_text('#!/bin/sh\necho "%s $*" >> %s\ncase "$*" in *"remaining=5"*) python3 "$(dirname "$0")/fakeidentity.py" "$*";; esac\ncat > /dev/null\nexit 0\n'
                                % (tool, log))
                stub.chmod(0o755)
            env = {**os.environ, "PATH": f"{directory}:{os.environ['PATH']}"}
            env["FN_HBOX"] = "hbox"
            for rev, keeps in ((".", "--exclude=*.cert"), ("HEAD", "! -name '*.cert'")):
                log.write_text("")
                done = subprocess.run(["sh", str(launcher), "--detach", "--no-build", "--name", "t",
                                       "--label", "l", rev, "tests.test_native_owner"],
                                      cwd=ROOT, env=env, capture_output=True, text=True,
                                      timeout=120)
                self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
                self.assertIn(keeps, log.read_text())
                log.write_text("")
                subprocess.run(["sh", str(launcher), "--detach", "--name", "t", "--label", "l",
                                rev, "tests.test_native_owner"], cwd=ROOT, env=env,
                               capture_output=True, text=True, timeout=120)
                self.assertNotIn(".cert", log.read_text())

    def test_no_build_refuses_a_tree_without_its_images_up_front(self):
        # item 74: the refusal comes before any rsync/ship, and names the
        # runs of NAME on the box that hold the images.
        import os
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            launcher = isolated_launcher(Path(directory))
            log = Path(directory) / "calls"
            answers = Path(directory) / "runs"
            stub = Path(directory) / "ssh"
            stub.write_text('#!/bin/sh\necho "ssh $*" >> %s\ncase "$*" in\n'
                            '*fn-no-build-images*) echo build/fn-host-developer ;;\n'
                            '*fn-no-build-runs*) cat %s ;;\nesac\ncat > /dev/null\nexit 0\n'
                            % (log, answers))
            stub.chmod(0o755)
            rsync = Path(directory) / "rsync"
            rsync.write_text('#!/bin/sh\necho "rsync $*" >> %s\nexit 0\n' % log)
            rsync.chmod(0o755)
            env = {**os.environ, "PATH": f"{directory}:{os.environ['PATH']}", "FN_HBOX": "hbox"}
            for held, words in (("abc\nxyz\n", "holding every image this run needs: abc xyz "
                                                 "-- pass --label ONE"),
                                ("", "no run of t on hbox holds them")):
                answers.write_text(held)
                log.write_text("")
                done = subprocess.run(["sh", str(launcher), "--no-build", "--name", "t", "--label",
                                       "fresh", ".", "tests.test_native_owner"], cwd=ROOT,
                                      env=env, capture_output=True, text=True, timeout=120,
                                      stdin=subprocess.DEVNULL)
                self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
                self.assertIn("--no-build reuses hbox:/tank/fn/scratch/t/native-fresh/tree "
                              "(--label fresh), which lacks: build/fn-host-developer", done.stderr)
                self.assertIn(words, done.stderr)
                self.assertNotIn("rsync", log.read_text())
                self.assertNotIn("mkdir -p", log.read_text())

    def test_default_builds_the_developer_image_only(self):
        answer = dry("HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        lines = image_lines(answer.stdout)
        self.assertEqual(len(lines), 1)
        self.assertIn("FN_NATIVE_PROFILE=developer FN_NATIVE_WORLD=full FN_NATIVE_BUILD=host/native/build.lisp "
                      "FN_NATIVE_IMAGE=build/fn-host-developer", lines[0])
        self.assertNotIn("--profile dtn", answer.stdout)
        self.assertNotIn("FN_NATIVE_BP_HOST", answer.stdout)

    def test_the_box_names_its_fixture_stores_for_the_modules_that_read_them(self):
        import sys
        sys.path.insert(0, str(ROOT))
        from tools import native_env
        lines, _refused, _notes = native_env.plan(["developer"], {}, ["tests.test_native_over_window"])
        self.assertIn("FN_OPEN_DEPTH_FIXTURES=$FN_FIXTURES_DIR", " ".join(lines))
        # an explicit --env still wins
        lines, _refused, _notes = native_env.plan(
            ["developer"], {"FN_OPEN_DEPTH_FIXTURES": "/x"}, ["tests.test_native_over_window"])
        self.assertNotIn("$FN_FIXTURES_DIR", " ".join(lines))
        for box, fixtures in (("hbox", "/tank/fn/scratch/fixtures"),
                              ("persvati", "/home/u/fn-gates/fixtures")):
            row = subprocess.run(["sh", str(ROOT / "tools/native_box.sh"), box, str(ROOT), "/home/u"],
                                 capture_output=True, text=True)
            self.assertIn(f"FIXTURES='{fixtures}'", row.stdout, row.stderr)
        answer = dry("HEAD", "tests.test_native_over_window")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertIn("export FN_FIXTURES_DIR=/tank/fn/scratch/fixtures", answer.stdout)

    def test_bp_service_native_takes_the_dtn_developer_image(self):
        import sys
        sys.path.insert(0, str(ROOT))
        from tools import native_env
        lines, _refused, _notes = native_env.plan(
            ["developer", "production", "dtn", "dtn-developer"], {},
            ["tests.test_bp_service_native"])
        self.assertIn("FN_NATIVE_BP_HOST=$T/build/fn-host-dtn-developer", " ".join(lines))

    def test_a_stored_verdict_is_consulted_before_a_module_runs_unless_all(self):
        answer = dry("HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        script = answer.stdout
        self.assertIn("export FN_VERDICT_STORE=${FN_VERDICT_STORE:-", script)
        self.assertIn(".verdicts} FN_NATIVE_ALL=0", script)
        self.assertIn("tcached test-tests.test_native_owner tests.test_native_owner", script)
        self.assertIn("native_verdicts.py lookup $module", script)
        self.assertIn("--one tests.test_native_owner $CASES", script)
        self.assertIn("FN_NATIVE_MODULE_LOG=$L/$name.log", script)
        self.assertIn("FN_NATIVE_ALL=1", dry("--all", "HEAD", "tests.test_native_owner").stdout)

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
        certify = next(i for i, line in enumerate(lines)
                       if line.strip().startswith("step certify "))
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
        self.assertIn('echo "== load at end: $(uptime)"', finish.split("\n}")[0])
        tstep = script[script.index("tstep() {"):]
        self.assertIn("/proc/loadavg", tstep.split("\n}")[0])

    def test_finish_writes_gate_walls_beside_run_log(self):
        answer = dry("HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        finish = answer.stdout[answer.stdout.index("finish() {"):].split("\n}")[0]
        self.assertIn("python3 $T/tools/gate_walls.py $S > $S/gate_walls.json 2>/dev/null", finish)
        # Cancellation is published first; normal completion still follows collection.
        self.assertLess(finish.index("echo 143 > $S/status"), finish.index("gate_walls.py"))
        self.assertLess(finish.index("gate_walls.py"), finish.index("echo $finish_status > $S/status"))
        self.assertLess(finish.index("gate_walls.py"), finish.index("== done status"))

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
        after = dry("HEAD", "tests.test_bp_service_native", "--images", "dtn-developer")
        before = dry("--images", "dtn-developer", "HEAD", "tests.test_bp_service_native")
        self.assertEqual(after.returncode, 0, after.stderr)
        self.assertEqual(after.stdout, before.stdout)

    def test_without_images_the_list_is_what_the_modules_read(self):
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
        both = dry("--images", "developer,production", "--allow-skips", "HEAD",
                   "tests.test_native_bounds_join")
        self.assertEqual(both.returncode, 0, both.stderr)
        join = next(line for line in both.stdout.splitlines()
                    if line.startswith("tstep test-tests.test_native_bounds_join "))
        self.assertIn("FN_NATIVE_HOST=$T/build/fn-host ", join)
        self.assertIn("FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer ", join)
        # Used helper images affect derivation; incidental imports stay notes.
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
        import tempfile
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        tree = Path(temp.name).resolve() / "hbox-native-copy-test"
        (tree / "tools").mkdir(parents=True)
        (tree / "tools" / "hbox_native.sh").write_text(
            head + '\necho "COPY=$FN_HBOX_NATIVE_COPY"\necho "RUNNING=$0"\necho "HERE=$HERE"\n')
        shutil.copy(ROOT / "tools" / "wait_for.sh", tree / "tools" / "wait_for.sh")
        shutil.copy(ROOT / "tools" / "boxes.sh", tree / "tools" / "boxes.sh")
        shutil.copy(ROOT / "tools" / "native_box.sh", tree / "tools" / "native_box.sh")
        shutil.copy(ROOT / "tools" / "image_set.py", tree / "tools" / "image_set.py")
        shutil.copy(ROOT / "tools" / "native_overlay.py", tree / "tools" / "native_overlay.py")
        shutil.copy(ROOT / "tools" / "native_reuse.py", tree / "tools" / "native_reuse.py")
        shutil.copy(ROOT / "tools" / "native_certify_plan.py", tree / "tools" / "native_certify_plan.py")
        env = {k: v for k, v in os.environ.items() if not k.startswith("FN_HBOX_NATIVE_")}
        probe = subprocess.run(["sh", str(tree / "tools" / "hbox_native.sh")], cwd=ROOT,
                               capture_output=True, text=True, timeout=30, env=env)
        fields = dict(line.split("=", 1) for line in probe.stdout.splitlines() if "=" in line)
        self.assertEqual(probe.returncode, 0, probe.stderr)
        self.assertTrue(fields["RUNNING"].startswith(fields["COPY"] + "/"), fields)
        self.assertNotIn(str(tree), fields["COPY"])
        self.assertEqual(fields["HERE"], str(tree.resolve()))
        self.assertFalse(Path(fields["COPY"]).exists())


class FromTrainDryRunTests(unittest.TestCase):
    """--from-train, read through --dry-run in a scratch git repo that holds a
    copy of tools/ and tests/ (the plan reads that repo's build/train records,
    never this tree's)."""

    @classmethod
    def setUpClass(cls):
        import shutil
        import tempfile
        cls.holder = tempfile.TemporaryDirectory()
        cls.repo = Path(cls.holder.name) / "scratch"
        cls.repo.mkdir()
        ignore = shutil.ignore_patterns("__pycache__", "*.pyc", "build")
        for name in ("tools", "tests"):
            shutil.copytree(ROOT / name, cls.repo / name, ignore=ignore)
        git = ["git", "-C", str(cls.repo), "-c", "commit.gpgsign=false",
               "-c", "user.name=t", "-c", "user.email=t@t",
               # the commit holds every file of tools/ and tests/ as loose
               # objects, past gc.auto: a detached auto-gc then packs them
               # into .git/objects while tearDownClass removes the repo
               "-c", "gc.auto=0", "-c", "maintenance.auto=false"]
        scratch_git([*git, "init", "-q", "-b", "lane/x"], check=True)
        scratch_git([*git, "add", "."], check=True, capture_output=True)
        scratch_git([*git, "commit", "-q", "-m", "c"], check=True, capture_output=True)
        cls.rev = scratch_git([*git, "rev-parse", "HEAD"], check=True, capture_output=True,
                                 text=True).stdout.strip()

    @classmethod
    def tearDownClass(cls):
        cls.holder.cleanup()

    def records(self, **changes):
        import json
        record = {"sha": self.rev, "ran_at": self.rev, "box": "hbox", "run": "run-1",
                  "certify_id": "cid-1", "known_reds_seen": []}
        record.update(changes)
        train, farm = self.repo / "build" / "train", self.repo / "build" / "farm"
        train.mkdir(parents=True, exist_ok=True)
        farm.mkdir(parents=True, exist_ok=True)
        (train / "lane__x.json").write_text(json.dumps({"box_run": "run-1"}))
        (train / "lane__x.box-step.json").write_text(json.dumps(record))
        (farm / "run-1.json").write_text(json.dumps({
            "host": "hbox", "box_manifest": "passed", "certify_id": "cid-1",
            "remote_path": "/tank/fn/batch/tree"}))

    def run_dry(self, *args):
        env = {k: v for k, v in os.environ.items() if not k.startswith("FN_HBOX_NATIVE_")}
        return subprocess.run(
            ["sh", str(self.repo / "tools" / "hbox_native.sh"), "--dry-run", "--name", "t",
             "--label", "l", "--box", "hbox", "--images", "developer,production,dtn", *args,
             "HEAD", "tests.test_native_owner"],
            cwd=self.repo, capture_output=True, text=True, timeout=60, env=env)

    def test_without_from_train_the_box_script_installs_certifies_and_acquires(self):
        import shutil
        shutil.rmtree(self.repo / "build", ignore_errors=True)
        answer = self.run_dry()
        self.assertEqual(answer.returncode, 0, answer.stderr)
        out = answer.stdout
        for line in ("T=$S/tree",
                     "ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k"
                     "  # the certify launcher (tools/farm.py HOSTS)",
                     "if [ $ACQUIRED_DEFAULT -eq 0 ]; then acquire_step acquire default; fi",
                     "acquire_step acquire-dtn dtn"):
            self.assertIn(line, out.splitlines())
        for fragment in ("step install ", "step certify ", "step box-wire "):
            self.assertIn(fragment, out)
        # One resolution plan, listed before the install that consumes it.
        self.assertIn("export FN_RESOLUTION_PLAN=$T/build/.resolution-plan.json", out)
        self.assertLess(out.index("step resolve "), out.index("step install "))
        self.assertNotIn("== reuse:", out)
        self.assertNotIn("from-train", answer.stderr)

    def test_a_refused_plan_says_why_and_falls_back(self):
        import shutil
        shutil.rmtree(self.repo / "build", ignore_errors=True)
        answer = self.run_dry("--from-train")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertIn("--from-train refused:", answer.stderr)
        self.assertIn("falling back", answer.stderr)
        self.assertIn("step install ", answer.stdout)
        self.assertIn("T=$S/tree", answer.stdout.splitlines())
        self.assertNotIn("== reuse:", answer.stdout)

    def test_a_record_for_another_commit_falls_back_naming_the_difference(self):
        self.records(sha="0" * 40)
        answer = self.run_dry("--from-train")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertIn("box step ran at 000000000000", answer.stderr)
        self.assertIn("falling back", answer.stderr)
        self.assertIn("step install ", answer.stdout)

    def test_an_accepted_plan_runs_in_the_trains_tree_without_install_certify_or_acquire(self):
        self.records()
        answer = self.run_dry("--from-train")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertNotIn("falling back", answer.stderr)
        out = answer.stdout
        self.assertIn("T=/tank/fn/batch/tree", out.splitlines())
        self.assertIn("== reuse: the train's certified tree", out)
        for fragment in ("step install ", "step certify ", "step box-wire ", "acquire_step acquire"):
            self.assertNotIn(fragment, out)
        # what follows the certify stays: the image's own launcher still loads the roots
        self.assertIn("step validate ", out)
        self.assertIn("step validate-dtn ", out)
        self.assertLess(out.index("== reuse:"), out.index("step validate "))

    def test_the_claim_is_taken_before_the_link_and_the_pid_recorded_after_the_start(self):
        text = SCRIPT.read_text()
        self.assertLess(text.index("native_reuse.py claim --root $REUSE_TREE --owner $S\""),
                        text.index("ln -sfn $REUSE_TREE $S/tree"))
        self.assertLess(text.index("echo \"hbox_native: started;"),
                        text.index("--owner $S --pid $PID"))

    def test_from_train_refuses_no_build_and_a_working_tree(self):
        for extra, rev in (("--no-build", "HEAD"), ("", ".")):
            with self.subTest(extra=extra, rev=rev):
                env = {k: v for k, v in os.environ.items() if not k.startswith("FN_HBOX_NATIVE_")}
                argv = ["sh", str(self.repo / "tools" / "hbox_native.sh"), "--dry-run", "--name", "t",
                        "--label", "l", "--box", "hbox", "--from-train", *([extra] if extra else []),
                        rev, "tests.test_native_owner"]
                answer = subprocess.run(argv, cwd=self.repo, capture_output=True, text=True,
                                        timeout=60, env=env)
                self.assertEqual(answer.returncode, 2, answer.stdout + answer.stderr)
                self.assertIn("--from-train starts an image build", answer.stderr)


class HarnessBudgetTests(unittest.TestCase):
    def test_one_place_names_the_harness_stores_budget(self):
        import sys
        sys.path.insert(0, str(ROOT))
        from tools import native_env
        self.assertEqual(native_env.HARNESS_INIT_WORDS,
                         ("--budget", native_env.HARNESS_INIT_BUDGET_MB))
        # Row Q10b: the budget is init's grammar word; no harness or test
        # sets an FN_INIT_ variable any more.
        env_named = subprocess.run(["git", "grep", "-n", "-E", "FN_INIT_(BUDGET_MB|SIZING)",
                                    "--", "tools", "tests", "host", "books"],
                                   cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(env_named.stdout, "")
        # Harnesses share the declared budget.
        typed = subprocess.run(["git", "grep", "-n", "-E", "--budget.{0,40}9830[4]",
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
                               "OPENSSL": "'bundled'", "FIXTURES": "'/tank/fn/scratch/fixtures'"})
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
                               "WRAP": "'/tank/fn/bin/persvati-jobs'", "IMAGES_BASE": "''", "OPENSSL": "'bundled'",
                               "FIXTURES": "'~/fn-gates/fixtures'"})
        resolved = self.row("persvati", "/home/u")
        self.assertEqual((resolved["BASE"], resolved["CACHE"]),
                         ("'/home/u/fn-gates'", "'/home/u/fn-certcache'"))
        answer = dry("--box", "persvati", "HEAD", "tests.test_native_owner")
        self.assertEqual(answer.returncode, 0, answer.stderr)
        script = answer.stdout
        self.assertIn("S=~/fn-gates/t/native-l", script)
        self.assertIn("CACHE=~/fn-certcache", script)
        self.assertNotIn("swarm-build", script)
        self.assertIn("openssl-3.5.8/bin/openssl", script)
        self.assertIn("export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8", script)
        self.assertNotIn("command -v openssl", script)
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
            launcher = isolated_launcher(Path(directory))
            log = Path(directory) / "calls"
            for tool in ("ssh", "rsync"):
                stub = Path(directory) / tool
                install_identity_stub(Path(directory))
                stub.write_text('#!/bin/sh\necho "%s $*" >> %s\ncase "$*" in *"remaining=5"*) python3 "$(dirname "$0")/fakeidentity.py" "$*" ;; '
                                'esac\ncat > /dev/null\nexit 0\n'
                                % (tool, log))
                stub.chmod(0o755)
            env = {**os.environ, "PATH": f"{directory}:{os.environ['PATH']}", "FN_HBOX": "hbox"}
            label = "detach-test-%d" % os.getpid()
            record = launcher.parent.parent / "build" / "hbox-native" / f"{label}.run"
            started = subprocess.run(["sh", str(launcher), "--no-build", "--name", "t", "--label", label,
                                      "HEAD", "tests.test_native_owner"],
                                     cwd=ROOT, env=env, capture_output=True, text=True, timeout=120,
                                     stdin=subprocess.DEVNULL)
            self.assertEqual(started.returncode, 0, started.stdout + started.stderr)
            self.assertIn(f"re-attach with: tools/hbox_native.sh attach {label}", started.stdout)
            fields = dict(line.split("=", 1) for line in record.read_text().splitlines())
            self.assertEqual(fields["box"], "hbox")
            self.assertEqual(fields["pid"], "4242")
            self.assertEqual(fields["pgid"], "4242")
            self.assertEqual(fields["starttime"], "888")
            commands = log.read_text()
            self.assertIn("nohup setsid env FN_NATIVE_LAUNCH_ID=", commands)
            self.assertIn("FN_NATIVE_LAUNCH_ID=" + fields["launch_id"], commands)
            self.assertIn(f"cat {fields['dir']}/run.identity", commands)
            self.assertEqual(fields["dir"], f"/tank/fn/scratch/t/native-{label}")
            self.assertEqual(fields["log"], fields["dir"] + "/run.log")
            # No wait_for poll happened: the start did not attach.
            self.assertNotIn("test -f", log.read_text())
            status = subprocess.run(["sh", str(launcher), "status", label], cwd=ROOT, env=env,
                                    capture_output=True, text=True, timeout=60,
                                    stdin=subprocess.DEVNULL)
            self.assertEqual(status.returncode, 0, status.stderr)
            self.assertIn("pid=4242", status.stdout)
            self.assertIn("/bin/kill -0 -- -4242", log.read_text())

    def test_a_reused_run_records_the_source_its_images_were_built_from(self):
        import os
        import tempfile
        source = "d" * 40
        for log_line, want in ((f"== source commit {source}", source), ("== load 1 2 3", None)):
            with tempfile.TemporaryDirectory() as directory:
                launcher = isolated_launcher(Path(directory))
                for tool in ("ssh", "rsync"):
                    stub = Path(directory) / tool
                    install_identity_stub(Path(directory))
                    stub.write_text('#!/bin/sh\ncase "$*" in *"remaining=5"*) python3 "$(dirname "$0")/fakeidentity.py" "$*" ;; '
                                    '*run.log*) printf "%%s\\n" "== load 1" %r ;; esac\n'
                                    'cat > /dev/null\nexit 0\n' % log_line)
                    stub.chmod(0o755)
                env = {**os.environ, "PATH": f"{directory}:{os.environ['PATH']}", "FN_HBOX": "hbox"}
                label = "reuse-test-%d-%d" % (os.getpid(), want is None)
                record = launcher.parent.parent / "build" / "hbox-native" / f"{label}.run"
                started = subprocess.run(["sh", str(launcher), "--reuse-image", "t/native-earlier",
                                          "--images", "developer", "--name", "t", "--label", label,
                                          "HEAD", "tests.test_native_owner"],
                                         cwd=ROOT, env=env, capture_output=True, text=True, timeout=120,
                                         stdin=subprocess.DEVNULL)
                if want is None:
                    self.assertEqual(started.returncode, 2, started.stdout + started.stderr)
                    self.assertIn("names no `== source` line", started.stderr)
                    self.assertFalse(record.exists())
                    continue
                self.assertEqual(started.returncode, 0, started.stdout + started.stderr)
                fields = dict(line.split("=", 1) for line in record.read_text().splitlines())
                self.assertEqual(fields["source"], want)

    def test_attach_without_a_record_names_the_runs_here(self):
        import tempfile
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        launcher = isolated_launcher(Path(temp.name))
        answer = subprocess.run(["sh", str(launcher), "attach", "no-such-label"], cwd=ROOT,
                                capture_output=True, text=True, timeout=60)
        self.assertEqual(answer.returncode, 2)
        self.assertIn("no record", answer.stderr)
        self.assertIn("no-such-label.run", answer.stderr)
        # --wait attaches at once; dry-run also accepts it.
        self.assertEqual(dry("--wait", "HEAD", "tests.test_native_owner").returncode, 0)


class NativeCertifyPlanTests(unittest.TestCase):
    def test_fake_planner_counts_only_misses_and_closure_refuses_even_with_full_cache(self):
        import tempfile
        helper = ROOT / "tools/native_certify_plan.py"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tools").mkdir()
            (root / "tools/certify_books.py").write_text('''
import os
from types import SimpleNamespace
def with_dependencies(roots):
    assert roots == ["books/root"]
    return ["books/base", "books/miss", "books/root"]
def install_from_cache(roots, toolchain, acl2):
    assert roots == ["books/root"] and toolchain == "identity"
    assert str(acl2) == "/fake/acl2"
    installed = ["books/base", "books/root"]
    if os.environ.get("FULL_CACHE") == "1": installed.append("books/miss")
    return SimpleNamespace(installed_from=dict.fromkeys(installed, "cache"))
''')
            def run(mode, allow=False, full=False):
                return subprocess.run([sys.executable, str(helper), "--tree", str(root),
                    "--mode", mode, "--box", "hbox", "--toolchain-identity", "identity",
                    "--acl2", "/fake/acl2", *( ["--allow-certify"] if allow else []), "books/root"],
                    capture_output=True, text=True, timeout=30,
                    env={**os.environ, "FULL_CACHE": str(int(full))})
            refused = run("incremental")
            self.assertEqual(refused.returncode, 16, refused.stderr)
            self.assertIn("1 books to certify of 3", refused.stdout)
            self.assertIn("first: books/miss", refused.stdout)
            self.assertIn("python3 tools/farm.py submit hbox --affected-by ...", refused.stdout)
            self.assertIn("--allow-certify", refused.stdout)
            self.assertEqual(run("incremental", allow=True).returncode, 0)
            cached = run("incremental", full=True)
            self.assertEqual(cached.returncode, 0, cached.stderr)
            self.assertIn("0 books to certify of 3", cached.stdout)
            closure = run("closure", full=True)
            self.assertEqual(closure.returncode, 16)
            self.assertIn("3 books to certify of 3", closure.stdout)
            self.assertIn("first: books/base, books/miss, books/root", closure.stdout)
            self.assertEqual(run("closure", allow=True, full=True).returncode, 0)

    def test_plan_failure_refuses_instead_of_certifying(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tools").mkdir()
            (root / "tools/certify_books.py").write_text(
                'def with_dependencies(roots): raise ValueError("cannot read closure")\n')
            result = subprocess.run([sys.executable, str(ROOT / "tools/native_certify_plan.py"),
                "--tree", str(root), "--mode", "closure", "--box", "hbox",
                "--toolchain-identity", "identity", "--acl2", "/fake/acl2", "books/root"],
                capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 2)
            self.assertIn("cannot read closure", result.stderr)


def install_flock(root):
    """Real kernel flock for local shell probes, including util-linux's -n FD."""
    flock = root / "flock"
    flock.write_text("#!" + sys.executable + "\n" + '''import fcntl, os, sys
args = sys.argv[1:]
nonblock = args[0] == "-n"
if args[0].startswith("-"):
    args.pop(0)
target = args.pop(0)
fd = int(target) if target.isdecimal() else os.open(target, os.O_CREAT | os.O_RDWR, 0o600)
try:
    fcntl.flock(fd, fcntl.LOCK_EX | (fcntl.LOCK_NB if nonblock else 0))
except BlockingIOError:
    raise SystemExit(1)
if args:
    os.execvp(args[0], args)
''')
    flock.chmod(0o755)


class NativeGenerationLockTests(unittest.TestCase):
    def test_full_launcher_overlap_refusal_leaves_live_generation_untouched(self):
        import fcntl
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            launcher = isolated_launcher(root)
            run_dir = root / "run"
            run_dir.mkdir()
            install_flock(root)
            label = "overlap-" + str(os.getpid())
            remote = "/tank/fn/scratch/t/native-" + label
            ssh = root / "ssh"
            ssh.write_text("#!" + sys.executable + "\n" + '''import os, subprocess, sys
args = sys.argv[1:]
if args[0] == "-n": args.pop(0)
command = args[1]
if os.environ["REMOTE_RUN"] not in command:
    raise SystemExit(0)
command = command.replace(os.environ["REMOTE_RUN"], os.environ["LOCAL_RUN"])
raise SystemExit(subprocess.call(["/bin/sh", "-c", command]))
''')
            ssh.chmod(0o755)
            setsid = root / "setsid"
            setsid.write_text("#!" + sys.executable + "\nimport os, sys\nos.setsid()\nos.execvp(sys.argv[1], sys.argv[1:])\n")
            setsid.chmod(0o755)
            protected = ("run.pid", "run.starttime", "scope-prefix", "scopes", "status", "run.sh")
            for name in protected:
                (run_dir / name).write_text(str(os.getpid()) if name == "run.pid" else "old-generation")
            before = {name: (run_dir / name).read_bytes() for name in protected}
            env = {**os.environ, "PATH": str(root) + os.pathsep + os.environ["PATH"],
                   "REMOTE_RUN": remote, "LOCAL_RUN": str(run_dir)}
            with (run_dir / "run.lock").open("a") as held:
                fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
                done = subprocess.run(["sh", str(launcher), "--box", "hbox", "--name", "t",
                    "--label", label, "--no-build", "HEAD", "tests.test_native_owner"],
                    cwd=ROOT, env=env, capture_output=True, text=True, stdin=subprocess.DEVNULL, timeout=20)
                self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
                self.assertIn("live leader " + str(os.getpid()), done.stderr)
                self.assertEqual(before, {name: (run_dir / name).read_bytes() for name in protected})

    def launch_fixture(self, root):
        install_identity_stub(root)
        ssh = root / "ssh"
        ssh.write_text("#!" + sys.executable + "\n" + '''import os, subprocess, sys, time
from pathlib import Path
args = sys.argv[1:]
command = args[-1]
root = Path(__file__).parent
with (root / "calls").open("a") as out: out.write(command + "\\n")
if "cat > " in command and "/run.sh" in command and os.environ.get("BLOCK_SHIPPING"):
    (root / "shipping").touch()
    until = time.monotonic() + 10
    while not (root / "release").exists():
        if time.monotonic() >= until: raise SystemExit(3)
        time.sleep(.01)
if "remaining=5" in command:
    if os.environ.get("WAIT_READBACK"):
        (root / "readback-ready").touch()
        until = time.monotonic() + 30
        while not (root / "readback-release").exists():
            if time.monotonic() >= until: raise SystemExit(3)
            time.sleep(.01)
    if (root / "identity").exists():
        print((root / "identity").read_text()); raise SystemExit(0)
    raise SystemExit(subprocess.call([sys.executable, str(root / "fakeidentity.py"), command]))
sys.stdin.buffer.read()
''')
        ssh.chmod(0o755)
        return {**os.environ, "PATH": str(root) + os.pathsep + os.environ["PATH"]}

    def test_concurrent_same_label_launch_refuses_locally_and_preserves_pending_record(self):
        import signal
        import tempfile
        import time
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            launcher = isolated_launcher(root)
            env = self.launch_fixture(root)
            label = "local-overlap-" + str(os.getpid())
            record = launcher.parent.parent / "build/hbox-native" / (label + ".run")
            args = ["--box", "hbox", "--name", "t", "--label", label, "--no-build", "HEAD", "tests.test_native_owner"]
            pid_file = root / "launcher.pid"
            with (root / "launcher.log").open("w") as log:
                first = subprocess.Popen(["sh", "-c", 'echo $$ > "$1"; shift; exec sh "$@"',
                    "launch-test", str(pid_file), str(launcher), *args],
                    cwd=ROOT, env={**env, "BLOCK_SHIPPING": "1"}, stdout=log, stderr=log, start_new_session=True)
                try:
                    until = time.monotonic() + 10
                    while not (root / "shipping").exists() and first.poll() is None and time.monotonic() < until:
                        time.sleep(.01)
                    self.assertTrue((root / "shipping").exists(), (root / "launcher.log").read_text())
                    pending = record.read_bytes()
                    self.assertIn(b"launch_id=", pending)
                    self.assertNotIn(b"pgid=", pending)
                    second = subprocess.run(["sh", str(launcher), *args], cwd=ROOT, env=env,
                        capture_output=True, text=True, timeout=15)
                    self.assertNotEqual(second.returncode, 0)
                    self.assertIn("same-label launch already in progress", second.stderr)
                    self.assertEqual(record.read_bytes(), pending)
                    (root / "release").touch()
                    self.assertEqual(first.wait(timeout=10), 0, (root / "launcher.log").read_text())
                    self.assertIn("pgid=4242", record.read_text())
                finally:
                    cleanup_recorded_group(first, pid_file)

    def test_successor_readback_never_publishes_and_pending_record_is_recoverable(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            launcher = isolated_launcher(root)
            env = self.launch_fixture(root)
            label = "mismatch-" + str(os.getpid())
            record = launcher.parent.parent / "build/hbox-native" / (label + ".run")
            done = subprocess.run(["sh", str(launcher), "--box", "hbox", "--name", "t", "--label", label,
                "--no-build", "HEAD", "tests.test_native_owner"], cwd=ROOT,
                env={**env, "FN_TEST_ID_MISMATCH": "1"}, capture_output=True, text=True, timeout=30)
            self.assertEqual(done.returncode, 3, done.stdout + done.stderr)
            self.assertIn("identity mismatch", done.stderr)
            self.assertIn("status " + label + " --dir", done.stderr)
            pending = record.read_text()
            self.assertIn("launch_id=", pending)
            self.assertNotIn("pgid=", pending)
            directory = subprocess.run(["sh", str(launcher), "status", label, "--dir"], cwd=ROOT,
                env=env, capture_output=True, text=True, timeout=10)
            self.assertEqual(directory.returncode, 0, directory.stderr)
            self.assertIn("hbox:/tank/fn/scratch/t/native-" + label, directory.stdout)
            adopted = subprocess.run(["sh", str(launcher), "adopt", label], cwd=ROOT, env=env,
                capture_output=True, text=True, timeout=15)
            self.assertEqual(adopted.returncode, 0, adopted.stdout + adopted.stderr)
            self.assertIn("adopted", adopted.stdout)
            self.assertIn("pgid=4242", record.read_text())
            self.assertEqual(next(l for l in pending.splitlines() if l.startswith("launch_id=")),
                             next(l for l in record.read_text().splitlines() if l.startswith("launch_id=")))

    def wait_barrier(self, path, process, seconds=10):
        import time
        until = time.monotonic() + seconds
        while not path.exists() and process.poll() is None and time.monotonic() < until:
            time.sleep(.01)
        self.assertTrue(path.exists(), path)

    def test_delayed_start_after_launcher_death_keeps_pending_id_adoptable(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); launcher = isolated_launcher(root)
            env = self.launch_fixture(root)
            label = "pending"
            record = launcher.parent.parent / "build/hbox-native/pending.run"
            args = ["--box", "hbox", "--name", "t", "--label", label, "--no-build", "HEAD", "tests.test_native_owner"]
            with (root / "launcher.log").open("w") as log:
                first = subprocess.Popen(["sh", "-c", 'echo $$ > "$1"; shift; exec sh "$@"',
                    "fixture", str(root / "launcher.pid"), str(launcher), *args], cwd=ROOT,
                    env={**env, "WAIT_READBACK": "1"}, stdout=log, stderr=log, start_new_session=True)
                delayed = None
                try:
                    self.wait_barrier(root / "readback-ready", first)
                    pending = record.read_bytes()
                    # The continuation belongs to launch A but has not started
                    # its generation; it survives A's local launcher death.
                    continuation = root / "delayed.py"
                    continuation.write_text("""import hashlib, os, time
from pathlib import Path
root = Path(__file__).parent
(root / 'delayed.pid').write_text(str(os.getpid()))
fields = dict(line.split('=', 1) for line in RECORD.read_text().splitlines())
(root / 'delayed-ready').touch()
until = time.monotonic() + 10
while not (root / 'start-release').exists():
    if time.monotonic() >= until: raise SystemExit(3)
    time.sleep(.01)
pid = os.getpid()
prefix = 'fn-native-' + hashlib.sha256(os.fsencode(fields['dir'])).hexdigest() + f'-{pid}-888'
(root / 'identity').write_text(f"{fields['launch_id']} {pid} 888 {prefix}\\n")
""".replace("RECORD", "Path(" + repr(str(record)) + ")"))
                    delayed = subprocess.Popen([sys.executable, str(continuation)], start_new_session=True,
                                               stdout=log, stderr=log)
                    self.wait_barrier(root / "delayed-ready", delayed)
                    cleanup_recorded_group(first, root / "launcher.pid")
                    calls = (root / "calls").read_bytes()
                    retry = subprocess.run(["sh", str(launcher), *args], cwd=ROOT, env=env,
                                           capture_output=True, text=True, timeout=15)
                    self.assertEqual(retry.returncode, 2, retry.stdout + retry.stderr)
                    self.assertIn("use adopt pending", retry.stderr)
                    self.assertEqual(record.read_bytes(), pending)
                    self.assertEqual((root / "calls").read_bytes(), calls)
                    (root / "start-release").touch()
                    self.assertEqual(delayed.wait(timeout=5), 0, (root / "launcher.log").read_text())
                    adopted = subprocess.run(["sh", str(launcher), "adopt", label], cwd=ROOT, env=env,
                                             capture_output=True, text=True, timeout=15)
                    self.assertEqual(adopted.returncode, 0, adopted.stdout + adopted.stderr)
                    self.assertIn("pgid=" + (root / "delayed.pid").read_text(), record.read_text())
                    self.assertEqual(next(l for l in pending.decode().splitlines() if l.startswith("launch_id=")),
                                     next(l for l in record.read_text().splitlines() if l.startswith("launch_id=")))
                finally:
                    cleanup_recorded_group(first, root / "launcher.pid")
                    if delayed is not None: cleanup_recorded_group(delayed, root / "delayed.pid")

    def test_stop_lock_keeps_scope_handles_until_cleanup_after_leader_exit(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); launcher = isolated_launcher(root)
            self.launch_fixture(root)
            run = root / "run"; run.mkdir()
            api = {"__name__": "fixture"}
            exec(SCRIPT.read_text().split("    cat <<'PROCESS'\n", 1)[1].split("\nPROCESS\n", 1)[0], api)
            prefix = api["scope_prefix"](run, 4242, 888)
            units = [prefix + "-1.scope", prefix + "-2.scope"]
            (run / "scopes").write_text("\n".join(units) + "\n")
            (run / "scope-prefix").write_text(prefix)
            (run / "run.starttime").write_text("888")
            (run / "status").write_text("143")
            proc = root / "proc/4242"; proc.mkdir(parents=True)
            (proc / "cmdline").write_bytes(b"sh\0" + os.fsencode(run / "run.sh") + b"\0")
            record = launcher.parent.parent / "build/hbox-native/cleanup.run"
            record.parent.mkdir(parents=True)
            record.write_text(f"box=stub\ndir={run}\npid=4242\npgid=4242\nstarttime=888\n")
            before = record.read_bytes()
            systemctl = root / "systemctl"
            systemctl.write_text('#!/bin/sh\ncase "$2" in show) printf "LoadState=loaded\nActiveState=active\n" ;; stop) printf "%s\n" "$4" >> "$FIXTURE_ROOT/stopped-units" ;; esac\n')
            systemctl.chmod(0o755)
            ssh = root / "ssh"
            ssh.write_text("#!" + sys.executable + "\n" + """import os, sys, time
from pathlib import Path
from types import SimpleNamespace
root = Path(os.environ['FIXTURE_ROOT'])
api = {'__name__': 'fixture'}
exec(sys.stdin.read(), api)
original = api['stop_scopes']
def cleanup(*args):
    (root / 'cleanup-ready').touch()
    until = time.monotonic() + 10
    while not (root / 'cleanup-release').exists():
        if time.monotonic() >= until: raise RuntimeError('cleanup barrier expired')
        time.sleep(.01)
    return original(*args)
api.update(os=SimpleNamespace(fsencode=os.fsencode, pidfd_open=lambda p: 701, close=lambda fd: None),
           signal=SimpleNamespace(SIGTERM=15, SIGKILL=9, pidfd_send_signal=lambda *a: None),
           process_stat=lambda *a: (4242, 888), leader_exited=lambda *a: True, stop_scopes=cleanup)
raise SystemExit(api['stop_run'](4242, 888, root / 'run', root / 'proc'))
""")
            ssh.chmod(0o755)
            env = {**os.environ, "PATH": str(root) + os.pathsep + os.environ["PATH"], "FIXTURE_ROOT": str(root)}
            with (root / "stop.log").open("w") as log:
                stopper = subprocess.Popen(["sh", "-c", 'echo $$ > "$1"; shift; exec sh "$@"',
                    "fixture", str(root / "stopper.pid"), str(launcher), "stop", "cleanup"], cwd=ROOT,
                    env=env, stdout=log, stderr=log, start_new_session=True)
                try:
                    self.wait_barrier(root / "cleanup-ready", stopper)
                    successor = subprocess.run(["sh", str(launcher), "--box", "hbox", "--name", "t", "--label", "cleanup",
                        "--no-build", "HEAD", "tests.test_native_owner"], cwd=ROOT, env=env,
                        capture_output=True, text=True, timeout=15)
                    self.assertEqual(successor.returncode, 1, successor.stdout + successor.stderr)
                    self.assertIn("same-label launch already in progress", successor.stderr)
                    self.assertEqual(record.read_bytes(), before)
                    self.assertEqual((run / "scopes").read_text().splitlines(), units)
                    (root / "cleanup-release").touch()
                    self.assertEqual(stopper.wait(timeout=5), 0, (root / "stop.log").read_text())
                    self.assertEqual((root / "stopped-units").read_text().splitlines(), units)
                finally:
                    cleanup_recorded_group(stopper, root / "stopper.pid")

    def test_publication_and_waiter_release_label_lock(self):
        import fcntl
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); launcher = isolated_launcher(root)
            env = self.launch_fixture(root)
            waiter = launcher.parent / "wait_for.sh"
            waiter.unlink()  # This fixture's symlink, never the shared helper.
            waiter.write_text('#!/bin/sh\necho $$ > "$FIXTURE_ROOT/waiter.pid"\n'
                'python3 -c "import os; os.fstat(7)" 2>/dev/null && touch "$FIXTURE_ROOT/bad-fd"\n'
                'touch "$FIXTURE_ROOT/wait-ready"\n'
                "timeout 10 sh -c 'while [ ! -f \"$FIXTURE_ROOT/wait-release\" ]; do sleep .01; done'\n")
            with (root / "wait.log").open("w") as log:
                process = subprocess.Popen(["sh", "-c", 'echo $$ > "$1"; shift; exec sh "$@"', "fixture",
                    str(root / "launcher.pid"), str(launcher), "--wait", "--box", "hbox", "--name", "t", "--label", "wait",
                    "--no-build", "HEAD", "tests.test_native_owner"], cwd=ROOT,
                    env={**env, "FIXTURE_ROOT": str(root)}, stdout=log, stderr=log, start_new_session=True)
                try:
                    self.wait_barrier(root / "wait-ready", process)
                    self.assertFalse((root / "bad-fd").exists())
                    record = launcher.parent.parent / "build/hbox-native/wait.run"
                    self.assertIn("pgid=4242", record.read_text())
                    with record.with_suffix(".lock").open("a") as held:
                        fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    (root / "wait-release").touch()
                    process.wait(timeout=5)
                finally:
                    cleanup_recorded_group(process, root / "launcher.pid")

    def test_publication_cannot_replace_a_successor_local_record(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            api = {"__name__": "identity_test"}
            code = SCRIPT.read_text().split("    cat <<'PROCESS'\n", 1)[1].split("\nPROCESS\n", 1)[0]
            exec(code, api)
            record = root / "record"
            record.write_text("box=hbox\ndir=" + str(root) + "\nlaunch_id=" + "b" * 32 + "\n")
            before = record.read_bytes()
            with self.assertRaisesRegex(ValueError, "identity mismatch"):
                api["publish_identity"](record, "a" * 32,
                    "a" * 32 + " 4242 888 " + api["scope_prefix"](root, 4242, 888))
            self.assertEqual(record.read_bytes(), before)



class NativeStopStatusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import re
        import shutil
        answer = dry("--box", "hbox", "HEAD", "tests.test_native_owner")
        if answer.returncode:
            raise AssertionError(answer.stdout + answer.stderr)
        # All trap, flag, step and finish code comes from the generated script.
        cls.prefix = answer.stdout.split("cat > $S/process.py <<'PROCESS'", 1)[0]
        cls.step = re.search(r"^step\(\) \{.*?^\}\n", answer.stdout, re.S | re.M).group(0)
        cls.finish = re.search(r"^finish\(\) \{.*?^\}\ntrap [^\n]+\n",
                               answer.stdout, re.S | re.M).group(0)
        cls.shells = ["/bin/sh"]
        if dash := shutil.which("dash"):
            cls.shells.append(dash)

    def prepare(self, root, full):
        import re
        import shlex
        import shutil
        tree = root / "tree"
        (tree / "tools").mkdir(parents=True)
        (tree / "build").mkdir()
        (tree / "build/fn-host-stop-fixture").write_bytes(b"stop checksum witness\n")
        shutil.copy(ROOT / "tools/gate_walls.py", tree / "tools/gate_walls.py")
        (root / "logs").mkdir()
        # macOS adapter: inspect only PIDs recorded by this test's processes.
        (root / "process.py").write_text('''import os, sys
from pathlib import Path
root = Path(__file__).parent
assert sys.argv[1] == "group-members"
leader = int(sys.argv[2])
assert leader == int((root / "test.pid").read_text())
members = []
for recorded in root.glob("*.pid"):
    pid = int(recorded.read_text())
    if pid in (leader, os.getpid()):
        continue
    try:
        if os.getpgid(pid) == leader:
            members.append(pid)
    except ProcessLookupError:
        pass
print(" ".join(map(str, sorted(set(members)))))
''')
        prefix = re.sub(r"^S=.*$", "S=" + shlex.quote(str(root)), self.prefix, count=1, flags=re.M)
        install_flock(root)
        prefix = "PATH=" + shlex.quote(str(root)) + ":$PATH; export PATH\n" + prefix
        # This PID file is written by the process the test launches, before work.
        return (prefix + '\nexport S\necho $$ > "$S/test.pid"\n'
                + (self.step + self.finish if full else ""))

    def escalation_fixture(self, root, process, run):
        import signal
        import time
        from types import SimpleNamespace
        pid = int((root / "test.pid").read_text())
        self.assertEqual(pid, process.pid)
        api = {"__name__": "test_process"}
        exec(SCRIPT.read_text().split("    cat <<'PROCESS'\n", 1)[1].split("\nPROCESS\n", 1)[0], api)
        (root / "run.starttime").write_text("888\n")
        (root / "scope-prefix").write_text(api["scope_prefix"](root, pid, 888) + "\n")
        (root / "scopes").write_text("")
        proc = root / "proc" / str(pid); proc.mkdir(parents=True)
        fields = ["S", "0", str(pid)] + ["0"] * 16 + ["888"]
        (proc / "stat").write_text(f"{pid} (sh) " + " ".join(fields))
        (proc / "cmdline").write_bytes(b"sh\0" + os.fsencode(run) + b"\0")
        signals = []
        def deliver(fd, sig, info, flags):
            self.assertEqual((fd, flags), (701, 4))
            self.assertIsNone(process.poll())
            self.assertEqual(int((root / "test.pid").read_text()), process.pid)
            signals.append(sig)
            os.killpg(process.pid, sig)
        def exited(fd, seconds=0):
            deadline = time.monotonic() + seconds
            while process.poll() is None:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    return False
                time.sleep(min(remaining, .01))
            return True
        api.update(os=SimpleNamespace(fsencode=os.fsencode, pidfd_open=lambda p: 701, close=lambda fd: None),
                   signal=SimpleNamespace(SIGTERM=signal.SIGTERM, SIGKILL=signal.SIGKILL,
                                          pidfd_send_signal=deliver), leader_exited=exited)
        return api, pid, signals

    def assert_group_stop(self, shell, root, script):
        import signal
        import time
        script_path = root / "test-run.sh"
        script_path.write_text(script)
        pid_file = root / "test.pid"
        with (root / "run.log").open("w") as log:
            child = subprocess.Popen([shell, str(script_path)], start_new_session=True,
                                     stdout=log, stderr=subprocess.STDOUT)
            try:
                deadline = time.monotonic() + 10
                while not (root / "ready").exists() and child.poll() is None and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue((root / "ready").exists(), (root / "run.log").read_text())
                pid = int(pid_file.read_text())
                self.assertEqual(pid, child.pid)
                self.assertEqual(os.getpgid(pid), pid)
                # Only the group of this test's process, from its own PID file.
                os.killpg(pid, signal.SIGTERM)
                self.assertEqual(child.wait(timeout=10), 143, (root / "run.log").read_text())
            finally:
                cleanup_recorded_group(child, pid_file)
        self.assertEqual((root / "status").read_text(), "143\n")
        self.assertFalse((root / "later").exists())

    def test_group_term_during_foreground_step_finishes_143_before_step_rc(self):
        import hashlib
        import json
        import tempfile
        body = '''
step long timeout --foreground 20 /bin/sh -c 'echo $$ > "$S/child.pid"; touch "$S/ready"; exec sleep 60'
step later touch "$S/later"
finish 0
'''
        for shell in self.shells:
            with self.subTest(shell=shell), tempfile.TemporaryDirectory(prefix="fn-stop-step-") as directory:
                root = Path(directory)
                script = self.prepare(root, full=True) + body
                self.assert_group_stop(shell, root, script)
                hashes = (root / "SHA256SUMS").read_text()
                self.assertIn(hashlib.sha256(b"stop checksum witness\n").hexdigest(), hashes)
                self.assertIn("logs/long.log", hashes)
                self.assertIsInstance(json.loads((root / "gate_walls.json").read_text()), dict)
                log = (root / "run.log").read_text()
                self.assertIn("== done status 143", log)
                self.assertNotIn("   long exit", log)  # trap finished before step's rc report

    def test_group_term_before_identity_or_finish_leaves_early_143(self):
        import tempfile
        body = '''
timeout --foreground 20 /bin/sh -c 'echo $$ > "$S/child.pid"; touch "$S/ready"; exec sleep 60'
touch "$S/later"
'''
        for shell in self.shells:
            with self.subTest(shell=shell), tempfile.TemporaryDirectory(prefix="fn-stop-early-") as directory:
                root = Path(directory)
                script = self.prepare(root, full=False) + body
                lines = script.splitlines()
                s_line = next(i for i, line in enumerate(lines) if line.startswith("S="))
                self.assertTrue(lines[s_line + 1].endswith(" TERM"))
                self.assert_group_stop(shell, root, script)
                self.assertFalse((root / "SHA256SUMS").exists())

    def test_term_during_finish_marks_cancellation_without_recursive_finish(self):
        import hashlib
        import json
        import tempfile
        body = 'finish 0\ntouch "$S/later"\n'
        for shell in self.shells:
            with self.subTest(shell=shell), tempfile.TemporaryDirectory(prefix="fn-stop-finish-") as directory:
                root = Path(directory)
                prepared = self.prepare(root, full=True)
                # timeout execs an executable; intercept only its gate_walls
                # command, delegating the group-members adapter to real Python.
                fake = root / "python3"
                fake.write_text('''#!/bin/sh
case "$1" in *gate_walls.py)
echo $$ > "$S/metadata.pid"; touch "$S/ready"; sleep .3; echo '{"collected": true}'; exit 0 ;;
*) exec REAL_PYTHON "$@" ;;
esac
'''.replace("REAL_PYTHON", str(sys.executable)))
                fake.chmod(0o755)
                self.assert_group_stop(shell, root, prepared + body)
                self.assertIn(hashlib.sha256(b"stop checksum witness\n").hexdigest(),
                              (root / "SHA256SUMS").read_text())
                self.assertEqual(json.loads((root / "gate_walls.json").read_text()), {"collected": True})
                self.assertEqual((root / "run.log").read_text().count("== load at end:"), 1)

    def test_step_143_distinguishes_stop_flag_from_unsignalled_failure(self):
        import tempfile
        for shell in self.shells:
            for stopped, rc in ((True, 7), (False, 143)):
                with self.subTest(shell=shell, stopped=stopped), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    script = root / "test-run.sh"
                    body = f"STOPPED={int(stopped)}\nstep failure /bin/sh -c 'exit {rc}'\n"
                    script.write_text(self.prepare(root, full=True) + body
                                      + 'step later touch "$S/later"\nfinish 0\n')
                    with (root / "run.log").open("w") as log:
                        result = subprocess.run([shell, str(script)], stdout=log, stderr=subprocess.STDOUT, timeout=30)
                    self.assertEqual(result.returncode, 143)
                    self.assertEqual((root / "status").read_text(), "143\n")
                    self.assertEqual((root / "stopped").exists(), stopped)
                    if stopped:
                        self.assertIn("failure exit 143", (root / "run.log").read_text())
                    self.assertFalse((root / "later").exists())

    def test_status_and_attach_display_stopped_without_a_deadline_wait(self):
        import tempfile
        with tempfile.TemporaryDirectory(prefix="fn-stop-display-") as directory:
            root = Path(directory)
            launcher = isolated_launcher(root)
            ssh = root / "ssh"
            # Existing transport commands run locally; no real SSH is reached.
            ssh.write_text('#!/bin/sh\n[ "$1" != -n ] || shift\nshift\nexec /bin/sh -c "$1"\n')
            ssh.chmod(0o755)
            (root / "status").write_text("143\n")
            (root / "stopped").write_text("TERM fixture-time\n")
            (root / "run.log").write_text("== done status 143\n")
            (root / "SHA256SUMS").write_text("fixture hashes\n")
            label = f"stop-display-{os.getpid()}"
            record = launcher.parent.parent / "build/hbox-native" / (label + ".run")
            record.parent.mkdir(parents=True, exist_ok=True)
            record.write_text(f"box=stub\ndir={root}\npid=4242\npgid=4242\nstarttime=888\n")
            env = {**os.environ, "PATH": str(root) + os.pathsep + os.environ["PATH"]}
            for stopped in (True, False):
                if not stopped:
                    (root / "stopped").unlink()
                for mode, code in (("status", 0), ("attach", 143)):
                    done = subprocess.run(["sh", str(launcher), mode, label], cwd=ROOT, env=env,
                                          capture_output=True, text=True, timeout=10, stdin=subprocess.DEVNULL)
                    self.assertEqual(done.returncode, code, done.stdout + done.stderr)
                    self.assertIn("stopped (143)" if stopped else "status 143", done.stdout)
                    if not stopped:
                        self.assertNotIn("stopped (143)", done.stdout)
                    self.assertNotIn("none yet", done.stdout)

    def test_term_ignoring_child_writes_status_promptly_then_owned_group_escalation(self):
        import signal
        import tempfile
        import time
        for shell in self.shells:
            with self.subTest(shell=shell), tempfile.TemporaryDirectory(prefix="fn-ignore-term-") as directory:
                root = Path(directory)
                run = root / "run.sh"
                run.write_text(self.prepare(root, full=True) + '''
step ignoring sh -c 'trap "" TERM; echo $$ > "$S/child.pid"; touch "$S/ready"; exec sleep 30'
touch "$S/later"
finish 0
''')
                with (root / "run.log").open("w") as log:
                    process = subprocess.Popen([shell, str(run)], start_new_session=True, stdout=log, stderr=log)
                    try:
                        deadline = time.monotonic() + 10
                        while not (root / "ready").exists() and process.poll() is None and time.monotonic() < deadline:
                            time.sleep(0.01)
                        self.assertTrue((root / "ready").exists(), (root / "run.log").read_text())
                        pid = int((root / "test.pid").read_text())
                        self.assertEqual(pid, process.pid)
                        child_pid = int((root / "child.pid").read_text())
                        api, pid, signals = self.escalation_fixture(root, process, run)
                        began = time.monotonic()
                        self.assertEqual(api["stop_run"](pid, 888, root, root / "proc", grace=2), 0)
                        self.assertLess(time.monotonic() - began, 5)
                        self.assertEqual(signals, [signal.SIGTERM, signal.SIGKILL])
                        self.assertEqual((root / "status").read_text(), "143\n")
                        self.assertTrue((root / "SHA256SUMS").is_file())
                        self.assertTrue((root / "stopped").read_text().startswith("TERM "))
                        self.assertFalse((root / "later").exists())
                        self.assert_pid_gone(child_pid)
                    finally:
                        cleanup_recorded_group(process, root / "test.pid")
                        if (root / "child.pid").exists():
                            try:
                                os.kill(int((root / "child.pid").read_text()), signal.SIGKILL)
                            except ProcessLookupError:
                                pass

    def test_anchor_stays_with_group_member_and_escalation_removes_recorded_processes(self):
        import signal
        import tempfile
        import time
        for shell in self.shells:
            with self.subTest(shell=shell), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                run = root / "run.sh"
                prepared = self.prepare(root, True)
                (root / "ignoring.sh").write_text('''#!/bin/sh
trap "" TERM
echo $$ > "$S/child.pid"
touch "$S/ready"
exec sleep 30
''')
                # TERM kills the direct step child; its ignoring grandchild
                # remains in the group and must still retain the anchor.
                run.write_text(prepared + '''
step forker sh -c 'echo $$ > "$S/parent.pid"; sh "$S/ignoring.sh" & wait'
touch "$S/later"
''')
                with (root / "run.log").open("w") as log:
                    leader = subprocess.Popen([shell, str(run)], start_new_session=True, stdout=log, stderr=log)
                    try:
                        deadline = time.monotonic() + 5
                        while not (root / "ready").exists() and time.monotonic() < deadline:
                            time.sleep(.01)
                        self.assertTrue((root / "ready").exists())
                        pid = int((root / "test.pid").read_text())
                        self.assertEqual(pid, leader.pid)
                        os.killpg(pid, signal.SIGTERM)
                        deadline = time.monotonic() + 5
                        while "waiting for group members" not in (root / "run.log").read_text() and time.monotonic() < deadline:
                            time.sleep(.01)
                        self.assertIn("waiting for group members", (root / "run.log").read_text())
                        self.assertEqual((root / "status").read_text(), "143\n")
                        child = int((root / "child.pid").read_text())
                        os.kill(child, 0)
                        self.assertIsNone(leader.poll())
                        # A repeated TERM must not bypass the group wait.
                        os.killpg(pid, signal.SIGTERM)
                        time.sleep(1.1)
                        with self.assertRaises(ProcessLookupError):
                            os.kill(int((root / "parent.pid").read_text()), 0)
                        self.assertIsNone(leader.poll())
                        os.kill(child, 0)
                        api, pid, signals = self.escalation_fixture(root, leader, run)
                        self.assertEqual(api["stop_run"](pid, 888, root, root / "proc", grace=1), 0)
                        self.assertEqual(signals, [signal.SIGTERM, signal.SIGKILL])
                        self.assertIsNotNone(leader.poll())
                        with self.assertRaises(ProcessLookupError): os.kill(pid, 0)
                        self.assert_pid_gone(child)
                        self.assertFalse((root / "later").exists())
                    finally:
                        cleanup_recorded_group(leader, root / "test.pid")
                        if (root / "child.pid").exists():
                            try: os.kill(int((root / "child.pid").read_text()), signal.SIGKILL)
                            except ProcessLookupError: pass

    def test_zero_grace_before_term_handler_is_recovery_failure(self):
        import contextlib
        import io
        import signal
        import tempfile
        import time
        for shell in self.shells:
            with self.subTest(shell=shell), tempfile.TemporaryDirectory() as directory:
                root = Path(directory); run = root / "run.sh"
                run.write_text(self.prepare(root, True) +
                    """step long sh -c 'echo $$ > "$S/child.pid"; touch "$S/ready"; exec sleep 30'
finish 0
""")
                with (root / "run.log").open("w") as log:
                    process = subprocess.Popen([shell, str(run)], start_new_session=True, stdout=log, stderr=log)
                    try:
                        until = time.monotonic() + 5
                        while not (root / "ready").exists() and time.monotonic() < until: time.sleep(.01)
                        self.assertTrue((root / "ready").exists())
                        api, pid, signals = self.escalation_fixture(root, process, run)
                        # Freeze the test's recorded leader before TERM: its
                        # trap cannot acknowledge cancellation ahead of KILL.
                        os.kill(pid, signal.SIGSTOP)
                        out, err = io.StringIO(), io.StringIO()
                        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                            rc = api["stop_run"](pid, 888, root, root / "proc", grace=0)
                        self.assertEqual(rc, 2, out.getvalue() + err.getvalue())
                        self.assertIn("recovery failed", err.getvalue())
                        self.assertIn(str(root), err.getvalue())
                        self.assertEqual(signals, [signal.SIGTERM, signal.SIGKILL])
                        self.assertIsNotNone(process.poll())
                        self.assertFalse((root / "status").exists())
                        self.assertFalse((root / "stopped").exists())
                        self.assert_pid_gone(int((root / "child.pid").read_text()))
                    finally:
                        cleanup_recorded_group(process, root / "test.pid")

    def test_term_after_normal_publication_cannot_change_final_status(self):
        import signal
        import tempfile
        import time
        for shell in self.shells:
            with self.subTest(shell=shell), tempfile.TemporaryDirectory() as directory:
                root = Path(directory); run = root / "run.sh"
                run.write_text(self.prepare(root, True) + """
echo() {
    case "$*" in '== done status '*)
        touch "$S/published"
        timeout 10 sh -c 'while [ ! -f "$S/release" ]; do sleep .01; done'
        ;;
    esac
    command echo "$@"
}
finish 0
""")
                with (root / "run.log").open("w") as log:
                    process = subprocess.Popen([shell, str(run)], start_new_session=True, stdout=log, stderr=log)
                    try:
                        until = time.monotonic() + 5
                        while not (root / "published").exists() and time.monotonic() < until: time.sleep(.01)
                        self.assertTrue((root / "published").exists())
                        pid = int((root / "test.pid").read_text()); self.assertEqual(pid, process.pid)
                        self.assertEqual((root / "status").read_text(), "0\n")
                        os.killpg(pid, signal.SIGTERM)
                        time.sleep(.1)
                        self.assertEqual((root / "status").read_text(), "0\n")
                        self.assertFalse((root / "stopped").exists())
                        (root / "release").touch()
                        self.assertEqual(process.wait(timeout=5), 0, (root / "run.log").read_text())
                        self.assertEqual((root / "status").read_text(), "0\n")
                        self.assertFalse((root / "stopped").exists())
                    finally:
                        cleanup_recorded_group(process, root / "test.pid")

    def test_hung_artifact_collectors_have_timeout_and_kill_backstops(self):
        import json
        import shutil
        import signal
        import tempfile
        import time
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            run = root / "run.sh"
            prepared = self.prepare(root, True)
            shim = root / "timeout"
            # Record the generated 120s/5s limits, but use 0.1s in this probe.
            # Both controlled collectors ignore TERM so -k is exercised.
            shim.write_text("#!" + sys.executable + "\n" + '''import json, os, sys
from pathlib import Path
root = Path(os.environ["S"])
args = sys.argv[1:]
with (root / "timeouts.jsonl").open("a") as out:
    out.write(json.dumps(args) + "\\n")
assert args[:3] == ["-k", "5", "120"]
name = "hash.pid" if args[3] == "sh" else "walls.pid"
command = 'trap "" TERM; echo $$ > "$S/' + name + '"; exec sleep 30'
os.execv(REAL_TIMEOUT, [REAL_TIMEOUT, "-k", "0.1", "0.1", "sh", "-c", command])
'''.replace("REAL_TIMEOUT", repr(shutil.which("timeout"))))
            shim.chmod(0o755)
            run.write_text(prepared + 'STOPPED=1\nfinish 143\ntouch "$S/later"\n')
            with (root / "run.log").open("w") as log:
                leader = subprocess.Popen(["/bin/sh", str(run)], start_new_session=True, stdout=log, stderr=log)
                try:
                    began = time.monotonic()
                    self.assertEqual(leader.wait(timeout=8), 143, (root / "run.log").read_text())
                    self.assertLess(time.monotonic() - began, 5)
                    self.assertEqual((root / "status").read_text(), "143\n")
                    self.assertTrue((root / "stopped").is_file())
                    calls = [json.loads(line) for line in (root / "timeouts.jsonl").read_text().splitlines()]
                    self.assertEqual(len(calls), 2)
                    self.assertEqual([call[3] for call in calls], ["sh", "python3"])
                    for name in ("hash.pid", "walls.pid"):
                        with self.assertRaises(ProcessLookupError): os.kill(int((root / name).read_text()), 0)
                    self.assertFalse((root / "later").exists())
                finally:
                    cleanup_recorded_group(leader, root / "test.pid")
                    for name in ("hash.pid", "walls.pid"):
                        if (root / name).exists():
                            try: os.kill(int((root / name).read_text()), signal.SIGKILL)
                            except ProcessLookupError: pass

    def collector_probe(self, root, slow=False):
        import shutil
        # Record timeout's own PID before exec; plain timeout then creates
        # its own group. Keep the production arguments but shorten this probe.
        (root / "timeout").write_text("#!" + sys.executable + "\n" + '''import os, sys
from pathlib import Path
args = sys.argv[1:]
assert args[:3] == ["-k", "5", "120"]
root = Path(os.environ["S"])
name = "hash" if args[3] == "sh" else "walls"
(root / (name + "-timeout.pid")).write_text(str(os.getpid()))
os.execv(REAL_TIMEOUT, [REAL_TIMEOUT, "-k", "0.1", DURATION, *args[3:]])
'''.replace("REAL_TIMEOUT", repr(shutil.which("timeout"))).replace("DURATION", repr("30" if slow else "0.1")))
        (root / "timeout").chmod(0o755)
        (root / "sleeper.sh").write_text('#!/bin/sh\necho $$ > "$S/sleep.pid"\nexec sleep 600\n')
        body = 'exec sleep 600' if slow else '''sh -c 'echo $$ > "$S/descendant.pid"; sh "$S/sleeper.sh" & wait' & wait'''
        (root / "sh").write_text('''#!/bin/sh
case "$1:$2" in -c:*sha256sum*)
    trap "" TERM
    echo $$ > "$S/collector.pid"
    touch "$S/collector-started"
    BODY
    ;;
esac
exec /bin/sh "$@"
'''.replace("BODY", body))
        (root / "sh").chmod(0o755)

    def assert_pid_gone(self, pid):
        import time
        for _ in range(100):
            try: os.kill(pid, 0)
            except ProcessLookupError: return
            time.sleep(.01)
        self.fail(f"recorded process {pid} survived")

    def clean_recorded_collectors(self, root):
        import signal
        for name in ("hash-timeout.pid", "walls-timeout.pid", "collector.pid", "descendant.pid", "sleep.pid"):
            recorded = root / name
            if recorded.exists():
                try: os.kill(int(recorded.read_text()), signal.SIGKILL)
                except ProcessLookupError: pass

    def test_cancellation_status_precedes_slow_collection_and_survives_grace_kill(self):
        import signal
        import tempfile
        import time
        for shell in self.shells:
            with self.subTest(shell=shell), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                prepared = self.prepare(root, True)
                self.collector_probe(root, slow=True)
                run = root / "run.sh"
                run.write_text(prepared + 'finish 0\ntouch "$S/later"\n')
                with (root / "run.log").open("w") as log:
                    leader = subprocess.Popen([shell, str(run)], start_new_session=True, stdout=log, stderr=log)
                    try:
                        until = time.monotonic() + 5
                        while not (root / "collector-started").exists() and time.monotonic() < until:
                            time.sleep(.01)
                        self.assertTrue((root / "collector-started").exists(), (root / "run.log").read_text())
                        self.assertFalse((root / "status").exists())
                        self.assertIsNone(leader.poll())
                        api, pid, signals = self.escalation_fixture(root, leader, run)
                        original_signal = api["signal"].pidfd_send_signal
                        def checked_signal(fd, sig, info, flags):
                            if sig == signal.SIGKILL:
                                self.assertEqual((root / "status").read_text(), "143\n")
                                self.assertTrue((root / "stopped").read_text().startswith("TERM "))
                            original_signal(fd, sig, info, flags)
                        api["signal"].pidfd_send_signal = checked_signal
                        self.assertEqual(api["stop_run"](pid, 888, root, root / "proc", grace=.2), 0)
                        self.assertEqual(signals, [signal.SIGTERM, signal.SIGKILL])
                        self.assertEqual((root / "status").read_text(), "143\n")
                        self.assertTrue((root / "stopped").exists())
                        self.assertFalse((root / "later").exists())
                    finally:
                        cleanup_recorded_group(leader, root / "test.pid")
                        self.clean_recorded_collectors(root)

    def test_normal_finish_timeout_removes_collector_descendant_before_return(self):
        import signal
        import tempfile
        for shell in self.shells:
            with self.subTest(shell=shell), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                prepared = self.prepare(root, True)
                self.collector_probe(root)
                run = root / "run.sh"
                run.write_text(prepared + 'finish 0\n')
                with (root / "run.log").open("w") as log:
                    leader = subprocess.Popen([shell, str(run)], start_new_session=True, stdout=log, stderr=log)
                    try:
                        self.assertEqual(leader.wait(timeout=8), 0, (root / "run.log").read_text())
                        self.assertEqual((root / "status").read_text(), "0\n")
                        self.assertFalse((root / "stopped").exists())
                        for name in ("collector.pid", "descendant.pid", "sleep.pid", "hash-timeout.pid", "walls-timeout.pid"):
                            self.assertTrue((root / name).exists(), name)
                            self.assert_pid_gone(int((root / name).read_text()))
                    finally:
                        cleanup_recorded_group(leader, root / "test.pid")
                        self.clean_recorded_collectors(root)

    def test_step_can_execute_a_shell_function_after_closing_the_lock_fd(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            run = root / "run.sh"
            run.write_text(self.prepare(root, True) + '''
static_gate() { echo real-function; }
step function static_gate
finish 0
''')
            done = subprocess.run(["/bin/sh", str(run)], capture_output=True, text=True, timeout=10)
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertEqual((root / "logs/function.log").read_text(), "real-function\n")



class NativeStopTests(unittest.TestCase):
    def setUp(self):
        import tempfile
        from types import SimpleNamespace
        from unittest import mock
        self.temp = tempfile.TemporaryDirectory(prefix="fn-native-stop-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.run_dir = self.root / "run"
        self.run_dir.mkdir()
        self.proc = self.root / "proc"
        (self.proc / "4242").mkdir(parents=True)
        self.code = SCRIPT.read_text().split("    cat <<'PROCESS'\n", 1)[1].split("\nPROCESS\n", 1)[0]
        self.api = {"__name__": "native_process_test"}
        exec(compile(self.code, str(SCRIPT), "exec"), self.api)
        self.events = []
        self.fake_os = SimpleNamespace(fsencode=os.fsencode,
            pidfd_open=mock.Mock(side_effect=lambda pid: self.events.append(("open", pid)) or 701),
            close=mock.Mock(side_effect=lambda fd: self.events.append(("close", fd))))
        self.fake_signal = SimpleNamespace(SIGTERM=15, SIGKILL=9,
            pidfd_send_signal=mock.Mock(side_effect=lambda *args: self.events.append(("signal", args))))
        self.fake_subprocess = SimpleNamespace(TimeoutExpired=subprocess.TimeoutExpired,
            run=mock.Mock(side_effect=lambda args, **kw: self.events.append(
                ("query" if args[2] == "show" else "scope", args[-1])) or
                SimpleNamespace(returncode=0, stdout="LoadState=loaded\nActiveState=active\n"
                                if args[2] == "show" else "", stderr="")))
        self.api.update(os=self.fake_os, signal=self.fake_signal, subprocess=self.fake_subprocess,
                        leader_exited=lambda fd, seconds=0: True)
        self.units = [self.api["scope_prefix"](self.run_dir, 4242, 888) + f"-{n}.scope" for n in (1, 2)]
        (self.run_dir / "scopes").write_text("\n".join(self.units) + "\n")
        (self.run_dir / "run.starttime").write_text("888\n")
        (self.run_dir / "scope-prefix").write_text(self.api["scope_prefix"](self.run_dir, 4242, 888) + "\n")
        self.identity()
        (self.run_dir / "status").write_text("143\n")
        (self.run_dir / "stopped").write_text("TERM fixture\n")

    def identity(self, pgid=4242, starttime=888, cmdline=None):
        # Parenthesized comm exercises spaces and ')' without shifting field 22.
        fields = ["S", "999", str(pgid)] + ["0"] * 16 + [str(starttime)] + ["0"] * 20
        (self.proc / "4242/stat").write_text("4242 (sh (odd) name) " + " ".join(fields))
        (self.proc / "4242/cmdline").write_bytes(
            cmdline if cmdline is not None else b"sh\0" + os.fsencode(str(self.run_dir / "run.sh")) + b"\0")

    def stop(self):
        import contextlib
        import io
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = self.api["stop_run"](4242, 888, self.run_dir, self.proc)
        return rc, out.getvalue(), err.getvalue()

    def test_group_members_parser_excludes_leader_and_helper_with_odd_comm(self):
        for pid, pgid in ((4242, 4242), (4243, 4242), (4244, 4242), (4245, 1234)):
            directory = self.proc / str(pid)
            directory.mkdir(exist_ok=True)
            fields = ["S", "9", str(pgid)] + ["0"] * 16 + ["888"]
            (directory / "stat").write_text(f"{pid} (comm with (parentheses) and ) spaces) " + " ".join(fields))
        self.fake_os.getpid = lambda: 4243
        self.assertEqual(self.api["group_members"](4242, self.proc), [4244])
        (self.proc / "self").mkdir()
        (self.proc / "4246").mkdir()  # Gone between readdir and stat.
        self.assertEqual(self.api["group_members"](4242, self.proc, helper_pid=4243), [4244])
        (self.proc / "4244/stat").write_text("malformed")
        with self.assertRaises((ValueError, IndexError)):
            self.api["group_members"](4242, self.proc, helper_pid=4243)

    def test_identity_capture_records_field_22_and_run_specific_scope_prefix(self):
        original = self.api["process_stat"]
        self.api["process_stat"] = lambda pid: original(pid, self.proc)
        import contextlib
        import io
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            self.api["write_identity"](4242, self.run_dir, "a" * 32)
        self.assertEqual((self.run_dir / "run.starttime").read_text(), "888\n")
        prefix = (self.run_dir / "scope-prefix").read_text().strip()
        self.assertEqual(printed.getvalue(), prefix + "\n")
        self.assertEqual((self.run_dir / "run.identity").read_text(),
                         "a" * 32 + " 4242 888 " + prefix + "\n")
        self.assertFalse((self.run_dir / "run.identity.4242.tmp").exists())
        self.assertTrue(self.units[0].startswith(prefix + "-"))
        self.assertNotEqual(prefix, self.api["scope_prefix"](self.run_dir, 4242, 889))
        self.assertNotEqual(prefix, self.api["scope_prefix"](self.root / "other", 4242, 888))

    def test_prefix_distinguishes_leaders_in_the_same_clock_tick(self):
        self.assertNotEqual(self.api["scope_prefix"](self.run_dir, 4242, 888),
                            self.api["scope_prefix"](self.run_dir, 4243, 888))

    def test_esrch_retry_stops_exact_recorded_scopes_with_real_fake_systemctl(self):
        import errno
        import contextlib
        import io
        from unittest import mock
        # Execute the real subprocess path against a fake bus, with real locking.
        self.api.update(os=os, subprocess=subprocess)
        fake = self.root / "systemctl"
        fake.write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "$CALLS"\n'
                        '[ "$2" != show ] || printf "LoadState=loaded\\nActiveState=active\\n"\n'
                        'exit 0\n')
        fake.chmod(0o755)
        calls = self.root / "calls"
        output = io.StringIO()
        with mock.patch.dict(os.environ, {"PATH": str(self.root) + os.pathsep + os.environ["PATH"],
                                         "CALLS": str(calls)}), \
             mock.patch.object(os, "pidfd_open", create=True, side_effect=ProcessLookupError(errno.ESRCH, "gone")), \
             contextlib.redirect_stdout(output):
            self.assertEqual(self.api["stop_run"](4242, 888, self.run_dir), 0)
            self.assertIn("already gone", output.getvalue())
            self.assertEqual(calls.read_text().splitlines(), [command + u for u in self.units
                for command in ("--user show -p LoadState,ActiveState -- ", "--user stop -- ")])
            for name, value in (("run.starttime", "999\n"), ("scope-prefix", "foreign\n")):
                old = (self.run_dir / name).read_text()
                (self.run_dir / name).write_text(value)
                calls.write_text("")
                with contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(self.api["stop_run"](4242, 888, self.run_dir), 2)
                self.assertEqual(calls.read_text(), "")
                (self.run_dir / name).write_text(old)
            import fcntl
            with (self.run_dir / "run.lock").open("a") as held:
                fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
                calls.write_text("")
                with contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(self.api["stop_run"](4242, 888, self.run_dir), 2)
                self.assertEqual(calls.read_text(), "")

    def exercise_scope_state(self, scenario, expected_rc, message, commands, esrch=False):
        import errno
        import json
        from unittest import mock
        fake = self.root / "systemctl"
        fake.write_text("#!" + sys.executable + "\n" + '''import json, os, sys
from pathlib import Path
args = sys.argv[1:]
root = Path(os.environ["SCOPE_FIXTURE"])
with (root / "state-calls.jsonl").open("a") as out:
    out.write(json.dumps(args) + "\\n")
scenario = os.environ["SCOPE_SCENARIO"]
unit = args[-1]
assert args[0] == "--user"
if args[1] == "show":
    assert args[2:-1] == ["-p", "LoadState,ActiveState", "--"]
    if scenario == "query-fails":
        print("cannot reach user bus", file=sys.stderr)
        raise SystemExit(1)
    if scenario == "malformed":
        print("ActiveState=active")
        raise SystemExit(0)
    gone = scenario == "not-loaded" or (root / (unit + ".gone")).exists()
    print("LoadState=" + ("not-found" if gone else "loaded"))
    inactive = gone or scenario == "inactive" or (root / (unit + ".inactive")).exists()
    print("ActiveState=" + ("inactive" if inactive else "active"))
elif args[1] == "stop":
    assert args[2:-1] == ["--"]
    if scenario == "disappears":
        (root / (unit + ".gone")).touch()
        print("Unit " + unit + " not loaded", file=sys.stderr)
        raise SystemExit(5)
    if scenario == "active-fails":
        print("active unit stop rejected", file=sys.stderr)
        raise SystemExit(5)
    assert scenario == "active"
    (root / (unit + ".inactive")).touch()
else:
    raise AssertionError(args)
''')
        fake.chmod(0o755)
        self.api["subprocess"] = subprocess
        if esrch:
            self.fake_os.pidfd_open.side_effect = ProcessLookupError(errno.ESRCH, "gone")
        with mock.patch.dict(os.environ, {"PATH": str(self.root) + os.pathsep + os.environ["PATH"],
                            "SCOPE_FIXTURE": str(self.root), "SCOPE_SCENARIO": scenario}):
            rc, out, err = self.stop()
        self.assertEqual(rc, expected_rc, out + err)
        for unit in self.units:
            self.assertIn(unit + ": " + message, out if expected_rc == 0 else err)
        calls = [json.loads(line) for line in (self.root / "state-calls.jsonl").read_text().splitlines()]
        expected = []
        for unit in self.units:
            for command in commands:
                expected.append(["--user", "show", "-p", "LoadState,ActiveState", "--", unit]
                                if command == "show" else ["--user", "stop", "--", unit])
        self.assertEqual(calls, expected)
        if scenario == "active":
            self.assertTrue(all((self.root / (unit + ".inactive")).exists() for unit in self.units))
        if esrch:
            self.assertIn("already gone", out)
            self.fake_signal.pidfd_send_signal.assert_not_called()
        return out, err

    def test_not_loaded_scopes_are_already_stopped_without_stop_call(self):
        self.exercise_scope_state("not-loaded", 0, "already stopped", ["show"])

    def test_inactive_scopes_are_already_stopped_without_stop_call(self):
        self.exercise_scope_state("inactive", 0, "already stopped", ["show"])

    def test_active_scopes_are_stopped(self):
        self.exercise_scope_state("active", 0, "stopped", ["show", "stop"])

    def test_active_scope_stop_failure_is_still_failure(self):
        _, err = self.exercise_scope_state("active-fails", 2, "stop failed (exit 5)", ["show", "stop", "show"])
        self.assertIn("active unit stop rejected", err)

    def test_scope_disappearing_between_query_and_stop_is_already_stopped(self):
        self.exercise_scope_state("disappears", 0, "already stopped", ["show", "stop", "show"])

    def test_esrch_retry_after_normal_end_skips_unloaded_scopes(self):
        self.exercise_scope_state("not-loaded", 0, "already stopped", ["show"], esrch=True)

    def test_scope_query_errors_are_not_mistaken_for_already_stopped(self):
        self.exercise_scope_state("query-fails", 2, "cleanup failed: state query failed (exit 1)", ["show"])

    def test_scope_query_without_properties_is_not_mistaken_for_already_stopped(self):
        self.exercise_scope_state("malformed", 2, "cleanup failed: state query omitted", ["show"])

    def test_esrch_cleanup_without_final_status_is_recovery_failure(self):
        import errno
        self.fake_os.pidfd_open.side_effect = ProcessLookupError(errno.ESRCH, "gone")
        (self.run_dir / "status").unlink()
        rc, out, err = self.stop()
        self.assertEqual(rc, 2)
        self.assertIn("was already gone", out)
        self.assertIn("recovery failed", err)
        self.assertIn(str(self.run_dir), err)
        self.assertEqual([e[1] for e in self.events if e[0] == "scope"], self.units)
        self.assertFalse((self.run_dir / "status").exists())

    def test_grace_escalates_through_the_same_pidfd_before_scope_cleanup(self):
        from unittest import mock
        self.api["leader_exited"] = mock.Mock(side_effect=[False, True])
        (self.run_dir / "status").unlink()
        (self.run_dir / "stopped").unlink()
        rc = self.api["stop_run"](4242, 888, self.run_dir, self.proc, grace=0)
        self.assertEqual(rc, 2)
        self.assertFalse((self.run_dir / "status").exists())
        self.assertFalse((self.run_dir / "stopped").exists())
        self.assertEqual([c.args for c in self.fake_signal.pidfd_send_signal.call_args_list],
                         [(701, 15, None, 4), (701, 9, None, 4)])
        self.assertEqual([e[0] for e in self.events], ["open", "signal", "signal", "query", "scope", "query", "scope", "close"])

    def test_opens_pidfd_before_identity_and_uses_only_it_to_signal(self):
        self.fake_signal.PIDFD_SIGNAL_PROCESS_GROUP = 4
        original = self.api["process_stat"]
        def checked_stat(*args):
            self.assertEqual(self.events, [("open", 4242)])
            return original(*args)
        self.api["process_stat"] = checked_stat
        rc, out, err = self.stop()
        self.assertEqual(rc, 0, err)
        self.fake_os.pidfd_open.assert_called_once_with(4242)
        self.fake_signal.pidfd_send_signal.assert_called_once_with(701, 15, None, 4)
        self.fake_os.close.assert_called_once_with(701)
        self.assertLess(next(i for i, e in enumerate(self.events) if e[0] == "signal"),
                        next(i for i, e in enumerate(self.events) if e[0] == "scope"))
        self.assertIn("sent TERM through pidfd", out)
        self.assertIn("run.sh writes status 143 when it exits", out)
        self.assertEqual((self.run_dir / "status").read_text(), "143\n")  # stop is not a status writer
        self.assertNotIn("os.kill", self.code)
        self.assertNotIn("killpg", self.code)

    def test_reuse_between_open_and_identity_is_refused(self):
        def opened(pid):
            self.events.append(("open", pid))
            self.identity(starttime=999)
            return 701
        self.fake_os.pidfd_open.side_effect = opened
        rc, _, err = self.stop()
        self.assertEqual(rc, 2)
        self.assertIn("start time", err)
        self.fake_signal.pidfd_send_signal.assert_not_called()
        self.fake_subprocess.run.assert_not_called()
        self.fake_os.close.assert_called_once_with(701)

    def test_reuse_after_identity_cannot_redirect_signal_to_numeric_pid(self):
        def signal_pinned(fd, sig, info, flags):
            self.identity(starttime=999, cmdline=b"sh\0/tmp/stranger/run.sh\0")
            self.events.append(("signal", (fd, sig, info, flags)))
            self.assertEqual((fd, sig, info, flags), (701, 15, None, 4))
        # The absent constant must use flag 4, never a numeric kill fallback.
        self.fake_signal.pidfd_send_signal.side_effect = signal_pinned
        rc, _, err = self.stop()
        self.assertEqual(rc, 0, err)
        self.fake_signal.pidfd_send_signal.assert_called_once_with(701, 15, None, 4)

    def test_missing_leader_or_unsupported_pidfd_refuses_without_cleanup(self):
        for error in (OSError("pidfd unavailable"), AttributeError("pidfd unavailable")):
            with self.subTest(error=error):
                self.fake_os.pidfd_open.side_effect = error
                rc, _, err = self.stop()
                self.assertEqual(rc, 2)
                self.assertIn("refused stop", err)
                self.fake_signal.pidfd_send_signal.assert_not_called()
                self.fake_subprocess.run.assert_not_called()
                self.fake_os.close.assert_not_called()

    def test_nonleader_wrong_starttime_and_inexact_commands_refuse(self):
        cases = [(12, 888, None, "group leader"), (4242, 889, None, "start time"),
                 (4242, 888, b"sh\0/tmp/stranger/run.sh\0", "command line"),
                 (4242, 888, b"sh\0" + os.fsencode(str(self.run_dir / "run.sh.extra")) + b"\0", "command line"),
                 (4242, 888, b"sh\0" + os.fsencode(str(self.run_dir / "run.sh")) + b"\0extra\0", "command line")]
        for pgid, start, cmd, message in cases:
            with self.subTest(message=message, cmd=cmd):
                self.identity(pgid, start, cmd)
                rc, _, err = self.stop()
                self.assertEqual(rc, 2)
                self.assertIn(message, err)
                self.fake_signal.pidfd_send_signal.assert_not_called()
                self.fake_subprocess.run.assert_not_called()

    def test_leader_exit_or_unsupported_group_signal_refuses_without_numeric_fallback(self):
        for error in (ProcessLookupError("pinned leader exited"), OSError("group flag unsupported")):
            with self.subTest(error=error):
                self.fake_signal.pidfd_send_signal.side_effect = error
                rc, _, err = self.stop()
                self.assertEqual(rc, 2)
                self.assertIn("refused stop", err)
                self.fake_subprocess.run.assert_not_called()

    def test_only_recorded_exact_units_are_stopped_after_term_and_reported(self):
        from types import SimpleNamespace
        active = SimpleNamespace(returncode=0, stdout="LoadState=loaded\nActiveState=active\n", stderr="")
        self.fake_subprocess.run.side_effect = [active,
            SimpleNamespace(returncode=1, stdout="", stderr="unit failure"), active, active,
            SimpleNamespace(returncode=0, stdout="", stderr="")]
        # Deduplicate; reject foreign run units, option injection and globs.
        (self.run_dir / "scopes").write_text("\n".join(
            [self.units[0], self.units[0], "--all", "fn-native-foreign-888-1.scope", "*.scope", self.units[1]]) + "\n")
        rc, out, err = self.stop()
        self.assertEqual(rc, 2)
        calls = self.fake_subprocess.run.call_args_list
        self.assertEqual([c.args[0] for c in calls],
                         [["systemctl", "--user", "show", "-p", "LoadState,ActiveState", "--", self.units[0]],
                          ["systemctl", "--user", "stop", "--", self.units[0]],
                          ["systemctl", "--user", "show", "-p", "LoadState,ActiveState", "--", self.units[0]],
                          ["systemctl", "--user", "show", "-p", "LoadState,ActiveState", "--", self.units[1]],
                          ["systemctl", "--user", "stop", "--", self.units[1]]])
        self.assertTrue(all(c.kwargs["timeout"] == 60 for c in calls))
        self.assertIn(self.units[0] + ": stop failed (exit 1): unit failure", err)
        self.assertIn(self.units[1] + ": stopped", out)
        self.assertIn("refused scope name outside this run", err)

    def test_stop_transport_uses_recorded_starttime_and_legacy_stop_refuses(self):
        import shlex
        launcher = isolated_launcher(self.root)
        command = self.root / "command"
        source = self.root / "source"
        ssh = self.root / "ssh"
        ssh.write_text('#!/bin/sh\nprintf "%s" "$*" > ' + shlex.quote(str(command)) +
                       '\ncat > ' + shlex.quote(str(source)) + '\n')
        ssh.chmod(0o755)
        label = f"stop-unit-{os.getpid()}"
        record = launcher.parent.parent / "build/hbox-native" / (label + ".run")
        record.parent.mkdir(parents=True, exist_ok=True)
        record.write_text(f"box=hbox\ndir={self.run_dir}\npid=9999\npgid=4242\nstarttime=888\n")
        env = {**os.environ, "PATH": str(self.root) + os.pathsep + os.environ["PATH"]}
        request = subprocess.run(["sh", str(launcher), "stop", label], cwd=ROOT, env=env,
                                 capture_output=True, text=True, timeout=30, stdin=subprocess.DEVNULL)
        self.assertEqual(request.returncode, 0, request.stderr)
        self.assertIn(f"python3 - stop 4242 888 {self.run_dir}", command.read_text())
        self.assertNotIn("9999", command.read_text())
        self.assertEqual(source.read_text().strip(), self.code.strip())
        explicit = subprocess.run(["sh", str(launcher), "stop", label, "--grace", "2"], cwd=ROOT,
                                  env=env, capture_output=True, text=True, timeout=30)
        self.assertEqual(explicit.returncode, 0, explicit.stderr)
        self.assertIn(f"python3 - stop 4242 888 {self.run_dir} 2", command.read_text())
        command.write_text("")
        invalid = subprocess.run(["sh", str(launcher), "stop", label, "--grace", "-1"], cwd=ROOT,
                                 env=env, capture_output=True, text=True, timeout=30)
        self.assertEqual(invalid.returncode, 2)
        self.assertIn("nonnegative integer", invalid.stderr)
        self.assertEqual(command.read_text(), "")
        command.write_text("")
        record.write_text(f"box=hbox\ndir={self.run_dir}\npid=4242\npgid=4242\n")
        refused = subprocess.run(["sh", str(launcher), "stop", label], cwd=ROOT, env=env,
                                 capture_output=True, text=True, timeout=30, stdin=subprocess.DEVNULL)
        self.assertEqual(refused.returncode, 2)
        self.assertIn("lacks a safe starttime", refused.stderr)
        self.assertEqual(command.read_text(), "")
        record.write_text(f"box=hbox\ndir={self.run_dir}\npid=4242\n")
        for mode in ("status", "attach", "stop"):
            refused = subprocess.run(["sh", str(launcher), mode, label], cwd=ROOT, env=env,
                                     capture_output=True, text=True, timeout=30, stdin=subprocess.DEVNULL)
            self.assertEqual(refused.returncode, 2, refused.stdout + refused.stderr)
            self.assertIn("use adopt " + label, refused.stderr)
            self.assertEqual(command.read_text(), "")


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

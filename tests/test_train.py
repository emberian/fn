"""Tests for tools/train.py against a throwaway origin + batch worktree with stub tools.

TRAIN_SCRIPT may point at an alternative copy of train.py (used to show a test
red against a variant that skips a rule).
"""
import ast
import contextlib
import io
import json
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tests.scratch_git import run as scratch_git

from tools import train

REPO = Path(__file__).resolve().parent.parent
SCRIPT = Path(os.environ.get("TRAIN_SCRIPT", REPO / "tools" / "train.py"))

STUB = '''#!/usr/bin/env python3
import json, os, sys
name = os.path.basename(__file__)[:-3]
# a test-suite stub runs under `python -m unittest <file>`: no mode of its own
args = [] if name.startswith("test_") else [a for a in sys.argv[1:]]
mode = args[0].lstrip("-") if args else ""
with open(os.environ["STUB_LOG"], "a") as f:
    f.write(name + " " + " ".join(args) + "\\n")
if name == "lock_discipline_check":
    keys = json.load(open("lockkeys.json"))
    if isinstance(keys, dict):
        # a contract-breaking checker: raw stdout, then an exit or a signal
        sys.stdout.write(keys["raw"]); sys.stdout.flush()
        if keys.get("signal"):
            import signal; os.kill(os.getpid(), signal.SIGKILL)
        sys.exit(keys.get("rc", 0))
    # the checker's current shape: `new` is a list of key strings
    print(json.dumps({"new": list(keys), "stale": [], "findings": []}))
    sys.exit(0)
if name == "world" and os.environ.get("STUB_WORLD"):
    # world.py re-links the umbrella: one part appears, one goes
    with open("books/image-world-part-9.lisp", "w") as f:
        f.write("new part\\n")
    if os.path.exists("books/image-world-part-1.lisp"):
        os.remove("books/image-world-part-1.lisp")
if name == "premise_audit" and mode == "json":
    every = "--all" in args and "STUB_PREMISES_ALL" in os.environ
    print(os.environ["STUB_PREMISES_ALL"] if every else os.environ.get("STUB_PREMISES", "{}"))
if mode == "write" and name == "resource_contract" and os.environ.get("STUB_CONTRACT"):
    os.makedirs("docs", exist_ok=True)
    with open("docs/resource-contract.md", "a") as f:
        f.write("block\\n")
if mode == "write" and name == "ledger":
    with open("planning/proofs.json", "a") as f:
        f.write("regen\\n")
sys.exit(int(os.environ.get("STUB_RC_%s_%s" % (name, mode), "0")))
'''
STUBS = ["tools/ledger.py", "tools/current_view.py", "tools/host_check.py",
         "tools/cost_obligations.py", "tools/book_roots_check.py",
         "tools/lock_discipline_check.py",
         "tools/secrets_check.py", "planning/repair/repair.py",
         "tools/main_last_check.py", "tools/interface_emit.py", "tools/extract/world.py",
         "tests/test_ledger.py", "tests/test_keystone_emit.py", "tests/test_train.py",
         "tests/test_farm.py", "tests/test_current_view.py", "tools/keystone_emit.py",
         "tests/test_keystone_critical.py", "tools/harness_check.py", "tools/premise_audit.py",
         "tools/resource_contract.py"]
REMOTE_STUB = '''#!/bin/sh
echo "remote_check $*" >> "$STUB_LOG"
for out in build/box/wire-grammar.json; do
  [ -n "$STUB_EMIT" ] && mkdir -p "$(dirname $out)" && echo "$STUB_EMIT" > "$out"
done
exit "${STUB_RC_remote_check:-0}"
'''


FARM_STUB = '''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
args = sys.argv[1:]
with open(os.environ["STUB_LOG"], "a") as f:
    f.write("farm " + " ".join(args) + "\\n")
act = [a for a in args if a in ("submit", "wait")][0]
rc = int(os.environ.get("STUB_RC_farm_" + act, "0"))
if act == "wait" and (os.environ.get("STUB_FAILED_BOOKS") or os.environ.get("STUB_KILLED_BOOKS")):
    failed = [b for b in os.environ.get("STUB_FAILED_BOOKS", "").split(",") if b]
    killed = [b for b in os.environ.get("STUB_KILLED_BOOKS", "").split(",") if b]
    man = Path("build/acl2/certify-stub-1/manifest.json")
    man.parent.mkdir(parents=True, exist_ok=True)
    results = {"books/wire-export": "passed", **{b: "failed" for b in failed + killed}}
    reasons = {**{b: ["ACL2 Error in (DEFTHM X ...)"] for b in failed},
               **{b: ["ACL2 exited -9"] for b in killed}}
    man.write_text(json.dumps({"status": "failed", "book_results": results, "book_failures": reasons}))
if act == "submit":
    rec = Path("build/farm/run-stub-1.json")
    rec.parent.mkdir(parents=True, exist_ok=True)
    rec.write_text(json.dumps({"run_id": "run-stub-1", "remote_path": os.environ["FARM_TREE"],
                               "certify_id": "certify-stub-1"}))
    if rc == 0:
        print("run-stub-1")
sys.exit(rc)
'''
SSH_STUB = '''#!/bin/sh
# ssh BOX COMMAND: a fetch (tar) really runs; anything else is logged and "emits".
cmd=$2
case "$cmd" in
  *"tar cf"*) exec sh -c "$cmd" ;;
esac
echo "ssh $*" >> "$STUB_LOG"
if [ "${STUB_RC_ssh:-0}" = 0 ]; then
  [ -z "$STUB_CACHE_SEED" ] || echo "== cache seed $STUB_CACHE_SEED"
  for out in build/box/wire-grammar.json; do
    mkdir -p "$FARM_TREE/$(dirname $out)" && echo "${STUB_EMIT:-emitted}" > "$FARM_TREE/$out"
  done
fi
exit "${STUB_RC_ssh:-0}"
'''


def sh(cwd, *argv, env=None, check=True):
    runner = scratch_git if argv[:1] == ("git",) else subprocess.run
    p = runner(argv, cwd=cwd, capture_output=True, text=True, env=env)
    if check and p.returncode != 0:
        raise AssertionError(f"{argv} rc {p.returncode}\n{p.stdout}\n{p.stderr}")
    return p


class CacheSeedTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="train-seed-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.train = SimpleNamespace(root=self.root, dir=self.root / "build/train")
        self.train.dir.mkdir(parents=True)
        self.old = self.root / "old ' tree"
        self.new = self.root / "new ' tree"
        self.new.mkdir()

    def previous(self, box="hbox", farm=True):
        train.box_record_path(self.train).write_text(json.dumps({"box": box, "run": "old-run"}))
        if farm:
            record = self.root / "build/farm/old-run.json"
            record.parent.mkdir(parents=True)
            record.write_text(json.dumps({"host": box, "remote_path": str(self.old)}))

    def execute(self, box="hbox"):
        seed, run = train.cache_seed_command(self.train, box, str(self.new))
        # Run the exact constructed remote shell locally, with harmless emits.
        with mock.patch.object(train, "WRAPS", {}), \
                mock.patch.object(train, "EMIT_CMD", "echo emitted"):
            command = train.emit_remote_command(str(self.new), "true", box, seed)
        result = subprocess.run(["sh", "-c", command], capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout.endswith("emitted\n"), result.stdout)
        return seed, run, result.stdout

    def test_same_box_seeds_every_cache_and_preserves_names(self):
        self.previous()
        cache = self.old / "build/cache"
        for name in ("ledger-forms/f/key.pickle", "ledger-tree/key.pickle",
                     "ledger-tree/suspects.json", "wire-emit.json", "callgraph/key.pickle",
                     "reach/files.pickle.z", "certify-audit.json", ".hidden"):
            path = cache / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(name)
        seed, run, output = self.execute()
        self.assertIn("cp -a", seed)
        self.assertEqual(run, "old-run")
        self.assertIn("== cache seed old-run\n", output)
        for path in cache.rglob("*"):
            if path.is_file():
                self.assertEqual((self.new / "build/cache" / path.relative_to(cache)).read_bytes(), path.read_bytes())

    def test_same_tree_keeps_its_cache_in_place(self):
        # farm reuses one remote tree per worktree: no copy onto itself (train 28 logged "copy failed")
        self.old = self.new
        self.previous()
        (self.new / "build/cache").mkdir(parents=True)
        (self.new / "build/cache/wire-emit.json").write_text("stamp")
        seed, run, output = self.execute()
        self.assertNotIn("cp -a", seed)
        self.assertEqual(run, "old-run")
        self.assertIn("== cache seed old-run (same tree; cache in place)\n", output)
        self.assertEqual((self.new / "build/cache/wire-emit.json").read_text(), "stamp")

    def test_absent_record_skips(self):
        seed, run, output = self.execute()
        self.assertNotIn("cp -a", seed)
        self.assertIsNone(run)
        self.assertIn("no previous box record", output)

    def test_different_box_skips(self):
        self.previous("persvati")
        seed, run, output = self.execute()
        self.assertNotIn("cp -a", seed)
        self.assertIsNone(run)
        self.assertIn("previous box differs", output)

    def test_missing_farm_record_skips(self):
        self.previous(farm=False)
        _, run, output = self.execute()
        self.assertIsNone(run)
        self.assertIn("previous farm record unavailable", output)

    def test_missing_remote_tree_skips(self):
        self.previous()
        _, _, output = self.execute()
        self.assertIn("previous cache missing", output)
        self.assertNotIn("== cache seed old-run\n", output)

    def test_copy_failure_does_not_block_emits_or_claim_a_seed(self):
        self.previous()
        (self.old / "build/cache").mkdir(parents=True)
        (self.new / "build").write_text("not a directory")
        _, _, output = self.execute()
        self.assertIn("copy failed", output)
        self.assertNotIn("== cache seed old-run\n", output)


class TrainBase(unittest.TestCase):
    def setUp(self):
        # Direct fixture-helper calls also need isolation when this suite is
        # invoked with a pin exported, outside the train's unit runner.
        environment = mock.patch.dict(os.environ)
        environment.start()
        self.addCleanup(environment.stop)
        for variable in train.BASE_PIN_VARS:
            os.environ.pop(variable, None)
        self.tmp = Path(tempfile.mkdtemp(prefix="train-test-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.origin = self.tmp / "origin.git"
        sh(self.tmp, "git", "init", "-q", "--bare", "-b", "dev", str(self.origin))
        self.seed = self.tmp / "seed"
        sh(self.tmp, "git", "clone", "-q", str(self.origin), str(self.seed))
        self.cfg(self.seed)
        for s in STUBS:
            p = self.seed / s
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(STUB)
        # train imports ledger's reader to derive BP host obligations. Keep
        # CLI gates stubbed while imports use the real, non-evaluating reader.
        (self.seed / "tools/ledger.py").write_text(
            'if __name__ == "__main__":\n' + textwrap.indent(STUB, "    ")
            + 'else:\n'
              '    import importlib.util, sys\n'
            + f'    spec = importlib.util.spec_from_file_location("train_fixture_ledger", {str(REPO / "tools/ledger.py")!r})\n'
              '    module = importlib.util.module_from_spec(spec)\n'
              '    sys.modules[spec.name] = module\n'
              '    spec.loader.exec_module(module)\n'
              '    globals().update({k: v for k, v in vars(module).items() if not k.startswith("__")})\n')
        # The gate imports the finding classes after querying this tool.
        # Importing its CLI stub must not terminate the scratch train process.
        (self.seed / "tools/premise_audit.py").write_text(
            'FINDING_CLASSES = ("never concluded", "preserved only", "established off the host path")\n'
            'if __name__ == "__main__":\n' + textwrap.indent(STUB, "    "))
        (self.seed / "tools/remote_check.sh").write_text(REMOTE_STUB)
        (self.seed / "tools/train.py").write_bytes(SCRIPT.read_bytes())
        (self.seed / "tools/box_artifacts.py").write_bytes((REPO / "tools/box_artifacts.py").read_bytes())
        (self.seed / "tools/certs.py").write_text("def closure(root, book): return {book: 'fixture-key'}\n")
        (self.seed / ".gitignore").write_text("build/\n__pycache__/\n")
        (self.seed / "lockkeys.json").write_text("[]\n")
        (self.seed / "src.txt").write_text("a\nb\nc\n")
        (self.seed / "tools/extract/world.lisp").write_text("base\n")
        (self.seed / "planning/decisions.md").write_text("d0\n")
        (self.seed / "planning/known-reds.json").write_text('{"rows": []}\n')
        self.commit(self.seed, "init")
        sh(self.seed, "git", "push", "-q", "origin", "HEAD:dev")
        self.work = self.tmp / "work"
        sh(self.tmp, "git", "clone", "-q", str(self.origin), str(self.work))
        self.cfg(self.work)
        sh(self.work, "git", "checkout", "-q", "-b", "integrate/t1", "origin/dev")
        # every train inherits a box step: the init commit's (no books since)
        init = sh(self.work, "git", "rev-parse", "HEAD").stdout.strip()
        (self.work / "build/train").mkdir(parents=True)
        (self.work / "build/train/box-step.json").write_text(
            json.dumps({"sha": init, "ran_at": init, "box": "persvati"}))
        self.log = self.tmp / "stub.log"
        self.env = dict(os.environ, STUB_LOG=str(self.log), TRAIN_PY=sys.executable,
                        TRAIN_PY3=sys.executable)
        for variable in train.BASE_PIN_VARS:
            self.env.pop(variable, None)

    def cfg(self, d):
        sh(d, "git", "config", "user.email", "t@example.org")
        sh(d, "git", "config", "user.name", "t")
        sh(d, "git", "config", "commit.gpgsign", "false")

    def commit(self, d, msg):
        sh(d, "git", "add", "-A")
        sh(d, "git", "commit", "-q", "-m", msg)
        return sh(d, "git", "rev-parse", "HEAD").stdout.strip()

    def lane(self, name, files, base="origin/dev"):
        """Commit `files` on lane/<name> from the seed clone, push it, return sha."""
        sh(self.seed, "git", "fetch", "-q", "origin")
        sh(self.seed, "git", "checkout", "-q", "-B", "lane/" + name, base)
        for path, text in files.items():
            if text is None:  # the lane deletes the file
                (self.seed / path).unlink()
            else:
                (self.seed / path).write_text(text)
        sha = self.commit(self.seed, "lane " + name)
        sh(self.seed, "git", "push", "-q", "origin", "HEAD:lane/" + name)
        return sha

    def advance_dev(self, files):
        """Move dev (the train's fork point) with a commit from the seed clone."""
        sh(self.seed, "git", "fetch", "-q", "origin")
        sh(self.seed, "git", "checkout", "-q", "-B", "devtip", "origin/dev")
        for path, text in files.items():
            (self.seed / path).write_text(text)
        self.commit(self.seed, "dev moves")
        sh(self.seed, "git", "push", "-q", "origin", "HEAD:dev")

    def train(self, *args, extra_env=None, check=False):
        env = dict(self.env, **(extra_env or {}))
        return sh(self.work, sys.executable, str(SCRIPT), *args, env=env, check=check)

    def stub_log(self):
        return self.log.read_text().splitlines() if self.log.exists() else []

    def origin_rev(self, ref):
        return sh(self.origin, "git", "rev-parse", ref).stdout.strip()

    def head(self):
        return sh(self.work, "git", "rev-parse", "HEAD").stdout.strip()

    def set_image(self, modules):
        path = self.work / "build/train/integrate__t1.json"
        st = json.loads(path.read_text()) if path.exists() else {"lanes": []}
        st["image"] = {"source": self.head(), "box": "hbox", "dir": "/r",
                       "modules": {m: {"rc": 0, "cases": {m + ".T.a": "ok"}} for m in modules}}
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(st))



class LaneCheckTests(TrainBase):
    def test_unit_step_removes_inherited_pins_for_a_new_fixture_suite(self):
        # This new suite has no TrainBase/environment cleanup of its own.
        suite = '''import os, unittest
from tools import train

class NewFixtureTests(unittest.TestCase):
    def test_default_fixture_base(self):
        self.assertEqual(train.train_base(), "origin/dev")
        for name in ("FN_TRAIN_BASE", "FN_LEDGER_BASE", "FN_HOST_CHECK_BASE"):
            self.assertNotIn(name, os.environ)
        self.assertEqual(os.environ["UNIT_KEEP"], "preserved")
'''
        path = "tests/test_new_fixture.py"
        (self.work / path).write_text(suite)
        pins = {name: "f" * 40 for name in ("FN_TRAIN_BASE", "FN_LEDGER_BASE", "FN_HOST_CHECK_BASE")}
        t = train.Train(self.work)
        with mock.patch.dict(os.environ, dict(self.env, **pins, UNIT_KEEP="preserved")), \
                contextlib.redirect_stdout(io.StringIO()):
            rc, record = train._unit_gate(t, [path])
            # Removing unit pins must not change the parent or other gates.
            self.assertEqual({name: os.environ[name] for name in pins}, pins)
            control = t.run("pin-env-control", [sys.executable, "-c",
                'import os; assert all(os.environ[name] == "f" * 40 for name in '
                '("FN_TRAIN_BASE", "FN_LEDGER_BASE", "FN_HOST_CHECK_BASE"))'])
        self.assertEqual(control, 0)
        self.assertIn(path, record["tests"])
        self.assertEqual(rc, 0, (t.logs / "gate-unit-test_new_fixture.log").read_text())

    def check_lane(self, name, sha, *options, extra_env=None, record=True):
        if record and not self.scratch(name).exists():
            # A real fixture record at the initial dev commit, not a guessed
            # record synthesized by the driver. The gate checks its currency.
            t = train.Train(self.work)
            dev = self.head()
            scratch = train.lane_check_tree(t, name, dev)
            train.save_box_record(scratch, {"sha": dev, "ran_at": dev, "box": "persvati"})
        return self.train("lane-check", f"{name}@{sha}", *options, extra_env=extra_env)

    def scratch(self, name):
        return self.work / "build/lanes" / ("lane-check-" + name)

    def test_ledger_red_only_in_the_merge_fails_and_copies_the_log(self):
        ledger = STUB.replace('sys.exit(int(os.environ.get(',
            'if name == "ledger" and mode == "check" and os.path.exists("lane-event") and os.path.exists("dev-event"):\n'
            '    print("merged ledger is red"); sys.exit(1)\n'
            'sys.exit(int(os.environ.get(')
        self.advance_dev({"tools/ledger.py": ledger})
        sha = self.lane("red", {"lane-event": "lane\n"})
        self.advance_dev({"dev-event": "dev\n"})
        p = self.check_lane("red", sha)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("lane-check ledger: FAIL", p.stdout)
        self.assertIn("lane-check verdict: FAIL", p.stdout)
        log = self.work / "build/lane-check" / f"red-{sha[:9]}.log"
        self.assertIn("merged ledger is red", log.read_text())
        self.assertIn(str(log), p.stdout)
        self.assertEqual(log.read_bytes(), (self.scratch("red") / "build/lane-check" / log.name).read_bytes())

    def test_regen_red_fails_before_local_gates(self):
        sha = self.lane("regen-red", {"tools/x.py": "x\n"})
        p = self.check_lane("regen-red", sha, extra_env={"STUB_RC_ledger_write": "1"})
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("lane-check regen: FAIL", p.stdout)
        self.assertNotIn("lane-check ledger: PASS", p.stdout)
        self.assertIn("lane-check verdict: FAIL", p.stdout)

    def test_regen_that_leaves_uncommitted_sources_cannot_pass(self):
        dirty_stub = STUB.replace('sys.exit(int(os.environ.get(',
            'if name == "resource_contract" and mode == "write":\n'
            '    with open("leftover-source", "w") as f: f.write("uncommitted\\n")\n'
            'sys.exit(int(os.environ.get(')
        sha = self.lane("dirty-regen", {"tools/resource_contract.py": dirty_stub})
        p = self.check_lane("dirty-regen", sha)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("lane-check regen: PASS", p.stdout)
        self.assertIn("lane-check gate: FAIL", p.stdout)
        self.assertNotIn("lane-check ledger: PASS", p.stdout)
        log = self.work / "build/lane-check" / f"dirty-regen-{sha[:9]}.log"
        self.assertIn("gates must run at a committed HEAD", log.read_text())

    def test_dropped_bare_and_term_findings_fail(self):
        for path in train.PREMISE_BASELINES:
            (self.seed / path).write_text(json.dumps({"accepted": {"still": "why"}}))
        self.commit(self.seed, "premise baselines")
        sh(self.seed, "git", "push", "-q", "origin", "HEAD:dev")
        sha = self.lane("premises", {path: '{"accepted": {}}' for path in train.PREMISE_BASELINES})
        p = self.check_lane("premises", sha, extra_env={
            "STUB_PREMISES": '{"still": {"class": "preserved only"}}',
            "STUB_PREMISES_ALL": '{"still": {"class": "preserved only"}}'})
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("lane-check premise_baseline: FAIL", p.stdout)
        self.assertIn("lane-check verdict: FAIL", p.stdout)
        log = self.work / "build/lane-check" / f"premises-{sha[:9]}.log"
        self.assertIn("premise baseline LOST", log.read_text())
        self.assertIn("premise term baseline LOST", log.read_text())
        self.assertIn("premise_audit --json --all", self.stub_log())

    def test_clean_path_runs_train_gates_and_preserves_dirty_lane_sources(self):
        sha = self.lane("clean", {"tools/x.py": "x\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        (self.seed / "src.txt").write_text("uncommitted source\n")
        before = sh(self.seed, "git", "status", "--porcelain").stdout
        dev = self.origin_rev("dev")
        scratch = train.lane_check_tree(train.Train(self.work), "clean", self.head())
        train.save_box_record(scratch, {"sha": self.head(), "ran_at": self.head(), "box": "persvati"})
        p = self.train("lane-check", str(self.seed))
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("lane-check verdict: PASS (3 box gates owed)", p.stdout)
        for name in train.GATES:
            self.assertIn(f"lane-check {name}: PASS {sys.executable} tools/train.py gate --local", p.stdout)
        for name in ("certify", "box_host_world", "image"):
            self.assertIn(f"lane-check {name}: NONE (", p.stdout)
        for name in ("reach", "keystone_cert"):
            self.assertIn(f"lane-check {name}: BOX ", p.stdout)
        self.assertIn(f"dev={dev}", p.stdout)
        self.assertIn("lane-check certify: NONE (box step inherits:", p.stdout)
        self.assertIn("lane-check extraction: BOX", p.stdout)
        for _, argv in train.LOCAL_BOX_CHECKS:
            self.assertIn(Path(argv[0]).stem + " " + " ".join(argv[1:]), self.stub_log())
        self.assertNotIn("remote_check ", "\n".join(self.stub_log()))
        self.assertEqual(sh(self.seed, "git", "status", "--porcelain").stdout, before)
        self.assertEqual(self.origin_rev("dev"), dev)
        self.assertEqual(sh(self.seed, "git", "rev-parse", "HEAD").stdout.strip(), sha)
        log = self.seed / "build/lane-check" / f"clean-{sha[:9]}.log"
        self.assertTrue(log.is_file())
        self.assertIn("ledger --write", self.stub_log())
        self.assertIn("ledger --check", self.stub_log())
        self.assertIn("keystone_emit --write-manifest", self.stub_log())
        self.assertIn("keystone_emit --check", self.stub_log())
        self.assertIn("current_view --check", self.stub_log())
        scratch = self.scratch("clean")
        self.assertEqual(sh(scratch, "git", "branch", "--show-current").stdout.strip(), "integrate/lane-check-clean")
        self.assertIn("regen", (scratch / "planning/proofs.json").read_text())
        self.assertFalse((self.seed / "planning/proofs.json").exists())

    def test_reuse_resets_to_new_dev_and_clean_removes_only_scratch(self):
        sha = self.lane("reuse", {"lane-event": "lane\n"})
        self.assertEqual(self.check_lane("reuse", sha).returncode, 0)
        old_dev = sh(self.work, "git", "rev-parse", "origin/dev").stdout.strip()
        self.advance_dev({"dev-event": "dev\n"})
        dev = self.origin_rev("dev")
        self.assertNotEqual(old_dev, dev)
        self.assertEqual(sh(self.work, "git", "rev-parse", "origin/dev").stdout.strip(), old_dev)
        p = self.check_lane("reuse", sha)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn(f"lane-check verdict: PASS (3 box gates owed) dev={dev}", p.stdout)
        self.assertEqual(sh(self.work, "git", "rev-parse", "origin/dev").stdout.strip(), old_dev)
        self.assertTrue((self.scratch("reuse") / "dev-event").is_file())
        self.assertEqual((self.scratch("reuse") / "planning/proofs.json").read_text().count("regen"), 1)
        p = self.check_lane("reuse", sha, "--clean")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertFalse(self.scratch("reuse").exists())
        self.assertNotIn("integrate/lane-check-reuse", sh(self.work, "git", "branch").stdout)
        self.assertTrue((self.work / "build/lane-check" / f"reuse-{sha[:9]}.log").is_file())
        self.assertTrue(self.seed.is_dir())

    def test_unowned_scratch_is_not_reset(self):
        sha = self.lane("occupied", {"lane-event": "lane\n"})
        scratch = self.scratch("occupied")
        scratch.mkdir(parents=True)
        sentinel = scratch / "other-seat"
        sentinel.write_text("keep\n")
        p = self.check_lane("occupied", sha)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("refusing to reset unowned scratch", (self.work / "build/lane-check" / f"occupied-{sha[:9]}.log").read_text())
        self.assertEqual(sentinel.read_text(), "keep\n")

    def test_box_image_modules_are_exactly_the_obliged_set(self):
        sha = self.lane("image", {"tools/build_native_host.sh": "launcher\n"})
        p = self.check_lane("image", sha)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("lane-check image: FAIL", p.stdout)
        line = next(l for l in p.stdout.splitlines() if l.startswith("lane-check image: BOX"))
        modules = line.split()[line.split().index("hbox") + 2:]
        self.assertEqual(modules, sorted(train.image_modules(["tools/build_native_host.sh"])))
        self.assertNotIn("--build-only", line)

    def test_reuse_preserves_and_evaluates_a_real_image_record(self):
        sha = self.lane("image-record", {"tools/build_native_host.sh": "launcher\n"})
        first = self.check_lane("image-record", sha)
        self.assertEqual(first.returncode, 1, first.stdout + first.stderr)
        scratch = train.Train(self.scratch("image-record"))
        state = scratch.load()
        modules = train.image_modules(["tools/build_native_host.sh"])
        state["image"] = {
            "source": scratch.head(), "box": "hbox", "dir": "/r",
            "modules": {m: {"rc": 0, "cases": {m + ".T.a": "ok"}} for m in modules}}
        scratch.save(state)
        second = self.check_lane("image-record", sha)
        self.assertEqual(second.returncode, 0, second.stdout + second.stderr)
        report = json.loads((scratch.root / "build/lane-check/gates.json").read_text())
        self.assertEqual(report["gates"]["image"]["rc"], 0)
        self.assertEqual(scratch.load()["image"], state["image"])
        self.assertIn("lane-check image: NONE (image gate passed)", second.stdout)

    def test_f6_host_owner_image_gate_matches_dev(self):
        (self.seed / "host").mkdir(exist_ok=True)
        sha = self.lane("host", {"host/owner-host.lisp": "(in-package \"ACL2\")\n"})
        p = self.check_lane("host", sha)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        report = json.loads((self.scratch("host") / "build/lane-check/gates.json").read_text())
        self.assertEqual(report["gates"]["image"]["rc"], 0)
        self.assertTrue(report["gates"]["image"]["skipped"])
        self.assertEqual(train.image_modules(["host/owner-host.lisp"]), {})
        self.assertIn("lane-check image: NONE (no native module obliged)", p.stdout)
        self.assertIn("lane-check extraction: BOX", p.stdout)
        self.assertIn("lane-check verdict: PASS (3 box gates owed)", p.stdout)

    def test_local_box_check_failure_blocks_inheritance_and_verdict(self):
        sha = self.lane("local-red", {"tools/x.py": "x\n"})
        p = self.check_lane("local-red", sha, extra_env={"STUB_RC_host_check_world": "7"})
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("lane-check box_step: FAIL", p.stdout)
        self.assertIn("lane-check box_host_world: BOX", p.stdout)
        self.assertNotIn("NONE (box step inherits:", p.stdout)
        self.assertIn("lane-check verdict: FAIL", p.stdout)

    def test_box_certify_uses_the_train_affected_books_and_added_roots(self):
        manifest_stub = STUB.replace('sys.exit(int(os.environ.get(',
            'if name == "keystone_emit" and mode == "write-manifest":\n'
            '    os.makedirs("build", exist_ok=True)\n'
            '    with open("build/teeth-obligations.json", "w") as f: json.dump({"entries": []}, f)\n'
            'sys.exit(int(os.environ.get(')
        (self.seed / "books").mkdir(exist_ok=True)
        sha = self.lane("books", {"books/a.lisp": "(in-package \"ACL2\")\n",
                                  "Makefile": "ACL2_BOOKS = books/new-root\n",
                                  "tools/keystone_emit.py": manifest_stub})
        p = self.check_lane("books", sha)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        line = next(l for l in p.stdout.splitlines() if l.startswith("lane-check certify: BOX"))
        self.assertIn("--affected-by books/a", line)
        self.assertIn("books/new-root", line)
        self.assertIn("books/wire-export books/image-world books/image-world-dtn books/a", line)
        self.assertNotIn("--lane", line)
        self.assertIn("lane-check box_interface_emit: BOX", p.stdout)
        self.assertIn("lane-check box_step: FAIL", p.stdout)
        self.assertIn("lane-check image: NONE (no native module obliged)", p.stdout)
        self.assertIn("lane-check extraction: BOX", p.stdout)

    def test_box_certify_for_a_changed_test_matches_the_train_command(self):
        (self.seed / "tests/acl2").mkdir(parents=True, exist_ok=True)
        manifest_stub = STUB.replace('sys.exit(int(os.environ.get(',
            'if name == "keystone_emit" and mode == "write-manifest":\n'
            '    os.makedirs("build", exist_ok=True)\n'
            '    with open("build/teeth-obligations.json", "w") as f: json.dump({"entries": []}, f)\n'
            'sys.exit(int(os.environ.get(')
        self.advance_dev({
            "Makefile": "ACL2_BOOKS = tests/acl2/base-tests tests/acl2/consumer-tests\n",
            "tests/acl2/base-tests.lisp": '(in-package "ACL2")\n',
            "tests/acl2/consumer-tests.lisp": '(include-book "base-tests")\n',
            "tools/keystone_emit.py": manifest_stub,
        })
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "--ff-only", "origin/dev")
        sha = self.lane("test-book", {
            "tests/acl2/base-tests.lisp": '(in-package "ACL2")\n; changed\n'})
        p = self.check_lane("test-book", sha)
        line = next(l for l in p.stdout.splitlines() if l.startswith("lane-check certify: BOX"))
        command = shlex.split(line.removeprefix("lane-check certify: BOX "))
        with mock.patch.object(train, "PY", sys.executable):
            self.assertEqual(command, ["timeout", "3600",
                *train.certify_command(train.Train(self.scratch("test-book")), "hbox")])
        self.assertIn("--affected-by", command)
        self.assertNotIn("--jobs", command, "farm owns the fixed per-box default")
        self.assertNotIn("auto", command)
        self.assertNotIn("--force", command, "lane-check respects load admission")
        self.assertEqual(command[command.index("--affected-by") + 1], "tests/acl2/base-tests")
        self.assertEqual(command[command.index("hbox") + 1:],
                         [*train.BOX_CERT_BOOKS, "tests/acl2/base-tests"])

    def test_f1_missing_box_record_is_a_real_gate_failure(self):
        sha = self.lane("no-record", {"tools/x.py": "x\n"})
        p = self.check_lane("no-record", sha, record=False)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        report = json.loads((self.scratch("no-record") / "build/lane-check/gates.json").read_text())
        box = report["gates"]["box_step"]
        self.assertEqual(box["rc"], 1)
        self.assertEqual(box["error"], "no box step recorded")
        self.assertNotIn("inherits_from", box)
        self.assertIn("lane-check box_step: FAIL", p.stdout)
        self.assertIn("tools/train.py boxstep hbox", p.stdout)
        self.assertNotIn("NONE (box step inherits:", p.stdout)

    def test_f4_no_books_still_owes_certifys_mandatory_roots_without_inheritance(self):
        sha = self.lane("wire", {"tools/x.py": "x\n"})
        p = self.check_lane("wire", sha, record=False)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        line = next(l for l in p.stdout.splitlines() if l.startswith("lane-check certify: BOX"))
        self.assertIn("submit hbox books/wire-export books/image-world books/image-world-dtn", line)
        self.assertNotIn("--affected-by", line)
        self.assertNotIn("lane-check certify: NONE", p.stdout)

    def test_f3_pinned_base_survives_a_shared_origin_dev_move_during_regen(self):
        baseline = json.dumps({"accepted": {"still": "why"}})
        self.advance_dev({"planning/premise-baseline.json": baseline})
        pinned = self.origin_rev("dev")
        moved = self.lane("moving-dev", {"planning/premise-baseline.json": '{"accepted": {}}'})
        mover = STUB.replace('sys.exit(int(os.environ.get(',
            'if name == "resource_contract" and mode == "write":\n'
            '    import subprocess\n'
            '    subprocess.run(["git", "-C", os.getcwd(), "update-ref", "refs/remotes/origin/dev", os.environ["MOVE_DEV"]], check=True)\n'
            'sys.exit(int(os.environ.get(')
        sha = self.lane("pinned", {"planning/premise-baseline.json": '{"accepted": {}}',
                                    "tools/resource_contract.py": mover})
        p = self.check_lane("pinned", sha, extra_env={"MOVE_DEV": moved,
            "STUB_PREMISES": '{"still": {"class": "preserved only"}}'})
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("lane-check premise_baseline: FAIL", p.stdout)
        self.assertIn(f"dev={pinned}", p.stdout)
        self.assertEqual(sh(self.work, "git", "rev-parse", "origin/dev").stdout.strip(), moved)
        report = json.loads((self.scratch("pinned") / "build/lane-check/gates.json").read_text())
        self.assertEqual(report["dev"], pinned)
        self.assertEqual({r["dev"] for r in report["gates"].values()}, {pinned})
        self.assertEqual(report["gates"]["premise_baseline"]["lost"], ["still"])

    def test_f5_merged_tree_owns_regeneration_and_new_gate_policy(self):
        sha = self.lane("older-policy", {"tools/x.py": "x\n"})
        policy = (self.seed / "tools/train.py").read_text()
        policy = policy.replace('def cmd_regen(t: Train, args) -> int:\n',
            'def cmd_regen(t: Train, args) -> int:\n    say("MERGED-REGEN-POLICY " + args.label + " " + __file__)\n')
        policy = policy.replace('def cmd_gate(t: Train, args) -> int:',
            'GATES = (*GATES, "fetched_policy")\n'
            'GATE_FUNCTIONS["fetched_policy"] = lambda t: (7, {"error": "new dev gate"})\n\n'
            'def cmd_gate(t: Train, args) -> int:')
        self.advance_dev({"tools/train.py": policy})
        p = self.check_lane("older-policy", sha)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("lane-check fetched_policy: FAIL", p.stdout)
        log = self.work / "build/lane-check" / f"older-policy-{sha[:9]}.log"
        self.assertIn("MERGED-REGEN-POLICY lane-check", log.read_text())
        self.assertIn(str(self.scratch("older-policy") / "tools/train.py"), log.read_text())
        report = json.loads((self.scratch("older-policy") / "build/lane-check/gates.json").read_text())
        self.assertEqual(report["gates"]["fetched_policy"]["rc"], 7)

    def test_cmd_gate_preserves_names_order_output_and_return_codes(self):
        # Literal order from 9fe40c34a plus the cheap gates after ascii,
        # independent of this implementation.
        baseline_gates = ("ancestor", "ledger", "current_view", "main_last", "keystone", "host_load", "ascii",
                          "cost_obligations", "book_roots", "harness", "evidence_size", "box_step", "lock_delta", "baseline", "premise_baseline", "secrets", "unit", "image")
        self.assertEqual(train.GATES, baseline_gates)
        for rc in (0, 7):
            p = self.train("gate", extra_env={"STUB_RC_ledger_check": str(rc)})
            st = json.loads((self.work / "build/train/integrate__t1.json").read_text())
            expected = {name: rc if name == "ledger" else 0 for name in baseline_gates}
            self.assertEqual({name: entry["rc"] for name, entry in st["gates"].items()}, expected)
            self.assertEqual(p.returncode, 1 if rc else 0, p.stdout + p.stderr)
            summary = "gates at " + self.head()[:9] + ": " + ", ".join(f"{n}={v}" for n, v in expected.items())
            self.assertIn(summary + "\n", p.stdout)
            self.assertEqual(self.stub_log(), [
                "ledger --check", "current_view --check", "main_last_check ", "keystone_emit --check",
                "cost_obligations --check", "book_roots_check ", "harness_check --quiet",
                "lock_discipline_check --json",
                "lock_discipline_check --json", "test_ledger ", "test_keystone_emit ",
                "test_keystone_critical ", "test_train ", "test_farm "])
            self.log.unlink()

    def test_review1_private_fetch_preserves_other_trains_tracking_refs(self):
        observer = self.tmp / "observer"
        sh(self.work, "git", "worktree", "add", "-q", "-b", "integrate/observer", str(observer), self.head())
        before = sh(observer, "git", "for-each-ref", "--format=%(refname) %(objectname)",
                    "refs/remotes/origin/").stdout
        fetch_head = self.work / ".git/FETCH_HEAD"
        fetch_before = fetch_head.read_bytes() if fetch_head.exists() else None
        self.advance_dev({"dev-event": "remote dev advances\n"})
        dev = self.origin_rev("dev")
        sha = self.lane("private-fetch", {"tools/x.py": "lane\n"})
        p = self.check_lane("private-fetch", sha)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn(f"dev={dev}", p.stdout)
        self.assertTrue((self.scratch("private-fetch") / "dev-event").is_file())
        self.assertEqual(sh(observer, "git", "for-each-ref", "--format=%(refname) %(objectname)",
                            "refs/remotes/origin/").stdout, before)
        self.assertEqual(fetch_head.read_bytes() if fetch_head.exists() else None, fetch_before)
        self.assertEqual(sh(self.work, "git", "for-each-ref", "refs/lane-check/").stdout, "")

    def test_review2_ledger_drop_uses_pinned_base_after_shared_ref_moves(self):
        # Exercise the ledger's actual fork/retirement decisions without its
        # unrelated book analysis. Expectations remain the explicit lost R.
        source = (REPO / "tools/ledger.py").read_text()
        functions = "\n\n".join(ast.get_source_segment(source, node)
                                 for node in ast.parse(source).body
                                 if isinstance(node, ast.FunctionDef)
                                 and node.name in ("fork_point_ids", "retirement_problems"))
        ledger = ('import json, os, subprocess, sys\nfrom pathlib import Path\nROOT = Path.cwd()\n'
                  + functions + '\nif "--check" in sys.argv:\n'
                  '    current = {r["id"] for r in json.loads(Path("planning/proofs.json").read_text())["proofs"]}\n'
                  '    problems = retirement_problems(fork_point_ids(), current, {})\n'
                  '    print("\\n".join(problems))\n'
                  '    sys.exit(bool(problems))\n')
        self.advance_dev({"planning/proofs.json": '{"proofs": [{"id": "R"}]}',
                          "planning/proof-events.json": '{"targets": [{"id": "R"}]}'})
        pinned = self.origin_rev("dev")
        mover = STUB.replace('sys.exit(int(os.environ.get(',
            'if name == "resource_contract" and mode == "write":\n'
            '    import subprocess\n'
            '    subprocess.run(["git", "-C", os.getcwd(), "update-ref", "refs/remotes/origin/dev", os.environ["MOVE_DEV"]], check=True)\n'
            'sys.exit(int(os.environ.get(')
        host = STUB.replace('sys.exit(int(os.environ.get(',
            'if name == "host_check" and os.environ.get("FN_HOST_CHECK_BASE") != os.environ["PINNED"]:\n'
            '    sys.exit("host base was not pinned")\n'
            'sys.exit(int(os.environ.get(')
        sha = self.lane("ledger-base", {"planning/proofs.json": '{"proofs": []}',
            "planning/proof-events.json": '{"targets": []}', "tools/ledger.py": ledger,
            "tools/resource_contract.py": mover, "tools/host_check.py": host})
        p = self.check_lane("ledger-base", sha, extra_env={"MOVE_DEV": sha, "PINNED": pinned})
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("lane-check ledger: FAIL", p.stdout)
        self.assertIn("lane-check box_step: PASS", p.stdout)
        log = self.work / "build/lane-check" / f"ledger-base-{sha[:9]}.log"
        self.assertIn("R: a row of planning/proofs.json at the fork point is gone", log.read_text())
        scratch = self.scratch("ledger-base")
        env = dict(self.env, MOVE_DEV=sha, PINNED=pinned)
        live = sh(scratch, sys.executable, "tools/ledger.py", "--check", env=env)
        self.assertEqual(live.returncode, 0)
        pinned_check = sh(scratch, sys.executable, "tools/ledger.py", "--check",
                          env=dict(env, FN_LEDGER_BASE=pinned), check=False)
        self.assertEqual(pinned_check.returncode, 1)
        report = json.loads((scratch / "build/lane-check/gates.json").read_text())
        self.assertEqual(report["gates"]["ledger"]["dev"], pinned)

    def test_review2_host_check_base_override_preserves_default_and_explicit_base(self):
        from tools import host_check
        base = self.head()
        (self.work / "host").mkdir()
        (self.work / "host/a.lisp").write_text("; changed\n")
        head = self.commit(self.work, "host changes")
        sh(self.work, "git", "update-ref", "refs/remotes/origin/dev", head)
        with mock.patch.dict(os.environ):
            os.environ.pop("FN_HOST_CHECK_BASE", None)
            self.assertEqual(host_check.touched_host_files(self.work), [])
            os.environ["FN_HOST_CHECK_BASE"] = base
            self.assertEqual(host_check.touched_host_files(self.work), ["host/a.lisp"])
            self.assertEqual(host_check.touched_host_files(self.work, head), [])

    def test_review3_ordinary_gate_keeps_image_paths_when_unit_moves_dev(self):
        mover = STUB.replace('sys.exit(int(os.environ.get(',
            'if name == "test_ledger":\n'
            '    import subprocess\n'
            '    subprocess.run(["git", "-C", os.getcwd(), "update-ref", "refs/remotes/origin/dev", os.environ["MOVE_DEV"]], check=True)\n'
            'sys.exit(int(os.environ.get(')
        (self.work / "tests/test_ledger.py").write_text(mover)
        (self.work / "packaging").mkdir()
        (self.work / "packaging/launcher-decide.sh").write_text("# launcher\n")
        head = self.commit(self.work, "launcher changes")
        p = self.train("gate", extra_env={"MOVE_DEV": head})
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertEqual(sh(self.work, "git", "rev-parse", "origin/dev").stdout.strip(), head)
        gates = json.loads((self.work / "build/train/integrate__t1.json").read_text())["gates"]
        self.assertEqual(gates["unit"]["rc"], 0)
        self.assertEqual(gates["image"]["rc"], 1)
        self.assertNotIn("skipped", gates["image"])
        self.assertIn("tests.test_native_operator_verbs", gates["image"]["need"])
        self.assertIn("no image run recorded", gates["image"]["error"])
        self.assertIn("packaging/launcher-decide.sh", next(l for l in self.stub_log() if l.startswith("secrets_check ")))

    def test_review4_added_makefile_root_owes_certify_despite_box_inheritance(self):
        (self.seed / "books").mkdir()
        self.advance_dev({"Makefile": "ACL2_BOOKS = books/wire-export\n",
                          "books/unselected.lisp": '(defthm impossible nil)\n'})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "--ff-only", "origin/dev")
        sha = self.lane("added-root", {"Makefile": "ACL2_BOOKS = books/wire-export books/unselected\n"})
        p = self.check_lane("added-root", sha)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        report = json.loads((self.scratch("added-root") / "build/lane-check/gates.json").read_text())
        self.assertEqual(report["gates"]["box_step"]["rc"], 0)
        self.assertIn("inherits_from", report["gates"]["box_step"])
        line = next(l for l in p.stdout.splitlines() if l.startswith("lane-check certify: BOX"))
        self.assertIn("books/unselected", line)
        self.assertNotIn("--affected-by", line)
        self.assertNotIn("lane-check certify: NONE", p.stdout)

    def test_review5_box_record_cannot_cover_unrun_reach_check(self):
        sha = self.lane("reach-owed", {"tools/reach_check.py": "raise SystemExit(7)\n"})
        p = self.check_lane("reach-owed", sha)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("lane-check box_step: PASS", p.stdout)
        line = next(l for l in p.stdout.splitlines() if l.startswith("lane-check reach: BOX"))
        self.assertIn("tools/reach_check.py --summary --strict", line)
        self.assertIn("--install-certs", line)
        self.assertNotIn("lane-check reach: NONE", p.stdout)

    def test_review5_box_record_cannot_cover_certificate_keystone_check(self):
        sha = self.lane("keystone-owed", {"tools/x.py": "lane\n"})
        p = self.check_lane("keystone-owed", sha, extra_env={"STUB_RC_keystone_emit_check": "7"})
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("lane-check box_step: PASS", p.stdout)
        self.assertIn("lane-check keystone: FAIL", p.stdout)
        line = next(l for l in p.stdout.splitlines() if l.startswith("lane-check keystone_cert: BOX"))
        self.assertIn("tools/keystone_emit.py --check", line)
        self.assertIn("--install-certs", line)
        self.assertNotIn("lane-check keystone_cert: NONE", p.stdout)


class MergeTests(TrainBase):
    def test_generated_conflict_takes_train_side(self):
        # train side first changes the ledger on dev; the lane changes it too.
        sha = self.lane("a", {"tools/extract/world.lisp": "lane version\n", "src.txt": "a\nb\nc\nlane\n"})
        self.advance_dev({"tools/extract/world.lisp": "dev version\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
        p = self.train("merge", f"a@{sha}")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual((self.work / "tools/extract/world.lisp").read_text(), "dev version\n")
        self.assertIn("lane", (self.work / "src.txt").read_text())
        parents = sh(self.work, "git", "rev-list", "--parents", "-n1", "HEAD").stdout.split()
        self.assertEqual(len(parents), 3, "expected a merge commit")
        self.assertIn(f"Merge lane/a @{sha} into integrate/t1", sh(self.work, "git", "log", "-1", "--format=%s").stdout)

    def test_retired_register_conflict_goes_back_to_the_lane(self):
        # the three registers left git (build/box/, build/teeth-obligations.json):
        # a lane that still commits one conflicts like source, never "ours"
        for path in ("planning/interfaces.json", "specs/wire-grammar.json",
                     "planning/teeth-obligations.json"):
            with self.subTest(path=path):
                self.setUp()
                (self.seed / Path(path).parent).mkdir(parents=True, exist_ok=True)
                sha = self.lane("k", {path: "lane register\n"})
                sh(self.seed, "git", "checkout", "-q", "-B", "devtip", "origin/dev")
                (self.seed / Path(path).parent).mkdir(parents=True, exist_ok=True)
                self.advance_dev({path: "dev register\n"})
                sh(self.work, "git", "fetch", "-q", "origin")
                sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
                p = self.train("merge", f"k@{sha}")
                self.assertNotEqual(p.returncode, 0, p.stdout)
                self.assertIn(f"source conflict in {path}", p.stdout)
                self.assertFalse((self.work / ".git" / "MERGE_HEAD").exists())

    def test_regen_commits_no_teeth_manifest(self):
        stub = self.work / "tools/keystone_emit.py"
        stub.write_text(STUB.replace("import json, os, sys", "import json, os, sys\nfrom pathlib import Path\n"
                                     "Path('build').mkdir(exist_ok=True)\n"
                                     "Path('build/teeth-obligations.json').write_text('{}')", 1))
        self.commit(self.work, "manifest-writing stub")
        r = self.train("regen")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("keystone_emit --write-manifest", self.stub_log())
        self.assertTrue((self.work / "build/teeth-obligations.json").is_file())
        self.assertEqual(sh(self.work, "git", "ls-files", "build", "planning/teeth-obligations.json").stdout, "")
        self.assertEqual(sh(self.work, "git", "status", "--porcelain").stdout.strip(), "")

    def test_world_part_conflict_takes_train_side(self):
        (self.seed / "books").mkdir(exist_ok=True)
        sha = self.lane("w", {"books/image-world-part-2.lisp": "lane part\n"})
        sh(self.seed, "git", "checkout", "-q", "-B", "devtip", "origin/dev")
        (self.seed / "books").mkdir(exist_ok=True)
        self.advance_dev({"books/image-world-part-2.lisp": "dev part\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
        p = self.train("merge", f"w@{sha}")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual((self.work / "books/image-world-part-2.lisp").read_text(), "dev part\n")

    def test_regen_commits_world_parts_added_and_removed(self):
        (self.work / "books").mkdir(exist_ok=True)
        (self.work / "books/image-world-part-1.lisp").write_text("old part\n")
        self.commit(self.work, "a part")
        r = self.train("regen", extra_env={"STUB_WORLD": "1"})
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(sh(self.work, "git", "status", "--porcelain").stdout.strip(), "")
        tracked = sh(self.work, "git", "ls-files", "books").stdout.split()
        self.assertIn("books/image-world-part-9.lisp", tracked)
        self.assertNotIn("books/image-world-part-1.lisp", tracked)

    def test_curated_proofs_conflict_goes_back_to_the_lane(self):
        # proofs.json rows are lane-curated: a conflict is not resolved to ours.
        sha = self.lane("p", {"planning/proofs.json": "lane repoint\n"})
        self.advance_dev({"planning/proofs.json": "dev row\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
        p = self.train("merge", f"p@{sha}")
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("planning/proofs.json", p.stdout)
        self.assertEqual((self.work / "planning/proofs.json").read_text(), "dev row\n")
        self.assertFalse((self.work / ".git" / "MERGE_HEAD").exists())

    def test_source_conflict_aborts_lane_and_next_lane_merges(self):
        bad = self.lane("bad", {"src.txt": "a\nlane-bad\nc\n"})
        good = self.lane("good", {"other.txt": "ok\n"})
        self.advance_dev({"src.txt": "a\ndev-edit\nc\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
        p = self.train("merge", f"bad@{bad}", f"good@{good}")
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("src.txt", p.stdout)
        self.assertEqual((self.work / "src.txt").read_text(), "a\ndev-edit\nc\n")
        self.assertTrue((self.work / "other.txt").exists(), "next lane must still merge")
        self.assertFalse((self.work / ".git" / "MERGE_HEAD").exists())
        st = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        self.assertEqual([l["status"] for l in st["lanes"]], ["conflict", "merged"])

    def test_decisions_union_keeps_both_sides(self):
        a = self.lane("a", {"planning/decisions.md": "d0\nda\n"})
        self.advance_dev({"planning/decisions.md": "d0\ndd\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
        p = self.train("merge", f"a@{a}")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        dec = (self.work / "planning/decisions.md").read_text()
        self.assertIn("da", dec)
        self.assertIn("dd", dec)


class RegenTests(TrainBase):
    def test_regen_order_is_fixed_and_cites_nothing(self):
        p = self.train("regen")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        log = [l.split()[0] + " " + (l.split()[1] if len(l.split()) > 1 else "") for l in self.stub_log()]
        self.assertEqual(log, ["world ", "ledger --write", "harness_check --write-stubs",
                               "keystone_emit --write-manifest", "resource_contract --write"])
        subj = sh(self.work, "git", "log", "-1", "--format=%s").stdout
        self.assertTrue(subj.startswith("Regenerate train 1"), subj)

    def test_regen_commits_the_resource_contract_block(self):
        p = self.train("regen", extra_env={"STUB_CONTRACT": "1"})
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual(sh(self.work, "git", "status", "--porcelain").stdout.strip(), "")
        self.assertIn("docs/resource-contract.md",
                      sh(self.work, "git", "show", "--name-only", "--format=", "HEAD").stdout.split())

    def test_regen_refuses_a_cite(self):
        p = self.train("regen", "--cite", "certify-x")
        self.assertNotEqual(p.returncode, 0)
        self.assertEqual(self.stub_log(), [])

    def test_regen_failure_stops_the_train(self):
        p = self.train("regen", extra_env={"STUB_RC_ledger_write": "1"})
        self.assertNotEqual(p.returncode, 0)
        subj = sh(self.work, "git", "log", "-1", "--format=%s").stdout
        self.assertFalse(subj.startswith("Regenerate"), subj)


class PushTests(TrainBase):
    def ready(self):
        sha = self.lane("a", {"other.txt": "ok\n"})
        self.assertEqual(self.train("merge", f"a@{sha}").returncode, 0)
        return sha

    def test_push_refused_when_gate_failed(self):
        self.ready()
        before = self.origin_rev("dev")
        g = self.train("gate", extra_env={"STUB_RC_ledger_check": "1"})
        self.assertNotEqual(g.returncode, 0)
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0, p.stdout)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_push_refused_when_main_last_check_fails(self):
        # a misplaced __main__ block reached dev once through a piped gate
        self.ready()
        before = self.origin_rev("dev")
        g = self.train("gate", extra_env={"STUB_RC_main_last_check_": "1"})
        self.assertNotEqual(g.returncode, 0)
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0, p.stdout)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_push_refused_without_gating(self):
        self.ready()
        before = self.origin_rev("dev")
        self.assertNotEqual(self.train("push").returncode, 0)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_push_refused_when_head_moved_after_gating(self):
        self.ready()
        self.assertEqual(self.train("gate").returncode, 0)
        (self.work / "late.txt").write_text("x\n")
        self.commit(self.work, "late commit")
        before = self.origin_rev("dev")
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0, p.stdout)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_push_allowed_when_all_gates_pass_at_head(self):
        sha = self.ready()
        g = self.train("gate")
        self.assertEqual(g.returncode, 0, g.stdout + g.stderr)
        p = self.train("push")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual(self.origin_rev("dev"), self.head())
        self.assertEqual(self.origin_rev("integrate/t1"), self.head())
        self.assertIn(f"carried: a@{sha[:9]}", p.stdout)
        self.assertIn("verdict: green: the known-red baseline is empty", p.stdout)
        self.assertIn(f"STATE: dev = {self.head()[:9]} (integrate/t1): carries a@{sha[:9]}; green", p.stdout)
        self.assertIn("census: not run at HEAD", p.stdout)

    def test_push_renames_the_landed_lanes_readies_and_names_them_in_the_state_line(self):
        sha = self.ready()
        ready = self.tmp / "ready"
        ready.mkdir()
        (ready / "a.md").write_text("# READY: lane/a\n")
        (ready / "a-landing.md").write_text(f"# READY (landing): lane/a @ {sha[:9]}\n")
        # lane/ab at a sha HEAD does not contain: not lane a's, not landed
        (ready / "ab.md").write_text("# READY: lane/ab @ 0123456789ab\n")
        (ready / "landed-old.md").write_text("# READY: lane/a\n")
        env = {"FN_READY_DIR": str(ready)}
        self.assertEqual(self.train("gate", extra_env=env).returncode, 0)
        p = self.train("push", "--label", "9", extra_env=env)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual(sorted(f.name for f in ready.iterdir()),
                         ["ab.md", "landed-a-landing.md", "landed-a.md", "landed-old.md"])
        self.assertIn(f"STATE: dev = {self.head()[:9]} (train 9): carries a@{sha[:9]}", p.stdout)
        self.assertIn("READY landed: landed-a-landing.md, landed-a.md", p.stdout)

    def test_push_renames_the_readies_of_lanes_stacked_inside_a_carried_one(self):
        # train 85: b-host-85 carried d-cost-rows, whose READY names its own
        # lane and sha; that sha is in HEAD, so its READY has landed too
        inner = self.lane("s", {"stacked.txt": "s\n"})
        sha = self.lane("a", {"other.txt": "ok\n"}, base=inner)
        self.assertEqual(self.train("merge", f"a@{sha}").returncode, 0)
        ready = self.tmp / "ready"
        ready.mkdir()
        (ready / "s.md").write_text(f"# READY: lane/s @ {inner[:9]} (stacked)\n")
        (ready / "m.md").write_text(f"# READY (landing): memory (lane/s {inner[:9]})\n")
        (ready / "x.md").write_text("# READY: lane/x @ 0123456789ab\n")
        (ready / "packet.md").write_text("# Statements: no lane named\n")
        env = {"FN_READY_DIR": str(ready)}
        self.assertEqual(self.train("gate", extra_env=env).returncode, 0)
        p = self.train("push", "--label", "9", extra_env=env)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual(sorted(f.name for f in ready.iterdir()),
                         ["landed-m.md", "landed-s.md", "packet.md", "x.md"])
        self.assertIn("READY landed: landed-m.md, landed-s.md", p.stdout)

    def test_push_refused_when_dev_moved_after_gating(self):
        self.ready()
        self.assertEqual(self.train("gate").returncode, 0)
        self.advance_dev({"elsewhere.txt": "x\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "--no-edit", "origin/dev")
        self.assertEqual(self.train("gate").returncode, 0)
        before = self.origin_rev("dev")
        # a gate record of the earlier dev, at the same HEAD
        path = self.work / "build/train/integrate__t1.json"
        st = json.loads(path.read_text())
        st["gates"]["ledger"]["dev"] = "0" * 40
        path.write_text(json.dumps(st))
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0, p.stdout)
        self.assertIn("re-run gate", p.stdout)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_a_train_stacked_on_an_unlanded_train_waits_for_it(self):
        first = self.ready()
        sh(self.work, "git", "checkout", "-q", "-b", "integrate/t2")
        sha = self.lane("b", {"b.txt": "b\n"})
        self.assertEqual(self.train("merge", f"b@{sha}").returncode, 0)
        self.assertEqual(self.train("gate").returncode, 0)
        before = self.origin_rev("dev")
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0, p.stdout)
        self.assertIn("HEAD carries integrate/t1's merges", p.stdout)
        self.assertEqual(self.origin_rev("dev"), before)
        # once t1 lands, t2 re-gates and pushes
        sh(self.work, "git", "checkout", "-q", "integrate/t1")
        self.assertEqual(self.train("gate").returncode, 0)
        self.assertEqual(self.train("push").returncode, 0)
        sh(self.work, "git", "checkout", "-q", "integrate/t2")
        self.assertEqual(self.train("gate").returncode, 0)
        p = self.train("push")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual(self.origin_rev("dev"), self.head())
        self.assertIn(f"carried: b@{sha[:9]}", p.stdout)
        self.assertNotIn(first[:9], p.stdout.split("carried:")[1].splitlines()[0])

    def test_a_train_formed_on_a_fungus_branch_is_not_stacked(self):
        # the Fungus seat merges lanes into lane/fungus-*; the train branches
        # from it, so those merges sit on the train's first-parent line
        # (the work tree's integrate/t1 starts at dev and takes the Fungus
        # merge first, as a train branched from lane/fungus-x does)
        sha = self.lane("f", {"f.txt": "f\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "--no-ff", "-m", f"Merge lane/f @{sha[:9]} into lane/fungus-x", sha)
        b = self.lane("b", {"b.txt": "b\n"})
        self.assertEqual(self.train("merge", f"b@{b}").returncode, 0)
        self.assertEqual(self.train("gate").returncode, 0)
        p = self.train("push")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual(self.origin_rev("dev"), self.head())

    # ruling 21: the lock gate's table.  The only green is "no key added
    # relative to dev"; dev's own keys are an owned red list; a checker that
    # breaks its exit/JSON contract is a failure, never an empty set.
    def lock_gate(self, dev_keys, head_keys, items=None):
        files = {"lockkeys.json": json.dumps(dev_keys) + "\n", "src.txt": "lock gate dev\n"}
        idir = self.seed / "planning/repair/items"
        idir.mkdir(parents=True, exist_ok=True)
        for name, body in (items or {}).items():
            files["planning/repair/items/%s.json" % name] = json.dumps(body)
        self.advance_dev(files)
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "checkout", "-q", "-B", "integrate/t1", "origin/dev")
        if head_keys is not None:
            (self.work / "lockkeys.json").write_text(json.dumps(head_keys) + "\n")
            self.commit(self.work, "head lock keys")
        g = self.train("gate")
        st = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        return g, st["gates"]["lock_delta"]

    def item(self, key, state="open", owner="deputy-C"):
        return {"id": "LOCK-X", "state": state, "owner": owner, "detail": "key " + key + " here"}

    def test_lock_no_keys_is_green(self):
        g, rec = self.lock_gate([], None)
        self.assertEqual(rec["rc"], 0, g.stdout)

    def test_lock_key_added_by_train_fails_by_default(self):
        g, rec = self.lock_gate([], ["k1"])
        self.assertEqual(rec["rc"], 1)
        self.assertEqual(rec["added"], ["k1"])
        self.assertIn("NEW lock key added by this train: k1", g.stdout)
        self.assertNotEqual(g.returncode, 0)

    def test_lock_dev_key_owned_by_open_item_is_recorded_red_not_failure(self):
        g, rec = self.lock_gate(["R2|f|O:x"], None, {"LOCK-X": self.item("R2|f|O:x")})
        self.assertEqual(rec["rc"], 0, g.stdout)
        self.assertEqual(rec["owned_reds"], [{"key": "R2|f|O:x", "items": [
            {"item": "LOCK-X", "owner": "deputy-C", "state": "open"}]}])

    def test_lock_key_after_a_newline_in_item_text_is_owned(self):
        body = {"id": "LOCK-X", "state": "open", "owner": "deputy-C",
                "detail": "list:\nR7|f|swallow:x (f.lisp:1): why"}
        g, rec = self.lock_gate(["R7|f|swallow:x"], None, {"LOCK-X": body})
        self.assertEqual(rec["rc"], 0, g.stdout)
        self.assertEqual(rec["unowned"], [])

    def test_lock_dev_key_without_item_fails(self):
        g, rec = self.lock_gate(["R2|f|O:x"], None)
        self.assertEqual(rec["rc"], 1)
        self.assertEqual(rec["unowned"], ["R2|f|O:x"])

    def test_lock_item_naming_a_longer_key_does_not_own(self):
        g, rec = self.lock_gate(["R2|f|O:x"], None, {"LOCK-X": self.item("R2|f|O:x-y")})
        self.assertEqual(rec["unowned"], ["R2|f|O:x"])
        self.assertEqual(rec["rc"], 1)

    def test_lock_key_persisting_past_its_closed_item_fails(self):
        g, rec = self.lock_gate(["k1"], None, {"LOCK-X": self.item("k1", state="landed")})
        self.assertEqual(rec["rc"], 1)
        self.assertEqual(rec["closed_items"], ["k1"])

    def test_lock_train_removing_a_key_is_green(self):
        g, rec = self.lock_gate(["k1"], [], {"LOCK-X": self.item("k1")})
        self.assertEqual(rec["rc"], 0, g.stdout)
        self.assertEqual(rec["gone"], ["k1"])

    def assert_contract_failure(self, broken, dev_side=False):
        g, rec = self.lock_gate(broken if dev_side else [], None if dev_side else broken)
        self.assertEqual(rec["rc"], 1, g.stdout)
        self.assertIn("contract", rec["error"])
        self.assertNotEqual(g.returncode, 0)
        return rec

    def test_lock_exit_2_with_empty_object_fails(self):
        rec = self.assert_contract_failure({"raw": "{}", "rc": 2})
        self.assertEqual(rec["head_error"], "exit status 2")

    def test_lock_killed_child_with_empty_new_fails(self):
        rec = self.assert_contract_failure({"raw": '{"new": [], "stale": [], "findings": []}', "signal": True})
        self.assertTrue(rec["head_error"].startswith("exit status -"), rec)

    def test_lock_exit_0_with_empty_object_fails(self):
        rec = self.assert_contract_failure({"raw": "{}", "rc": 0})
        self.assertEqual(rec["head_error"], "missing field 'new'")

    def test_lock_missing_findings_field_fails(self):
        rec = self.assert_contract_failure({"raw": '{"new": [], "stale": []}'})
        self.assertEqual(rec["head_error"], "missing field 'findings'")

    def test_lock_mistyped_new_fails(self):
        rec = self.assert_contract_failure({"raw": '{"new": {}, "stale": [], "findings": []}'})
        self.assertEqual(rec["head_error"], "field 'new' is not a list")

    def test_lock_malformed_new_entry_fails(self):
        rec = self.assert_contract_failure({"raw": '{"new": [{"rule": "R2"}], "stale": [], "findings": []}'})
        self.assertTrue(rec["head_error"].startswith("malformed entry"), rec)

    def test_lock_unparseable_output_fails(self):
        rec = self.assert_contract_failure({"raw": "Traceback ..."})
        self.assertEqual(rec["head_error"], "output is not JSON")

    def test_lock_contract_failure_on_dev_side_fails(self):
        rec = self.assert_contract_failure({"raw": "{}", "rc": 2}, dev_side=True)
        self.assertEqual(rec["dev_error"], "exit status 2")

    def test_host_load_runs_only_when_host_changed(self):
        self.ready()
        self.train("gate")
        self.assertNotIn("host_check --load", self.stub_log())
        (self.work / "host").mkdir()
        (self.work / "host/x.c").write_text("x\n")
        self.commit(self.work, "host change")
        self.train("gate")
        self.assertIn("host_check --load", self.stub_log())

    def test_push_refused_when_a_unit_suite_fails(self):
        # train 36: `gate; push` pushed two test_ledger reds; the suites are gates now
        self.ready()
        before = self.origin_rev("dev")
        g = self.train("gate", extra_env={"STUB_RC_test_ledger_": "1"})
        self.assertNotEqual(g.returncode, 0, g.stdout)
        self.assertIn("unit=1", g.stdout)
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0, p.stdout)
        self.assertIn("gate unit failed", p.stdout + p.stderr)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_unit_runs_the_fixed_suites_and_the_tests_of_changed_tools(self):
        self.ready()
        self.train("gate")
        log = self.stub_log()
        for name in ("test_ledger", "test_keystone_emit", "test_keystone_critical", "test_train", "test_farm"):
            self.assertIn(name + " ", log)
        self.assertNotIn("test_current_view ", log)
        (self.work / "tools/current_view.py").write_text(STUB + "# changed\n")
        self.commit(self.work, "tool change")
        self.log.unlink()
        self.train("gate")
        self.assertIn("test_current_view ", self.stub_log())

    def test_native_suites_are_left_to_the_native_gate(self):
        root = Path(tempfile.mkdtemp(prefix="train-unit-"))
        self.addCleanup(shutil.rmtree, root, True)
        (root / "tests").mkdir()
        for name in ("test_native_x.py", "test_y.py", "test_z.py"):
            (root / "tests" / name).write_text("")
        got = train.unit_tests(root, ["tests/test_native_x.py", "tests/test_y.py",
                                      "tools/z.py", "tools/absent.py", "books/b.lisp"])
        self.assertEqual(got, list(train.UNIT_TESTS) + ["tests/test_y.py", "tests/test_z.py"])

    def test_suites_that_start_the_native_image_are_left_to_the_native_gate(self):
        root = Path(tempfile.mkdtemp(prefix="train-unit-"))
        self.addCleanup(shutil.rmtree, root, True)
        (root / "tests").mkdir()
        (root / "tests" / "test_bp_x_native.py").write_text(
            "import unittest\nfrom tests.native_harness import (\n    Node,\n)\n")
        (root / "tests" / "test_plain_native.py").write_text(
            "import unittest\n# mentions native_harness in a comment only\n")
        got = train.unit_tests(root, ["tests/test_bp_x_native.py", "tests/test_plain_native.py"])
        self.assertEqual(got, list(train.UNIT_TESTS) + ["tests/test_plain_native.py"])

    def test_a_missing_fixed_suite_fails_the_gate(self):
        self.ready()
        (self.work / "tests/test_farm.py").unlink()
        self.commit(self.work, "drops a suite")
        g = self.train("gate")
        self.assertNotEqual(g.returncode, 0, g.stdout)
        self.assertIn("unit: tests/test_farm.py is missing", g.stdout)

    def test_push_refused_when_the_teeth_gate_fails(self):
        self.ready()
        before = self.origin_rev("dev")
        g = self.train("gate", extra_env={"STUB_RC_keystone_emit_check": "1"})
        self.assertNotEqual(g.returncode, 0, g.stdout)
        self.assertIn("keystone=1", g.stdout)
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0, p.stdout)
        self.assertIn("gate keystone failed", p.stdout + p.stderr)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_push_refused_when_ascii_failed(self):
        self.ready()
        self.assertEqual(self.train("gate").returncode, 0)
        path = next((self.work / "build/train").glob("integrate__*.json"))
        st = json.loads(path.read_text())
        st["gates"]["ascii"]["rc"] = 1
        path.write_text(json.dumps(st))
        before = self.origin_rev("dev")
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0, p.stdout)
        self.assertIn("gate ascii failed", p.stdout + p.stderr)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_secrets_failure_blocks(self):
        self.ready()
        g = self.train("gate", extra_env={"STUB_RC_secrets_check_other.txt": "1"})
        # stub keys rc on the first arg (the file name) via mode
        self.assertNotEqual(g.returncode, 0, g.stdout)


class BoxStepTests(TrainBase):
    """The box_step gate (coordinator ruling 2026-10-07): ran at HEAD, or
    inherited when nothing under books/, specs/ or tests/acl2/ changed since
    the recorded box step and the local checks are 0."""

    def merge(self, files):
        sha = self.lane("a", files)
        self.assertEqual(self.train("merge", f"a@{sha}").returncode, 0)

    def box(self):
        return json.loads((self.work / "build/train/box-step.json").read_text())

    def test_inherits_when_no_box_paths_changed_and_names_the_sha(self):
        self.merge({"tools/x.py": "x\n"})
        g = self.train("gate")
        self.assertEqual(g.returncode, 0, g.stdout)
        st = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        self.assertEqual(st["gates"]["box_step"]["inherits_from"], self.box()["sha"])
        for check in ("interface_emit --check", "world --check", "host_check --build-lists", "host_check --read",
                      "host_check --world"):
            self.assertIn(check, " | ".join(self.stub_log()))
        p = self.train("push")
        self.assertEqual(p.returncode, 0, p.stdout)
        self.assertIn("box step: inherited from " + self.box()["sha"][:9], p.stdout)

    def test_refuses_when_books_changed_since_the_box_step(self):
        for path in ("books/b.lisp", "specs/s.md", "tests/acl2/t.lisp"):
            with self.subTest(path=path):
                self.setUp()
                (self.seed / Path(path).parent).mkdir(parents=True, exist_ok=True)
                self.merge({path: "changed\n"})
                g = self.train("gate")
                self.assertNotEqual(g.returncode, 0, g.stdout)
                self.assertIn("run `train.py boxstep BOX`", g.stdout)
                self.assertNotEqual(self.train("push").returncode, 0)

    def test_refuses_when_a_local_check_fails(self):
        self.merge({"tools/x.py": "x\n"})
        g = self.train("gate", extra_env={"STUB_RC_host_check_world": "1"})
        self.assertNotEqual(g.returncode, 0, g.stdout)

    def test_refuses_without_a_record(self):
        (self.work / "build/train/box-step.json").unlink()
        self.merge({"tools/x.py": "x\n"})
        self.assertNotEqual(self.train("gate").returncode, 0)

    def test_boxstep_fetches_the_emits_into_build_box_uncommitted_then_the_gate_passes_at_head(self):
        (self.seed / "books").mkdir(exist_ok=True)
        self.merge({"books/b.lisp": "changed\n"})
        self.assertNotEqual(self.train("gate").returncode, 0)
        before = self.head()
        b = self.train("boxstep", "persvati", extra_env={"STUB_EMIT": "emitted"})
        self.assertEqual(b.returncode, 0, b.stdout + b.stderr)
        self.assertEqual(self.head(), before, "the box step commits nothing")
        self.assertEqual(self.box()["sha"], before)
        self.assertEqual((self.work / "build/box/wire-grammar.json").read_text(), "emitted\n")
        self.assertFalse((self.work / "build/box/interfaces.json").exists())
        self.assertFalse((self.work / "planning/interfaces.json").exists())
        stamp = json.loads((self.work / "build/box/stamp.json").read_text())
        self.assertEqual((stamp["sha"], stamp["box"]), (before, "persvati"))
        log = " | ".join(self.stub_log())
        self.assertIn("--fetch build/box/wire-grammar.json", log)
        # the certified world's witness runs in the box step, required
        self.assertIn("books/wire-export books/image-world books/image-world-dtn", log)
        self.assertIn("FN_CERT_WORLD_REQUIRED=1 python3 -m unittest tests.test_cert_world_checks", log)
        self.assertNotIn("interfaces.json", log)
        self.assertIn("remote_check persvati", " | ".join(self.stub_log()))
        g = self.train("gate")
        self.assertEqual(g.returncode, 0, g.stdout)
        self.assertIn("ran at HEAD on persvati", g.stdout)

    def test_two_branches_alternating_in_one_tree_keep_their_own_box_steps(self):
        (self.seed / "books").mkdir(exist_ok=True)
        (self.seed / "specs").mkdir(exist_ok=True)
        self.merge({"books/b.lisp": "first\n"})
        self.assertEqual(self.train("boxstep", "persvati").returncode, 0)
        first = self.head()
        sh(self.work, "git", "checkout", "-q", "-b", "integrate/t2", "origin/dev")
        sha = self.lane("c", {"specs/c.md": "second\n"})
        self.assertEqual(self.train("merge", f"c@{sha}").returncode, 0)
        self.assertEqual(self.train("boxstep", "persvati").returncode, 0)
        self.assertEqual(self.box()["sha"], self.head(), "the tree's latest box step is t2's")
        sh(self.work, "git", "checkout", "-q", "integrate/t1")
        self.assertEqual(self.head(), first)
        g = self.train("gate")
        self.assertEqual(g.returncode, 0, g.stdout)
        self.assertIn("ran at HEAD on persvati", g.stdout)

    def test_failed_boxstep_records_nothing(self):
        before = self.box()
        self.merge({"tools/x.py": "x\n"})
        b = self.train("boxstep", "hbox", extra_env={"STUB_RC_remote_check": "3"})
        self.assertNotEqual(b.returncode, 0)
        self.assertEqual(self.box(), before)


class CertWorldWitnessTests(unittest.TestCase):
    def test_the_witness_fails_rather_than_skips_where_the_box_step_requires_it(self):
        env = {k: v for k, v in os.environ.items() if k != "FN_ACL2"}
        skipped = subprocess.run([sys.executable, "-m", "unittest", "tests.test_cert_world_checks"],
                                 cwd=REPO, capture_output=True, text=True, env=env, timeout=120)
        self.assertEqual(skipped.returncode, 0, skipped.stderr)
        self.assertIn("skipped", skipped.stderr)
        required = subprocess.run([sys.executable, "-m", "unittest", "tests.test_cert_world_checks"],
                                  cwd=REPO, capture_output=True, text=True, timeout=120,
                                  env=dict(env, FN_CERT_WORLD_REQUIRED="1"))
        self.assertNotEqual(required.returncode, 0, required.stderr)
        self.assertIn("FN_CERT_WORLD_REQUIRED and no ACL2 launcher", required.stderr)


class CertifyTests(TrainBase):
    """`train.py certify BOX`: one farm run, then the emits in that run's tree."""

    def setUp(self):
        super().setUp()
        self.ftree = self.tmp / "farm-tree"
        self.ftree.mkdir()
        (self.seed / "tools/farm.py").write_text(FARM_STUB)
        self.commit(self.seed, "farm stub")
        sh(self.seed, "git", "push", "-q", "origin", "HEAD:dev")
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "--ff-only", "origin/dev")
        # the regen step's manifest (keystone_emit --write-manifest), uncommitted
        (self.work / "build/teeth-obligations.json").write_text('{"entries": []}\n')
        ssh = self.tmp / "ssh-stub"
        ssh.write_text(SSH_STUB)
        ssh.chmod(0o755)
        self.env.update(TRAIN_SSH=str(ssh), FARM_TREE=str(self.ftree))

    def merge(self, files):
        sha = self.lane("a", files)
        self.assertEqual(self.train("merge", f"a@{sha}").returncode, 0)

    def box(self):
        return json.loads((self.work / "build/train/box-step.json").read_text())

    def books_train(self):
        (self.seed / "books").mkdir(exist_ok=True)
        (self.seed / "tests/acl2").mkdir(parents=True, exist_ok=True)
        self.merge({"books/b.lisp": "changed\n", "tests/acl2/t.lisp": "t\n"})

    def test_certify_is_one_run_with_wire_export_and_the_affected_by_words(self):
        self.books_train()
        c = self.train("certify", "hbox")
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)
        farm = [l for l in self.stub_log() if l.startswith("farm ")]
        self.assertEqual(len(farm), 2, farm)
        sub = farm[0]
        for word in ("--affected-by books/b", "--affected-by tests/acl2/t", "--timeout-seconds 1800",
                     "submit hbox", "books/wire-export", "books/image-world", "books/image-world-dtn",
                     "books/b", "tests/acl2/t"):
            self.assertIn(word, sub)
        # the affected closure, never the lane selection (direct includers)
        self.assertNotIn("--lane", sub.split())
        self.assertNotIn("books/b.lisp", sub)
        self.assertTrue(farm[1].startswith("farm --root") or "wait hbox run-stub-1" in farm[1], farm[1])
        self.assertNotIn("remote_check", " ".join(self.stub_log()))

    def test_certify_test_only_change_selects_its_includers(self):
        from tools import certs

        (self.seed / "tests/acl2").mkdir(parents=True, exist_ok=True)
        self.advance_dev({
            "Makefile": "ACL2_BOOKS = tests/acl2/base-tests tests/acl2/consumer-tests\n",
            "tests/acl2/base-tests.lisp": '(in-package "ACL2")\n',
            "tests/acl2/consumer-tests.lisp": '(include-book "base-tests")\n',
        })
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "--ff-only", "origin/dev")
        self.merge({"tests/acl2/base-tests.lisp": '(in-package "ACL2")\n; changed\n'})
        self.assertIn("tests/acl2/base-tests", certs.closure(self.work, "tests/acl2/consumer-tests"))
        result = self.train("certify", "hbox")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        submit = next(line for line in self.stub_log() if line.startswith("farm "))
        self.assertEqual(shlex.split(submit), [
            "farm", "--affected-by", "tests/acl2/base-tests", "--timeout-seconds", "1800",
            "submit", "hbox", *train.BOX_CERT_BOOKS, "tests/acl2/base-tests"])

    def test_certify_books_only_command_is_unchanged(self):
        (self.seed / "books").mkdir(exist_ok=True)
        self.merge({"books/b.lisp": '(in-package "ACL2")\n'})
        result = self.train("certify", "hbox")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        submit = next(line for line in self.stub_log() if line.startswith("farm "))
        self.assertEqual(shlex.split(submit), [
            "farm", "--affected-by", "books/b", "--timeout-seconds", "1800",
            "submit", "hbox", *train.BOX_CERT_BOOKS, "books/b"])

    def host_book_train(self, book="host/owner-host", listed=False, changes=None):
        (self.seed / "books").mkdir(exist_ok=True)
        (self.seed / book).parent.mkdir(parents=True, exist_ok=True)
        (self.seed / "host/native").mkdir(parents=True, exist_ok=True)
        self.advance_dev({
            "Makefile": "ACL2_BOOKS = books/consumer" + (" " + book if listed else "") + "\n",
            "books/consumer.lisp": f'(include-book "../{book}")\n',
            book + ".lisp": '(in-package "ACL2")\n',
            "host/unreferenced.lisp": '(in-package "ACL2")\n',
            "host/native/io.lisp": '(in-package "CL-USER")\n',
        })
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "--ff-only", "origin/dev")
        self.merge(changes if changes is not None else {
            book + ".lisp": '(in-package "ACL2")\n; changed\n'})
        result = self.train("certify", "hbox")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        submit = next(line for line in self.stub_log() if line.startswith("farm "))
        return shlex.split(submit)

    def test_certify_host_dependency_change_selects_its_includers(self):
        self.assertEqual(self.host_book_train(), [
            "farm", "--affected-by", "host/owner-host", "--timeout-seconds", "1800",
            "submit", "hbox", *train.BOX_CERT_BOOKS])

    def test_certify_changed_host_makefile_root_is_also_named(self):
        self.assertEqual(self.host_book_train(listed=True), [
            "farm", "--affected-by", "host/owner-host", "--timeout-seconds", "1800",
            "submit", "hbox", *train.BOX_CERT_BOOKS, "host/owner-host"])

    def test_certify_nested_host_book_in_makefile_closure_is_selected(self):
        self.assertEqual(self.host_book_train(book="host/library/adapter"), [
            "farm", "--affected-by", "host/library/adapter", "--timeout-seconds", "1800",
            "submit", "hbox", *train.BOX_CERT_BOOKS])

    def test_certify_raw_native_and_unreferenced_host_changes_add_nothing(self):
        self.assertEqual(self.host_book_train(changes={
            "host/native/io.lisp": '(in-package "CL-USER")\n; changed\n',
            "host/unreferenced.lisp": '(in-package "ACL2")\n; changed\n',
        }), ["farm", "--timeout-seconds", "1800", "submit", "hbox", *train.BOX_CERT_BOOKS])

    def test_certify_has_no_lane_mode_to_choose(self):
        self.books_train()
        result = self.train("certify", "hbox", "--transitive")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual([line for line in self.stub_log() if line.startswith("farm ")], [])

    def known(self, *subjects, kind="certify", state="open"):
        """Commit known-red rows for SUBJECTS, owned by item KR-X in STATE, on dev."""
        rows = [{"kind": kind, "subject": b, "item": "KR-X", "owner": "builder-B",
                 "evidence": "measured"} for b in subjects]
        self.advance_dev({"planning/known-reds.json": json.dumps({"rows": rows}),
                          "planning/repair/items/KR-X.json": json.dumps({"id": "KR-X", "state": state})})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "--no-edit", "origin/dev")

    def test_a_certify_whose_failures_are_all_known_reds_goes_on_and_records_them(self):
        (self.seed / "planning/repair/items").mkdir(parents=True, exist_ok=True)
        self.known("host/far-a", "books/far-b")
        self.books_train()
        c = self.train("certify", "hbox", extra_env={"STUB_RC_farm_wait": "1",
                                                     "STUB_FAILED_BOOKS": "host/far-a,books/far-b"})
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)
        self.assertIn("every one a known red", c.stdout)
        self.assertEqual(self.box()["known_reds_seen"], ["books/far-b", "host/far-a"])
        self.assertEqual(len([l for l in self.stub_log() if l.startswith("ssh ")]), 1)

    def test_a_certify_failure_outside_the_known_reds_records_nothing(self):
        (self.seed / "planning/repair/items").mkdir(parents=True, exist_ok=True)
        self.known("host/far-a")
        self.books_train()
        before = self.box()
        c = self.train("certify", "hbox", extra_env={"STUB_RC_farm_wait": "1",
                                                     "STUB_FAILED_BOOKS": "host/far-a,books/b"})
        self.assertNotEqual(c.returncode, 0)
        self.assertIn("NEW certify red (not in planning/known-reds.json): books/b", c.stdout)
        self.assertEqual(self.box(), before)
        self.assertEqual([l for l in self.stub_log() if l.startswith("ssh ")], [])

    def test_a_killed_known_red_book_has_no_verdict_and_records_nothing(self):
        (self.seed / "planning/repair/items").mkdir(parents=True, exist_ok=True)
        self.known("host/far-a")
        self.books_train()
        before = self.box()
        c = self.train("certify", "hbox", extra_env={"STUB_RC_farm_wait": "1",
                                                     "STUB_KILLED_BOOKS": "host/far-a"})
        self.assertNotEqual(c.returncode, 0)
        self.assertIn("KILLED (no verdict): host/far-a", c.stdout)
        self.assertEqual(self.box(), before)

    def test_a_certify_row_of_another_kind_does_not_excuse_a_book(self):
        (self.seed / "planning/repair/items").mkdir(parents=True, exist_ok=True)
        self.known("host/far-a", kind="native")
        self.books_train()
        c = self.train("certify", "hbox", extra_env={"STUB_RC_farm_wait": "1",
                                                     "STUB_FAILED_BOOKS": "host/far-a"})
        self.assertNotEqual(c.returncode, 0)

    def test_certify_always_adds_critical_witnesses_of_transitively_affected_books(self):
        (self.seed / "books").mkdir(exist_ok=True)
        (self.seed / "tests/acl2").mkdir(parents=True, exist_ok=True)
        critical = {"critical": "durability", "book": "books/theorem.lisp",
                    "owner_book": "tests/acl2/special-witness.lisp"}
        entries = [critical, dict(critical, name="another-theorem"),
                   dict(critical, book="books/unrelated.lisp",
                        owner_book="tests/acl2/unrelated-witness.lisp"),
                   dict(critical, critical=None,
                        owner_book="tests/acl2/noncritical-witness.lisp")]
        self.advance_dev({
            "books/b.lisp": '(in-package "ACL2")\n',
            "books/middle.lisp": '(include-book "b")\n',
            "books/theorem.lisp": '(include-book "middle")\n',
            "books/unrelated.lisp": '(in-package "ACL2")\n',
            "tests/acl2/special-witness.lisp": '(include-book "../../books/theorem")\n',
            "tests/acl2/unrelated-witness.lisp": '(in-package "ACL2")\n',
            "tests/acl2/noncritical-witness.lisp": '(in-package "ACL2")\n',
        })
        (self.work / "build/teeth-obligations.json").write_text(json.dumps({"entries": entries}))
        sh(self.work, "git", "merge", "-q", "--ff-only", "origin/dev")
        self.merge({"books/b.lisp": '(in-package "ACL2")\n; changed\n'})
        result = self.train("certify", "hbox")  # witnesses ride the default lane mode too
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        submit = next(line for line in self.stub_log() if line.startswith("farm "))
        words = submit.split()
        self.assertNotIn("--jobs", words, "farm owns the fixed per-box default")
        self.assertNotIn("auto", words)
        self.assertNotIn("--force", words, "trains respect shared-box load admission")
        self.assertEqual(words.count("tests/acl2/special-witness"), 1)
        self.assertNotIn("tests/acl2/unrelated-witness", words)
        self.assertNotIn("tests/acl2/noncritical-witness", words)

    def test_certify_adds_a_critical_witness_whose_own_closure_changed(self):
        (self.seed / "books").mkdir(exist_ok=True)
        (self.seed / "tests/acl2").mkdir(parents=True, exist_ok=True)
        critical = {"critical": "durability", "book": "books/theorem.lisp",
                    "owner_book": "tests/acl2/special-witness.lisp"}
        entries = [critical,
                   dict(critical, book="books/unrelated.lisp",
                        owner_book="tests/acl2/unrelated-witness.lisp")]
        self.advance_dev({
            "books/b.lisp": '(in-package "ACL2")\n',
            "books/teeth.lisp": '(in-package "ACL2")\n',
            "books/theorem.lisp": '(include-book "b")\n',
            "books/unrelated.lisp": '(in-package "ACL2")\n',
            "tests/acl2/special-witness.lisp":
                '(include-book "../../books/theorem")\n(include-book "../../books/teeth")\n',
            "tests/acl2/unrelated-witness.lisp": '(in-package "ACL2")\n',
        })
        (self.work / "build/teeth-obligations.json").write_text(json.dumps({"entries": entries}))
        sh(self.work, "git", "merge", "-q", "--ff-only", "origin/dev")
        self.merge({"books/teeth.lisp": '(in-package "ACL2")\n; changed\n'})
        result = self.train("certify", "hbox")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        submit = next(line for line in self.stub_log() if line.startswith("farm "))
        words = submit.split()
        self.assertEqual(words.count("tests/acl2/special-witness"), 1)
        self.assertNotIn("tests/acl2/unrelated-witness", words)

    def test_certify_emits_in_the_run_tree_fetches_into_build_box_and_records_the_split(self):
        self.books_train()
        before = self.head()
        c = self.train("certify", "hbox")
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)
        ssh = [l for l in self.stub_log() if l.startswith("ssh ")]
        self.assertEqual(len(ssh), 1, ssh)
        for word in (str(self.ftree), "timeout", "swarm-build", "interface_emit.py --write --check",
                     "protocol_emit.py --wire --check", "host_check.py --world",
                     "FN_CERT_WORLD_REQUIRED=1 python3 -m unittest tests.test_cert_world_checks"):
            self.assertIn(word, ssh[0])
        self.assertNotIn("certify_books", ssh[0])
        self.assertEqual(self.head(), before, "the certify's emits are not committed")
        self.assertEqual((self.work / "build/box/wire-grammar.json").read_text(), "emitted\n")
        self.assertFalse((self.work / "planning/interfaces.json").exists())
        self.assertEqual(json.loads((self.work / "build/box/stamp.json").read_text())["sha"], before)
        rec = self.box()
        self.assertEqual(rec["sha"], self.head())
        self.assertEqual((rec["box"], rec["run"], rec["certify_id"]), ("hbox", "run-stub-1", "certify-stub-1"))
        self.assertEqual(set(rec["wall"]), {"install", "certify", "emit", "total", "emit_steps"})
        st = json.loads(self.work.joinpath("build/train/integrate__t1.json").read_text())
        self.assertEqual(st["box_wall"], rec["wall"])
        self.assertIsNone(rec["cache_seed"])
        self.assertIsNone(st["cache_seed"])
        g = self.train("gate")
        self.assertIn("ran at HEAD on hbox", g.stdout)
        s = self.train("status")
        self.assertIn("certify", s.stdout)

    def test_successful_seed_is_recorded_in_box_and_train_state(self):
        self.books_train()
        record = self.work / "build/farm/old-run.json"
        record.parent.mkdir(parents=True, exist_ok=True)
        record.write_text(json.dumps({"remote_path": "/old/farm-tree", "host": "hbox"}))
        (self.work / "build/train/box-step.json").write_text(json.dumps({"box": "hbox", "run": "old-run"}))
        result = self.train("certify", "hbox", extra_env={"STUB_CACHE_SEED": "old-run"})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.box()["cache_seed"], "old-run")
        state = json.loads(self.work.joinpath("build/train/integrate__t1.json").read_text())
        self.assertEqual(state["cache_seed"], "old-run")
        ssh = [line for line in self.stub_log() if line.startswith("ssh ")]
        self.assertEqual(len(ssh), 1)
        self.assertLess(ssh[0].index("cp -a /old/farm-tree/build/cache/."),
                        ssh[0].index("tools/interface_emit.py"))

    def test_a_books_free_train_certifies_wire_export_and_the_world_alone(self):
        self.merge({"tools/x.py": "x\n"})
        c = self.train("certify", "hbox")
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)
        sub = [l for l in self.stub_log() if l.startswith("farm") and " submit " in l][0]
        self.assertNotIn("--lane", sub)
        self.assertNotIn("--affected-by", sub)
        self.assertTrue(sub.endswith("submit hbox books/wire-export books/image-world books/image-world-dtn"), sub)

    def test_failed_certify_records_nothing(self):
        self.books_train()
        before = self.box()
        c = self.train("certify", "hbox", extra_env={"STUB_RC_farm_wait": "1"})
        self.assertNotEqual(c.returncode, 0)
        self.assertEqual(self.box(), before)
        self.assertEqual([l for l in self.stub_log() if l.startswith("ssh ")], [])

    def test_failed_submit_records_nothing(self):
        self.books_train()
        before = self.box()
        c = self.train("certify", "hbox", extra_env={"STUB_RC_farm_submit": "2"})
        self.assertNotEqual(c.returncode, 0)
        self.assertEqual(self.box(), before)

    def test_failed_emit_records_nothing_and_commits_nothing(self):
        self.books_train()
        before, head = self.box(), self.head()
        c = self.train("certify", "hbox", extra_env={"STUB_RC_ssh": "1"})
        self.assertNotEqual(c.returncode, 0)
        self.assertEqual(self.box(), before)
        self.assertEqual(self.head(), head)

    def test_certify_refuses_a_dirty_tree(self):
        self.books_train()
        (self.work / "src.txt").write_text("edited\n")
        c = self.train("certify", "hbox")
        self.assertNotEqual(c.returncode, 0)
        self.assertEqual([l for l in self.stub_log() if l.startswith("farm")], [])

    def test_certify_refuses_an_untracked_file(self):
        # farm ships the worktree, so an untracked file would reach the box
        self.books_train()
        (self.work / "NOTES.txt").write_text("x\n")
        self.assertNotEqual(self.train("certify", "hbox").returncode, 0)
        self.assertEqual([l for l in self.stub_log() if l.startswith("farm")], [])



class BaselineGateTests(TrainBase):
    """The known-red baseline: rows shrink only, each owned by an open item."""

    def setUp(self):
        super().setUp()
        (self.seed / "planning/repair/items").mkdir(parents=True, exist_ok=True)

    def rows(self, *subjects, item="KR-X"):
        return json.dumps({"rows": [{"kind": "native", "subject": s, "item": item, "owner": "builder-B",
                                     "evidence": "gate log"} for s in subjects]}) + "\n"

    def on_dev(self, text, state="open"):
        self.advance_dev({"planning/known-reds.json": text,
                          "planning/repair/items/KR-X.json": json.dumps({"id": "KR-X", "state": state})})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "checkout", "-q", "-B", "integrate/t1", "origin/dev")

    def gate_with(self, text=None, item_state=None):
        if text is not None:
            (self.work / "planning/known-reds.json").write_text(text)
        if item_state is not None:
            (self.work / "planning/repair/items/KR-X.json").write_text(
                json.dumps({"id": "KR-X", "state": item_state}))
        if text is not None or item_state is not None:
            self.commit(self.work, "head baseline")
        g = self.train("gate")
        st = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        return g, st["gates"]["baseline"]

    def test_unchanged_owned_rows_pass_and_status_says_not_green(self):
        self.on_dev(self.rows("t.a", "t.b"))
        g, rec = self.gate_with()
        self.assertEqual(rec["rc"], 0, g.stdout)
        self.assertEqual(rec["rows"], 2)
        s = self.train("status")
        self.assertIn("non-regressing against 2 known reds, 0 amended", s.stdout)
        self.assertIn("NOT green", s.stdout)

    def test_a_removed_row_passes(self):
        self.on_dev(self.rows("t.a", "t.b"))
        g, rec = self.gate_with(self.rows("t.a"))
        self.assertEqual(rec["rc"], 0, g.stdout)
        self.assertEqual(rec["gone"], [["native", "t.b"]])

    def test_a_row_added_relative_to_dev_fails(self):
        self.on_dev(self.rows("t.a"))
        g, rec = self.gate_with(self.rows("t.a", "t.new"))
        self.assertEqual(rec["rc"], 1)
        self.assertEqual(rec["added"], [["native", "t.new"]])
        self.assertIn("rows shrink only", g.stdout)

    def test_the_first_baseline_is_established_when_dev_has_none(self):
        sh(self.seed, "git", "fetch", "-q", "origin")
        sh(self.seed, "git", "checkout", "-q", "-B", "devtip", "origin/dev")
        sh(self.seed, "git", "rm", "-q", "planning/known-reds.json")
        self.commit(self.seed, "no baseline")
        sh(self.seed, "git", "push", "-q", "origin", "HEAD:dev")
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "checkout", "-q", "-B", "integrate/t1", "origin/dev")
        (self.work / "planning/repair/items").mkdir(parents=True, exist_ok=True)
        g, rec = self.gate_with(self.rows("t.a"), item_state="open")
        self.assertEqual(rec["rc"], 0, g.stdout)
        self.assertTrue(rec["established"])

    def test_a_missing_baseline_at_head_fails(self):
        sh(self.work, "git", "rm", "-q", "planning/known-reds.json")
        self.commit(self.work, "drop baseline")
        g, rec = self.gate_with()
        self.assertEqual(rec["rc"], 1)

    def test_a_row_whose_item_is_missing_fails(self):
        self.on_dev(self.rows("t.a"))
        g, rec = self.gate_with(self.rows("t.a", item="KR-X") .replace("KR-X", "KR-NONE"))
        self.assertEqual(rec["rc"], 1)
        self.assertEqual(len(rec["unowned"]), 1)

    def test_a_row_whose_item_is_closed_fails(self):
        self.on_dev(self.rows("t.a"))
        g, rec = self.gate_with(item_state="landed")
        self.assertEqual(rec["rc"], 1)
        self.assertEqual(len(rec["closed_items"]), 1)

    def test_a_malformed_file_fails(self):
        self.on_dev(self.rows("t.a"))
        for text in ('{"rows": [{"kind": "native"}]}\n', '{"rows": {}}\n', "not json\n",
                     self.rows("t.a").replace('"native"', '"vibes"'),
                     json.dumps({"rows": json.loads(self.rows("t.a"))["rows"] * 2})):
            g, rec = self.gate_with(text)
            self.assertEqual(rec["rc"], 1, text)

    def test_push_refused_when_the_baseline_gate_fails(self):
        self.on_dev(self.rows("t.a"))
        before = self.origin_rev("dev")
        self.gate_with(self.rows("t.a", "t.new"))
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("gate baseline failed", p.stdout)
        self.assertEqual(self.origin_rev("dev"), before)

    def amendment(self, subject, item="KR-X", owner="builder-B"):
        return {"kind": "native", "subject": subject, "dev_sha": "abc123def", "item": item,
                "owner": owner, "ruling": "coordinator: test"}

    def amendments(self, *records):
        return json.dumps({"note": "append-only", "amendments": list(records)}) + "\n"

    def gate_amended(self, rows, amend):
        (self.work / "planning/known-reds-amendments.json").write_text(amend)
        return self.gate_with(rows)

    def test_an_unamended_addition_is_refused_with_the_usual_message(self):
        self.on_dev(self.rows("t.a"))
        g, rec = self.gate_amended(self.rows("t.a", "t.new"), self.amendments())
        self.assertEqual(rec["rc"], 1)
        self.assertEqual(rec["added"], [["native", "t.new"]])
        self.assertIn("known red ADDED by this train (rows shrink only): native t.new", g.stdout)

    def test_an_amended_addition_is_accepted_and_counted(self):
        self.on_dev(self.rows("t.a"))
        g, rec = self.gate_amended(self.rows("t.a", "t.new"), self.amendments(self.amendment("t.new")))
        self.assertEqual(rec["rc"], 0, g.stdout)
        self.assertEqual(rec["admitted"], [["native", "t.new"]])
        self.assertEqual((rec["rows"], rec["amended"]), (2, 1))

    def test_an_amendment_covers_only_the_row_it_names(self):
        self.on_dev(self.rows("t.a"))
        g, rec = self.gate_amended(self.rows("t.a", "t.new", "t.other"),
                                   self.amendments(self.amendment("t.new")))
        self.assertEqual(rec["rc"], 1)
        self.assertEqual(rec["added"], [["native", "t.other"]])

    def test_a_dangling_amendment_fails(self):
        self.on_dev(self.rows("t.a"))
        g, rec = self.gate_amended(self.rows("t.a"), self.amendments(self.amendment("t.stock")))
        self.assertEqual(rec["rc"], 1)
        self.assertEqual(rec["dangling_amendments"], ["native t.stock"])
        self.assertIn("amendments cannot be stockpiled", g.stdout)

    def test_an_amendment_of_a_retired_row_with_a_closed_item_is_history(self):
        self.on_dev(self.rows("t.a", "t.new"))
        (self.work / "planning/known-reds-amendments.json").write_text(
            self.amendments(self.amendment("t.new")))
        g, rec = self.gate_with(self.rows("t.a"))
        self.assertEqual(rec["rc"], 1, "item still open: the amendment dangles")
        g, rec = self.gate_with(self.rows("t.a"), item_state="landed")
        self.assertEqual(rec["dangling_amendments"], [])

    def test_a_rewritten_or_dropped_amendment_fails(self):
        self.on_dev(self.rows("t.a", "t.new"))
        self.advance_dev({"planning/known-reds-amendments.json": self.amendments(self.amendment("t.new"))})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "checkout", "-q", "-B", "integrate/t1", "origin/dev")
        g, rec = self.gate_amended(self.rows("t.a", "t.new"),
                                   self.amendments(self.amendment("t.new", owner="builder-B") | {"ruling": "edited"}))
        self.assertTrue(rec["amendments_rewritten"])
        self.assertEqual(rec["rc"], 1)
        g, rec = self.gate_amended(self.rows("t.a", "t.new"), self.amendments())
        self.assertTrue(rec["amendments_rewritten"])
        self.assertEqual(rec["rc"], 1)

    def test_an_amendment_disagreeing_with_its_row_fails(self):
        self.on_dev(self.rows("t.a"))
        g, rec = self.gate_amended(self.rows("t.a", "t.new"),
                                   self.amendments(self.amendment("t.new", owner="someone-else")))
        self.assertEqual(rec["mismatched_amendments"], ["native t.new"])
        self.assertEqual(rec["rc"], 1)

    def test_an_owner_transfer_appends_a_record_and_the_row_takes_the_new_owner(self):
        # coordinator 2026-10-09: the measured owner's record stays as written,
        # a later record names the owner it takes over from
        self.on_dev(self.rows("t.a", "t.new"))
        first = self.amendment("t.new")
        self.advance_dev({"planning/known-reds-amendments.json": self.amendments(first)})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "checkout", "-q", "-B", "integrate/t1", "origin/dev")
        moved = json.loads(self.rows("t.a", "t.new"))
        moved["rows"][1]["owner"] = "builder-M"
        transfer = dict(first, owner="builder-M", transfer_from=first["owner"], ruling="moved")
        g, rec = self.gate_amended(json.dumps(moved) + "\n", self.amendments(first, transfer))
        self.assertEqual(rec["rc"], 0, g.stdout)
        self.assertEqual((rec["rows"], rec["amended"], rec["mismatched_amendments"]), (2, 1, []))
        # without the transfer record the moved row disagrees with its amendment
        g, rec = self.gate_amended(json.dumps(moved) + "\n", self.amendments(first))
        self.assertEqual(rec["mismatched_amendments"], ["native t.new"])

    def test_a_second_record_that_is_not_a_proper_transfer_is_malformed(self):
        first = self.amendment("t.a")
        bad = [dict(first, owner="builder-M"),                                   # no transfer_from
               dict(first, owner="builder-M", transfer_from="someone-else"),     # wrong previous owner
               dict(first, transfer_from=first["owner"]),                        # same owner
               dict(first, owner="builder-M", transfer_from=first["owner"], item="OTHER"),
               dict(first, owner="builder-M", transfer_from=first["owner"], dev_sha="0000000")]
        for second in bad:
            with self.assertRaises(train.TrainError, msg=str(second)):
                train.parse_amendments(self.amendments(first, second))
        with self.assertRaises(train.TrainError):
            train.parse_amendments(self.amendments(dict(first, transfer_from="x")))
        ok = dict(first, owner="builder-M", transfer_from=first["owner"])
        self.assertEqual(len(train.parse_amendments(self.amendments(first, ok))), 2)

    def test_parser_accepts_refile_with_same_owner_and_measured_sha(self):
        first = self.amendment("t.a")
        second = dict(first, item="KR-TARGET", item_from="KR-X", ruling="re-file ruling")
        self.assertEqual(train.parse_amendments(self.amendments(first, second)), [first, second])

    def test_parser_refuses_invalid_refiles_and_transfer_changing_item(self):
        first = self.amendment("t.a")
        refile = dict(first, item="KR-TARGET", item_from="KR-X")
        bad = [dict(refile, owner="builder-M"), dict(refile, item_from="WRONG"),
               dict(refile, dev_sha="0000000"), dict(refile, item="KR-X"),
               dict(first, transfer_from="builder-B", owner="builder-M", item="KR-TARGET")]
        for second in bad:
            with self.subTest(record=second), self.assertRaises(train.TrainError):
                train.parse_amendments(self.amendments(first, second))
        with self.assertRaises(train.TrainError):
            train.parse_amendments(self.amendments(refile))

    def test_refile_gate_refuses_closed_missing_or_differently_owned_target(self):
        self.on_dev(self.rows("t.a"))
        first = self.amendment("t.new")
        refile = dict(first, item="KR-TARGET", item_from="KR-X")
        target = self.work / "planning/repair/items/KR-TARGET.json"
        rows = json.loads(self.rows("t.a", "t.new"))
        rows["rows"][1]["item"] = "KR-TARGET"
        for item, message in [(None, "missing"),
                              ({"state": "closed", "owner": "builder-B"}, "closed"),
                              ({"state": "open", "owner": "builder-M"}, "owner")]:
            with self.subTest(item=item):
                if item is not None:
                    target.write_text(json.dumps(item))
                g, rec = self.gate_amended(json.dumps(rows), self.amendments(first, refile))
                self.assertEqual(rec["rc"], 1, g.stdout)
                self.assertEqual(len(rec["invalid_refiles"]), 1)
                self.assertIn(message, rec["invalid_refiles"][0])
        target.write_text('{"state": "open", "owner": "builder-B"}\n')
        g, rec = self.gate_amended(json.dumps(rows), self.amendments(first, refile))
        self.assertEqual(rec["rc"], 0, g.stdout)

    def test_refile_gate_accepts_closed_umbrella_as_history(self):
        self.on_dev(self.rows("t.new"))
        first = self.amendment("t.new")
        refile = dict(first, item="KR-TARGET", item_from="KR-X")
        (self.work / "planning/repair/items/KR-TARGET.json").write_text(
            '{"state": "open", "owner": "builder-B"}\n')
        (self.work / "planning/repair/items/KR-X.json").write_text('{"state": "closed"}\n')
        g, rec = self.gate_amended(self.rows("t.new", item="KR-TARGET"), self.amendments(first, refile))
        self.assertEqual(rec["rc"], 0, g.stdout)
        self.assertFalse(rec["dangling_amendments"])
        self.assertFalse(rec["invalid_refiles"])

    def test_a_malformed_amendments_file_fails(self):
        self.on_dev(self.rows("t.a"))
        for text in ("not json\n", '{"amendments": {}}\n', '{"amendments": [{"kind": "native"}]}\n',
                     self.amendments(self.amendment("t.a"), self.amendment("t.a"))):
            g, rec = self.gate_amended(self.rows("t.a"), text)
            self.assertEqual(rec["rc"], 1, text)

    def test_status_shows_the_row_count_and_the_amendment_count(self):
        self.on_dev(self.rows("t.a"))
        self.gate_amended(self.rows("t.a", "t.new"), self.amendments(self.amendment("t.new")))
        s = self.train("status")
        self.assertIn("non-regressing against 2 known reds, 1 amended", s.stdout)
        self.assertIn("NOT green", s.stdout)

    def test_status_says_green_only_when_there_are_no_rows(self):
        self.on_dev(self.rows())
        self.gate_with()
        s = self.train("status")
        self.assertIn("green: the known-red baseline is empty", s.stdout)
        self.assertNotIn("NOT green", s.stdout)

    def test_the_verdict_words_push_prints_carry_the_amendment_count(self):
        self.assertEqual(train.verdict_words(json.loads(self.rows("t.a", "t.b"))["rows"],
                                             [self.amendment("t.b")]),
                         "non-regressing against 2 known reds, 1 amended "
                         "(planning/known-reds.json, planning/known-reds-amendments.json); NOT green")


class PremiseBaselineTests(TrainBase):
    """planning/premise-baseline.json is shrink-only across merges
    (PREMISE-BASELINE-MERGE-LOSS: a merge resolved 1,171 entries to 753)."""

    def baseline(self, *names):
        return json.dumps({"note": "n", "accepted": {n: "why " + n for n in names}},
                          indent=2, sort_keys=True) + "\n"

    def on_dev(self, *names):
        self.advance_dev({"planning/premise-baseline.json": self.baseline(*names)})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")

    def gate(self, premises):
        g = self.train("gate", extra_env={"STUB_PREMISES": json.dumps(premises)})
        st = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        return g, st["gates"]["premise_baseline"]

    def test_a_conflict_takes_the_union_of_both_sides_entries(self):
        self.on_dev("a", "b", "c")
        sha = self.lane("p", {"planning/premise-baseline.json": self.baseline("a", "c", "d")})
        self.advance_dev({"planning/premise-baseline.json": self.baseline("a", "b", "e")})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
        m = self.train("merge", f"p@{sha}")
        if m.returncode:
            sys.stderr.write(m.stdout + m.stderr)
        self.assertEqual(m.returncode, 0, "the conflict on the premise baseline did not resolve")
        merged = json.loads((self.work / "planning/premise-baseline.json").read_text())
        self.assertEqual(sorted(merged["accepted"]), ["a", "b", "c", "d", "e"])

    def test_a_dropped_entry_still_a_finding_refuses_and_a_resolved_one_passes(self):
        self.on_dev("a", "b", "c")
        sha = self.lane("p", {"planning/premise-baseline.json": self.baseline("a"),
                              "tools/x.py": "x\n"})
        self.assertEqual(self.train("merge", f"p@{sha}").returncode, 0)
        lost, record = self.gate({"a": {"class": "never concluded"},
                                  "b": {"class": "preserved only"},
                                  "c": {"class": "established by a hosted entry"}})
        self.assertNotEqual(lost.returncode, 0)
        self.assertEqual((record["rc"], record["dropped"], record["lost"]), (1, ["b", "c"], ["b"]))
        self.assertIn("LOST an entry that is still a finding (preserved only): b", lost.stdout)
        resolved, record = self.gate({"a": {"class": "never concluded"},
                                      "b": {"class": "established by a hosted entry"}})
        self.assertEqual(record["rc"], 0, resolved.stdout)
        self.assertEqual(record["lost"], [])

    def test_no_drop_runs_no_audit(self):
        self.on_dev("a")
        sha = self.lane("p", {"tools/x.py": "x\n"})
        self.assertEqual(self.train("merge", f"p@{sha}").returncode, 0)
        _, record = self.gate({})
        self.assertEqual((record["rc"], record["dropped"]), (0, []))
        self.assertNotIn("premise_audit --json", self.stub_log())


class PremiseTermBaselineTests(TrainBase):
    """planning/premise-term-baseline.json (premises assumed only of a term,
    D12's lane/d-premise-args) gets the same union and the same shrink-only
    gate, judged against premise_audit --json --all."""

    TERM = "planning/premise-term-baseline.json"
    baseline = PremiseBaselineTests.baseline
    on_dev = PremiseBaselineTests.on_dev

    def on_dev_terms(self, bare, terms):
        self.advance_dev({"planning/premise-baseline.json": self.baseline(*bare),
                          self.TERM: self.baseline(*terms)})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")

    def gate_terms(self, bare_premises, all_premises):
        g = self.train("gate", extra_env={"STUB_PREMISES": json.dumps(bare_premises),
                                          "STUB_PREMISES_ALL": json.dumps(all_premises)})
        st = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        return g, st["gates"]["premise_baseline"]

    def test_a_term_conflict_takes_the_union(self):
        self.on_dev_terms(["a"], ["t1", "t2"])
        sha = self.lane("p", {self.TERM: self.baseline("t1", "t3")})
        self.advance_dev({self.TERM: self.baseline("t2", "t4")})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
        m = self.train("merge", f"p@{sha}")
        self.assertEqual(m.returncode, 0, m.stdout + m.stderr)
        merged = json.loads((self.work / self.TERM).read_text())
        self.assertEqual(sorted(merged["accepted"]), ["t1", "t2", "t3", "t4"])

    def test_a_dropped_term_still_a_finding_refuses(self):
        self.on_dev_terms(["a"], ["t1", "t2", "t3"])
        sha = self.lane("p", {self.TERM: self.baseline("t1"), "tools/x.py": "x\n"})
        self.assertEqual(self.train("merge", f"p@{sha}").returncode, 0)
        # the bare audit says nothing of t2: only --all sees a term premise
        lost, record = self.gate_terms({}, {"t2": {"class": "never concluded"},
                                            "t3": {"class": "established by a hosted entry"}})
        self.assertNotEqual(lost.returncode, 0)
        self.assertEqual(record["rc"], 1)
        self.assertEqual((record["term"]["dropped"], record["term"]["lost"]), (["t2", "t3"], ["t2"]))
        self.assertIn("premise term baseline LOST an entry that is still a finding "
                      "(never concluded): t2", lost.stdout)
        self.assertIn("premise_audit --json --all", self.stub_log())

    def test_a_term_entry_moved_to_the_bare_baseline_is_carried(self):
        self.on_dev_terms(["a"], ["t1", "t2"])
        sha = self.lane("p", {"planning/premise-baseline.json": self.baseline("a", "t2"),
                              self.TERM: self.baseline("t1")})
        self.assertEqual(self.train("merge", f"p@{sha}").returncode, 0)
        g, record = self.gate_terms({}, {"t2": {"class": "never concluded"}})
        self.assertEqual(record["rc"], 0, g.stdout)
        self.assertEqual(record["term"]["lost"], [])

    def test_the_term_file_gone_at_head_refuses(self):
        self.on_dev_terms(["a"], ["t1"])
        sha = self.lane("p", {self.TERM: None})
        self.assertEqual(self.train("merge", f"p@{sha}").returncode, 0)
        g, record = self.gate_terms({}, {})
        self.assertEqual(record["rc"], 1, g.stdout)
        self.assertIn("premise-term-baseline.json is gone at HEAD", g.stdout)

    def test_no_term_file_on_dev_is_skipped(self):
        self.on_dev("a")
        sha = self.lane("p", {self.TERM: self.baseline("t1")})
        self.assertEqual(self.train("merge", f"p@{sha}").returncode, 0)
        g, record = self.gate_terms({}, {})
        self.assertEqual((record["rc"], record["term"]), (0, {"skipped": True}), g.stdout)


class CostObligationsGateTests(TrainBase):
    """Exercise the actual cost ratchet, with only the interface registry stubbed."""
    def setUp(self):
        super().setUp()
        from tools import cost_obligations, interface_emit

        (self.seed / "books").mkdir()
        script = f'''import sys
from pathlib import Path
from unittest import mock
sys.path.insert(0, {str(REPO)!r})
from tools import cost_obligations, interface_emit
import json
assert sys.argv[1:] == ["--check"]
root = Path.cwd()
with mock.patch.object(interface_emit, "registry", lambda root: json.loads(
        (root / "planning/dispatched.json").read_text())):
    findings = cost_obligations.check(root)
for finding in findings:
    print(finding)
print("cost_obligations: {{}} finding(s)".format(len(findings)))
sys.exit(1 if findings else 0)
'''
        with mock.patch.object(interface_emit, "registry", return_value={"entries": []}):
            # Build the protected base with no dispatched entry. HEAD will
            # contain the new entry, so falling back to HEAD would miss it.
            generator = '(defconst *fn-cost-contracts* \'((car 0 "one cell read")))\n'
            (self.seed / "books/def-cost.lisp").write_text(generator)
            obligations = cost_obligations.render(cost_obligations.build(self.seed))
            contracts = cost_obligations.render(cost_obligations.build_contracts(self.seed))
        # vertical-cost-route: every tree carries the final-world aggregate,
        # its last form (def-cost-check-all); this fixture declares no row.
        final_world = '(in-package "ACL2")\n(def-cost-check-all)\n'
        self.advance_dev({"tools/cost_obligations.py": script,
                          "books/def-cost.lisp": generator,
                          "books/cost-final-world.lisp": final_world,
                          "planning/dispatched.json": '{"entries": []}\n',
                          "planning/cost-obligations.json": obligations,
                          "planning/cost-contracts.json": contracts})
        sh(self.work, "git", "pull", "-q", "--ff-only")
        head = self.head()
        (self.work / "build/train/box-step.json").write_text(
            json.dumps({"sha": head, "ran_at": head, "box": "persvati"}))

    def test_a_dispatched_entry_without_def_cost_fails_and_is_named(self):
        from tools import cost_obligations, interface_emit
        entries = {"entries": [{"name": "fn-new-dispatched", "class": "common-lisp-compliant",
                                 "dispatched_from": ["host/native/io.lisp"]}]}
        (self.work / "planning/dispatched.json").write_text(json.dumps(entries))
        with mock.patch.object(interface_emit, "registry", return_value=entries):
            (self.work / "planning/cost-obligations.json").write_text(
                cost_obligations.render(cost_obligations.build(self.work)))
        self.commit(self.work, "new dispatched entry without cost")
        g = self.train("gate")
        self.assertNotEqual(g.returncode, 0, g.stdout + g.stderr)
        self.assertIn("fn-new-dispatched: a new guard-verified dispatched entry with no def-cost", g.stdout)
        record = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        self.assertEqual(record["gates"]["cost_obligations"]["rc"], 1)

    def test_a_clean_tree_passes(self):
        g = self.train("gate")
        self.assertEqual(g.returncode, 0, g.stdout + g.stderr)
        self.assertIn("cost_obligations: 0 finding(s)", g.stdout)
        record = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        self.assertEqual(record["gates"]["cost_obligations"]["rc"], 0)

    def test_gates_lists_cost_obligations(self):
        self.assertIn("cost_obligations", train.GATES)


class BookRootsGateTests(TrainBase):
    def test_an_orphan_book_fails_the_train_gate(self):
        script = f'''import sys
from pathlib import Path
from unittest import mock
sys.path.insert(0, {str(REPO)!r})
from tools import book_roots_check
with mock.patch.object(book_roots_check.ledger, "ROOT", Path.cwd()):
    sys.exit(book_roots_check.main(Path.cwd(), excluded={{}}))
'''
        (self.work / "tools/book_roots_check.py").write_text(script)
        (self.work / "Makefile").write_text("ACL2_BOOKS =\n")
        (self.work / "books").mkdir()
        (self.work / "books/orphan.lisp").write_text("")
        self.commit(self.work, "orphan production book")
        head = self.head()
        (self.work / "build/train/box-step.json").write_text(
            json.dumps({"sha": head, "ran_at": head, "box": "persvati"}))
        g = self.train("gate")
        self.assertNotEqual(g.returncode, 0, g.stdout + g.stderr)
        self.assertIn("books/orphan.lisp is outside", g.stdout)
        record = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        self.assertEqual(record["gates"]["book_roots"]["rc"], 1)
        self.assertTrue(all(gate["rc"] == 0 for name, gate in record["gates"].items()
                            if name != "book_roots"), g.stdout + g.stderr)

    def test_gates_lists_book_roots(self):
        self.assertIn("book_roots", train.GATES)


class HarnessGateTests(TrainBase):
    def test_a_clean_harness_passes(self):
        g = self.train("gate")
        self.assertEqual(g.returncode, 0, g.stdout + g.stderr)
        self.assertIn("harness_check --quiet", self.stub_log())
        self.assertIn("tools/harness_check.py --quiet  -> rc 0", g.stdout)
        self.assertTrue((self.work / "build/train/logs/gate-harness.log").is_file())
        record = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        self.assertEqual(record["gates"]["harness"]["rc"], 0)
        self.assertEqual(record["gates"]["harness"]["head"], self.head())

    def test_a_harness_finding_fails_and_refuses_push(self):
        sha = self.lane("a", {"other.txt": "ok\n"})
        self.assertEqual(self.train("merge", f"a@{sha}").returncode, 0)
        before = self.origin_rev("dev")
        g = self.train("gate", extra_env={"STUB_RC_harness_check_quiet": "1"})
        self.assertEqual(g.returncode, 1, g.stdout + g.stderr)
        record = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        self.assertEqual(record["gates"]["harness"]["rc"], 1)
        self.assertEqual(record["gates"]["harness"]["head"], self.head())
        self.assertTrue(all(gate["rc"] == 0 for name, gate in record["gates"].items()
                            if name != "harness"), g.stdout + g.stderr)
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("gate harness failed (rc 1); push refused", p.stdout)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_gates_lists_harness(self):
        self.assertIn("harness", train.GATES)


class EvidenceSizeGateTests(TrainBase):
    PATH = "planning/big-evidence.txt"

    def change(self, files):
        sha = self.lane("evidence-size", files)
        self.assertEqual(self.train("merge", f"evidence-size@{sha}").returncode, 0)

    def gate(self, expected):
        g = self.train("gate", "--local")
        self.assertEqual(g.returncode, expected, g.stdout + g.stderr)
        record = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        self.assertEqual(record["gates"]["evidence_size"]["rc"], expected)
        self.assertTrue(all(gate["rc"] == 0 for name, gate in record["gates"].items()
                            if name != "evidence_size"), g.stdout + g.stderr)
        self.assertEqual((self.work / "build/train/logs/gate-evidence_size.log").read_text(),
                         "\n".join(line for line in g.stdout.splitlines()
                                   if line.startswith(("evidence_size:", "REFUSED "))) + "\n")
        return g

    def test_adding_50001_lines_refuses_push(self):
        self.change({self.PATH: "line\n" * 50_001})
        before = self.origin_rev("dev")
        g = self.gate(1)
        self.assertIn(f"{self.PATH}: 50001 lines", g.stdout)
        self.assertIn("publish to hbox evidence and cite by sha256", g.stdout)
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("gate evidence_size failed (rc 1); push refused", p.stdout)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_50000_lines_pass(self):
        self.change({self.PATH: "line\n" * 50_000})
        self.gate(0)

    def test_unterminated_final_line_counts(self):
        self.change({self.PATH: "line\n" * 50_000 + "last"})
        self.assertIn(f"{self.PATH}: 50001 lines", self.gate(1).stdout)

    def test_modifying_existing_big_file_refuses(self):
        self.advance_dev({self.PATH: "line\n" * 50_001})
        sh(self.work, "git", "pull", "-q", "--ff-only")
        self.change({self.PATH: "changed\n" + "line\n" * 50_000})
        self.assertIn(f"{self.PATH}: 50001 lines", self.gate(1).stdout)

    def test_deleting_existing_big_file_passes(self):
        self.advance_dev({self.PATH: "line\n" * 50_001})
        sh(self.work, "git", "pull", "-q", "--ff-only")
        self.change({self.PATH: None})
        self.gate(0)

    def test_untouched_big_file_on_dev_passes(self):
        self.advance_dev({self.PATH: "line\n" * 50_001})
        sh(self.work, "git", "pull", "-q", "--ff-only")
        self.change({"other.txt": "small\n"})
        self.gate(0)

    def test_big_file_outside_planning_passes(self):
        self.change({"other.txt": "line\n" * 50_001})
        self.gate(0)

    def test_non_utf8_size_boundary(self):
        for size, expected in ((4 * 1024 * 1024, 0), (4 * 1024 * 1024 + 1, 1)):
            with self.subTest(size=size):
                (self.work / self.PATH).write_bytes(b"\xff" * size)
                self.commit(self.work, "binary evidence")
                g = self.gate(expected)
                if expected:
                    self.assertIn(f"{self.PATH}: {size} bytes (non-UTF-8", g.stdout)
                    self.assertIn("publish to hbox evidence and cite by sha256", g.stdout)

    def test_gates_lists_evidence_size_before_box_step(self):
        self.assertIn("evidence_size", train.GATES)
        self.assertEqual(train.GATES.index("evidence_size") + 1, train.GATES.index("box_step"))


class AsciiGateTests(unittest.TestCase):
    def gate(self, changed, refusals):
        temporary = tempfile.TemporaryDirectory(prefix="train-ascii-")
        self.addCleanup(temporary.cleanup)
        t = SimpleNamespace(root=Path(temporary.name), logs=Path(temporary.name) / "logs")
        out = "".join(f"REFUSED {r}: bytes 0xE2 0x80 0x99 (U+2019): books/ and host/ are ASCII (PKT-379)\n" for r in refusals)
        with mock.patch.object(train, "git", return_value=SimpleNamespace(stdout="\n".join(changed))), \
                mock.patch.object(train.subprocess, "run", return_value=SimpleNamespace(stdout=out, stderr="", returncode=0)), \
                mock.patch.object(train, "say"):
            return train._ascii_gate(t)

    def test_refusal_in_a_changed_file_fails(self):
        self.assertEqual(self.gate(["host/native/io.lisp"], ["host/native/io.lisp:12:3"]), 1)

    def test_older_refusal_in_an_unchanged_file_passes(self):
        self.assertEqual(self.gate(["host/native/io.lisp"], ["books/blake3-tree.lisp:627:17"]), 0)

    def test_nothing_changed_skips(self):
        self.assertEqual(self.gate([], ["books/blake3-tree.lisp:627:17"]), 0)

class CensusTests(unittest.TestCase):
    HEAD = "a" * 40
    LINE = ("census: units=23068 executed=10417 never=11755 removable=2575 code_mb=12.38 "
            "never_mb=7.24 removable_mb=1.53\n")
    DELTA = ("census-delta: units=+0 executed=+92 never=-84 removable=-21 code_mb=+0.00 "
             "never_mb=-0.05 removable_mb=-0.01\n")

    def test_a_finished_census_reads_its_figures_and_delta(self):
        got = train.parse_census("== census done status 0", self.LINE + self.DELTA)
        self.assertEqual(got["figures"]["units"], 23068)
        self.assertEqual(got["figures"]["code_mb"], 12.38)
        self.assertEqual(got["delta"]["never"], -84)
        self.assertIsNone(train.parse_census("== census done status 0", self.LINE)["delta"])

    def test_an_unfinished_or_failed_or_malformed_census_is_refused(self):
        for last in ("== census done status 1", "== run 23:55:01", ""):
            with self.assertRaises(train.TrainError):
                train.parse_census(last, self.LINE)
        with self.assertRaises(train.TrainError):
            train.parse_census("== census done status 0", "")
        with self.assertRaises(train.TrainError):
            train.parse_census("== census done status 0", "census: units=1 code_mb=2.00\n")
        with self.assertRaises(train.TrainError):
            train.parse_census("== census done status 0", self.LINE.replace("12.38", "x"))

    def test_the_words_read_units_and_code_and_name_only_moves_beyond_noise(self):
        rec = dict(train.parse_census("== census done status 0", self.LINE + self.DELTA), source=self.HEAD)
        self.assertEqual(train.census_words(rec, self.HEAD),
                         "census: units=23068 code_mb=12.38 (units +0, code_mb +0.00)")
        moved = self.DELTA.replace("units=+0", "units=-310").replace("removable=-21", "removable=-400")
        rec = dict(train.parse_census("== census done status 0", self.LINE + moved), source=self.HEAD)
        self.assertEqual(train.census_words(rec, self.HEAD),
                         "census: units=23068 code_mb=12.38 (units -310, code_mb +0.00; beyond noise: removable -400)")
        self.assertEqual(train.census_words(rec, "b" * 40), "census: not run at HEAD")
        self.assertEqual(train.census_words(None, self.HEAD), "census: not run at HEAD")


class ImageModuleTests(unittest.TestCase):
    """The image gate's pure half: which modules a diff obliges, the box's
    lines parsed, and the verdict."""

    HEAD = "a" * 40

    def test_launcher_only_diff_obliges_nntp_post_probe_with_other_modules(self):
        path = "tools/build_native_host.sh"
        probe = "tests.test_native_nntp_post_probe"
        expected = {"tests.test_native_operator_verbs", "tests.test_native_heap_from_profile",
                    probe, *train.SERVED_NATIVES}
        self.assertEqual(train.image_modules([path], REPO), {m: [path] for m in expected})
        self.assertNotIn(probe, train.SERVED_NATIVES)
        self.assertEqual(train.image_modules(["tools/train.py"], REPO), {})

    def ran(self, modules, source=None):
        return {"source": source or self.HEAD, "dir": "/box/run",
                "modules": {m: {"rc": 0, "cases": {m + ".T.test_ok": "ok"}} for m in modules}}

    def test_native_pin_carry_probe_obliges_its_module_with_negative_control(self):
        path = "tests/native_bp_pin_carry.lisp"
        need = train.image_modules([path], REPO)
        self.assertIn("tests.test_native_bp_pin_carry", need)
        self.assertEqual(need["tests.test_native_bp_pin_carry"], [path])
        self.assertEqual(train.image_modules(["tests/unreferenced-B22-probe.lisp"], REPO), {})

    def test_probe_derivation_finds_all_consumers_and_changed_native_suites(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "tests").mkdir()
            (root / "tests/test_native_a.py").write_text('probe = "tests/shared-probe.lisp"\n')
            (root / "tests/test_native_b.py").write_text('probe = "shared-probe.lisp"\n')
            (root / "tests/test_other_image.py").write_text('from tests.native_harness import run\nprobe = "tests/shared-probe.lisp"\n')
            (root / "tests/test_ordinary.py").write_text('probe = "tests/shared-probe.lisp"\n')
            expected = {f"tests.{m}": ["tests/shared-probe.lisp"]
                        for m in ("test_native_a", "test_native_b", "test_other_image")}
            self.assertEqual(train.image_modules(["tests/shared-probe.lisp"], root), expected)
            self.assertEqual(train.image_modules(["tests/shared-probe.lisp-more.lisp"], root), {})
            for name in ("test_native_a", "test_other_image"):
                path = f"tests/{name}.py"
                self.assertEqual(train.image_modules([path], root), {f"tests.{name}": [path]})
            self.assertEqual(train.image_modules(["tests/test_ordinary.py"], root), {})

    def test_include_directories_resolve_nil_fn_and_exclude_system(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "host").mkdir()
            (root / "acl2-projects").write_text(':FN "."\n')
            path = "host/new-adapter.lisp"
            expected = {m: [path] for m in train.BP_NATIVES}
            for include in ('(include-book "../books/bp-release" :dir nil)',
                            '(include-book "../books/bp-release" :dir ())',
                            '(include-book "books/bp-release" :dir :fn)'):
                with self.subTest(include=include):
                    (root / path).write_text(include)
                    self.assertEqual(train.image_modules([path], root), expected)
            (root / path).write_text('(include-book "books/bp-release" :dir :system)')
            self.assertEqual(train.image_modules([path], root), {})

    def test_unsupported_include_directories_or_fn_contract_refuse(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "host").mkdir()
            path = "host/new-adapter.lisp"
            (root / path).write_text('(include-book "books/bp-release" :dir :other)')
            with self.assertRaisesRegex(train.TrainError, "unsupported include-book :dir :other"):
                train.image_modules([path], root)
            (root / path).write_text('(include-book "books/bp-release" :dir :fn)')
            with self.assertRaisesRegex(train.TrainError, "cannot resolve :dir :fn"):
                train.image_modules([path], root)
            (root / "acl2-projects").write_text(':FN "elsewhere"\n')
            with self.assertRaisesRegex(train.TrainError, "unsupported.*contract"):
                train.image_modules([path], root)

    def test_literal_make_event_and_nested_event_containers_derive_bp_includes(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "host").mkdir()
            path = "host/new-adapter.lisp"
            for event in ('(make-event \'(include-book "../books/bp-release"))',
                          '(progn (encapsulate () (make-event \'(progn (include-book "../books/bp-release")))))',
                          '(progn! (encapsulate () (include-book "../books/bp-release")))'):
                with self.subTest(event=event):
                    (root / path).write_text(event)
                    self.assertEqual(train.image_modules([path], root), {m: [path] for m in train.BP_NATIVES})
            (root / path).write_text('(defconst *template* \'(include-book "../books/bp-release"))')
            self.assertEqual(train.image_modules([path], root), {})

    def test_computed_make_event_refuses_even_inside_containers(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "host").mkdir()
            path = "host/new-adapter.lisp"
            for event in ('(make-event (f state))',
                          '(make-event (compute-event state))',
                          '(progn (encapsulate () (make-event (compute-event state))))',
                          '(make-event \'(progn (make-event (compute-event state))))'):
                with self.subTest(event=event):
                    (root / path).write_text(event)
                    with self.assertRaisesRegex(train.TrainError, "new-adapter.lisp: unresolved make-event"):
                        train.image_modules([path], root)

    def test_raw_dispatch_verdicts_quasiquoted_table_has_no_dependency_events(self):
        import ledger
        path = "host/raw-dispatch-verdicts.lisp"
        forms = ledger.Reader((REPO / path).read_text(encoding="utf-8")).top_level()
        events = [(form, line) for form, line in forms if ledger.head(form) == "make-event"]
        self.assertEqual(len(events), 1)
        expression = events[0][0][1]
        self.assertEqual(ledger.head(expression), "quasiquote")
        self.assertEqual(ledger.head(expression[1]), "table")
        # The real adapter's ',(...) is quote around an unquote, not an event.
        self.assertEqual(ledger.head(expression[1][3]), "quote")
        self.assertEqual(ledger.head(expression[1][3][1]), "unquote")
        self.assertEqual(list(train.image_dependency_events(events, path)), [])
        self.assertEqual(train.image_modules([path], REPO), {})

    def test_quasiquoted_leaf_event_heads_have_no_dependencies(self):
        import ledger
        for name in ("table", "defconst", "value-triple", "in-theory", "defthm",
                     "defthmd", "defun", "defund", "defun-nx", "defun-sk"):
            with self.subTest(head=name):
                forms = ledger.Reader(f"(make-event `({name} ,(f state) ,@(g state)))").top_level()
                self.assertEqual(list(train.image_dependency_events(forms, "host/adapter.lisp")), [])

    def test_quasiquoted_dependency_or_container_heads_refuse(self):
        import ledger
        for name in sorted(ledger.TRANSPARENT | {"progn", "include-book", "encapsulate",
                                                "mutual-recursion", "make-event",
                                                "def-carried-view", "unknown-event"}):
            with self.subTest(head=name):
                forms = ledger.Reader(
                    f'(make-event `({name} (include-book "../books/bp-release")))').top_level()
                with self.assertRaisesRegex(train.TrainError, "host/adapter.lisp: unresolved make-event"):
                    list(train.image_dependency_events(forms, "host/adapter.lisp"))

    def test_quasiquoted_nonliteral_heads_refuse(self):
        import ledger
        for template in ('(,(f state) data)', '(,@(f state) data)',
                         '("table" data)', ',(f state)', 'table'):
            with self.subTest(template=template):
                forms = ledger.Reader(f"(make-event `{template})").top_level()
                with self.assertRaisesRegex(train.TrainError, "host/adapter.lisp: unresolved make-event"):
                    list(train.image_dependency_events(forms, "host/adapter.lisp"))

    def test_bp_host_adapters_oblige_the_bp_native_modules(self):
        expected = {"tests.test_bp_app_native", "tests.test_bp_obligation_native",
                    "tests.test_native_ion_workflow", "tests.test_native_bp_pin_carry",
                    "tests.test_native_bp_carry_abandon"}
        for path in ("host/bp-release-owner-host.lisp", "host/workflow-host.lisp"):
            with self.subTest(path=path):
                self.assertEqual(train.image_modules([path], REPO), {m: [path] for m in expected})
        self.assertEqual(train.image_modules(["host/owner-host.lisp"], REPO), {})

    def test_bp_host_derivation_uses_local_includes_not_names_comments_or_quotes(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "host").mkdir()
            path = "host/new-adapter.lisp"
            file = root / path
            file.write_text('(in-package "ACL2")\n(include-book "../books/bp-release")\n')
            self.assertEqual(train.image_modules([path], root), {m: [path] for m in train.BP_NATIVES})
            file.write_text('; (include-book "../books/bp-release")\n'
                            '\'(include-book "../books/bp-release")\n'
                            '(local (include-book "../books/bp-release"))\n'
                            '(include-book "../books/bp-release" :dir :system)\n'
                            '(defun bp-looking-name () nil)\n')
            self.assertEqual(train.image_modules([path], root), {})
            file.write_text('(include-book "../books/bp-release"')
            with self.assertRaisesRegex(train.TrainError, "cannot derive image obligations"):
                train.image_modules([path], root)

    def test_drop_matches_box_and_dir_and_preserves_other_runs(self):
        first = train.merge_image_run(None, self.HEAD, "hbox", "/s/native-standin", self.ran(["a"])["modules"], "b" * 40)
        prior = train.merge_image_run(first, self.HEAD, "persvati", "/s/native-real", self.ran(["b"])["modules"], "c" * 40)
        before = json.dumps(prior, sort_keys=True)
        with self.assertRaisesRegex(train.TrainError, "no image module entry"):
            train.drop_image_run(prior, "standin", {"box": "persvati", "dir": "/s/native-standin"})
        after, dropped, directory = train.drop_image_run(prior, "standin", {"box": "hbox", "dir": "/s/native-standin"})
        self.assertEqual((dropped, directory), (["a"], "/s/native-standin"))
        self.assertEqual(after, {"source": self.HEAD, "runs": {"/s/native-real": "persvati"},
                                 "modules": {"b": prior["modules"]["b"]},
                                 "images_from": {"/s/native-real": "c" * 40}})
        self.assertEqual(json.dumps(prior, sort_keys=True), before)
        with self.assertRaisesRegex(train.TrainError, "no image module entry"):
            train.drop_image_run(after, "standin", {"box": "hbox", "dir": directory})

    def test_drop_without_record_requires_one_exact_native_label_directory(self):
        prior = train.merge_image_run(None, self.HEAD, "hbox", "/s/native-one", self.ran(["a"])["modules"])
        prior = train.merge_image_run(prior, self.HEAD, "hbox", "/s/native-one-more", self.ran(["b"])["modules"])
        after, dropped, _ = train.drop_image_run(prior, "one", None)
        self.assertEqual(dropped, ["a"])
        self.assertEqual(after["modules"], {"b": prior["modules"]["b"]})
        self.assertEqual(after["runs"], {"/s/native-one-more": "hbox"})
        with self.assertRaisesRegex(train.TrainError, "no recorded image run"):
            train.drop_image_run(prior, "missing", None)
        ambiguous = train.merge_image_run(prior, self.HEAD, "persvati", "/other/native-one", self.ran(["c"])["modules"])
        with self.assertRaisesRegex(train.TrainError, "ambiguous"):
            train.drop_image_run(ambiguous, "one", None)

    def test_drop_refuses_an_empty_run_and_removes_last_run_provenance(self):
        prior = train.merge_image_run(None, self.HEAD, "hbox", "/s/native-empty", {})
        with self.assertRaisesRegex(train.TrainError, "no image module entry"):
            train.drop_image_run(prior, "empty", None)
        prior = train.merge_image_run(prior, self.HEAD, "hbox", "/s/native-one", self.ran(["a"])["modules"], "b" * 40)
        after, _, _ = train.drop_image_run(prior, "one", None)
        self.assertEqual(after, {"source": self.HEAD, "runs": {"/s/native-empty": "hbox"}, "modules": {}})

    def test_drop_supports_a_single_run_record_and_keeps_unrelated_state(self):
        prior = dict(self.ran(["a"]), box="hbox", dir="/s/native-one", extra="keep")
        after, dropped, _ = train.drop_image_run(prior, "one", None)
        self.assertEqual(dropped, ["a"])
        self.assertEqual(after, dict(prior, modules={}))

    def test_a_module_log_with_a_non_text_octet_still_reads_its_cases(self):
        # train 86: a NUL in test_native_key_statements' log made grep call it
        # a binary file and print nothing, so the module read with no case
        with tempfile.TemporaryDirectory() as d:
            run = Path(d)
            (run / "rc").mkdir()
            (run / "logs").mkdir()
            (run / "rc" / "test-tests.m").write_text("1\n")
            record = {"module": "tests.m", "cases": [["tests.m.T.test_a", "ok"], ["tests.m.T.test_b", "FAIL"]]}
            (run / "logs" / "test-tests.m.log").write_bytes(
                b"article \x00\xff body\n" + b"FN_TEST_BUDGET_RESULT " + json.dumps(record).encode() + b"\n")
            out = subprocess.run(["sh", "-c", train.image_read_script(str(run))],
                                 capture_output=True, text=True, check=True).stdout
        read = train.parse_image_results(out)
        self.assertEqual(read["tests.m"]["rc"], 1)
        self.assertEqual(read["tests.m"]["cases"], {"tests.m.T.test_a": "ok", "tests.m.T.test_b": "FAIL"})

    def test_a_reservation_book_change_obliges_the_capacity_vector(self):
        need = train.image_modules(["books/store-maintenance-reserve.lisp", "README.md"])
        self.assertEqual(need, {"tests.test_native_capacity_vector": ["books/store-maintenance-reserve.lisp"]})
        need = train.image_modules(["books/heap-figure.lisp"])
        self.assertIn("tests.test_native_capacity_vector", need)
        self.assertIn("tests.test_native_heap_from_profile", need)

    def test_a_launcher_change_obliges_the_served_natives_operator_verbs_and_heap_from_profile(self):
        need = train.image_modules(["packaging/launcher-decide.sh", "README.md"])
        self.assertEqual(set(need), {"tests.test_native_operator_verbs",
                                     "tests.test_native_heap_from_profile", "tests.test_native_nntp_post_probe",
                                     *train.SERVED_NATIVES})
        self.assertIn("tests.test_native_served_line_stack", need)
        self.assertEqual(need["tests.test_native_owner"], ["packaging/launcher-decide.sh"])

    def test_heap_probe_and_host_native_oblige_and_unrelated_paths_do_not(self):
        self.assertTrue(train.image_modules(["books/heap-figure.lisp"]))
        self.assertTrue(train.image_modules(["host/native/admin.lisp"]))
        self.assertTrue(train.image_modules(["tools/extract/core_launcher.py"]))
        self.assertEqual(train.image_modules(["host/owner-host.lisp", "tools/train.py",
                                              "books/heap-figure-tests.lisp", "packaging/fn.md"]), {})

    def test_f2_acl2_projects_file_is_an_image_input(self):
        self.assertEqual(train.image_inputs_changed(["acl2-projects"]), ["acl2-projects"])

    def test_f2_acl2_projects_loader_is_an_image_input(self):
        self.assertEqual(train.image_inputs_changed(["tools/acl2_projects.py"]), ["tools/acl2_projects.py"])

    def test_f2_acl2_toolchain_is_an_image_input(self):
        self.assertEqual(train.image_inputs_changed(["tools/acl2_toolchain.py"]), ["tools/acl2_toolchain.py"])

    def test_image_input_classification_keeps_devs_default(self):
        paths = ["tools/train.py", "unlisted-source", "VERSION", "tests/acl2/a.lisp",
                 "planning/proofs.json", "docs/a.md", "tests/test_train.py"]
        self.assertEqual(train.image_inputs_changed(paths), paths[:4])

    def test_parse_reads_rc_and_cases_and_keeps_a_caseless_crash(self):
        text = "\n".join([
            "RC tests.test_native_owner 0",
            "RC tests.test_native_operator_verbs 1",
            "RC tests.test_native_served_cost 137",
            'FN_TEST_BUDGET_RESULT {"module": "tests.test_native_owner", "cases": [["o.T.a", "ok"], ["o.T.b", "skip"]]}',
            'FN_TEST_BUDGET_RESULT {"module": "tests.test_native_operator_verbs", "cases": [["v.T.a", "FAIL"]]}',
            'FN_TEST_BUDGET_RESULT {"module": "tests.test_native_not_run_here", "cases": [["n.T.a", "ok"]]}',
            "FN_TEST_BUDGET_RESULT {not json"])
        got = train.parse_image_results(text)
        self.assertEqual(got, {"tests.test_native_owner": {"rc": 0, "cases": {"o.T.a": "ok", "o.T.b": "skip"}},
                               "tests.test_native_operator_verbs": {"rc": 1, "cases": {"v.T.a": "FAIL"}},
                               "tests.test_native_served_cost": {"rc": 137, "cases": {}}})

    def test_nothing_obliged_is_green_without_a_run(self):
        self.assertEqual(train.image_verdict({}, None, self.HEAD, []), (0, {"skipped": True}))

    def test_obliged_without_a_run_or_with_another_commits_run_refuses(self):
        need = train.image_modules(["packaging/fn"])
        self.assertEqual(train.image_verdict(need, None, self.HEAD, [])[0], 1)
        rc, rec = train.image_verdict(need, self.ran(need, source="b" * 40), self.HEAD, [])
        self.assertEqual(rc, 1)
        self.assertIn("not HEAD", rec["error"])

    def test_another_commits_record_stands_only_across_planning_and_docs(self):
        need = train.image_modules(["packaging/fn"])
        other = self.ran(need, source="b" * 40)
        rc, rec = train.image_verdict(need, other, self.HEAD, [],
                                      lambda s: ["docs/resource-contract.md", "planning/proofs.json"])
        self.assertEqual(rc, 0, rec)
        self.assertEqual(rec["carried_from"], "b" * 40)
        for path in ("tests/test_native_owner.py", "tools/extract/probes.py", "host/native/io.lisp",
                     "books/heap.lisp", "Makefile"):
            rc, rec = train.image_verdict(need, other, self.HEAD, [], lambda s: ["docs/x.md", path])
            self.assertEqual(rc, 1, path)
            self.assertIn(path, rec["error"])
        # a source that is no commit here never stands for HEAD
        rc, rec = train.image_verdict(need, other, self.HEAD, [], lambda s: None)
        self.assertEqual(rc, 1)
        self.assertIn("not HEAD", rec["error"])
        # a carried record is still read case by case
        other["modules"]["tests.test_native_owner"] = {"rc": 1, "cases": {"o.T.a": "FAIL"}}
        rc, rec = train.image_verdict(need, other, self.HEAD, [], lambda s: ["docs/x.md"])
        self.assertEqual(rc, 1)
        self.assertEqual(rec["unexplained"], ["o.T.a"])

    def test_every_obliged_module_green_at_head_passes(self):
        need = train.image_modules(["packaging/fn"])
        self.assertEqual(train.image_verdict(need, self.ran(need), self.HEAD, [])[0], 0)

    def test_an_interrupted_image_gate_refuses_naming_the_missing_modules(self):
        need = train.image_modules(["packaging/fn"])
        partial = self.ran([m for m in need if m != "tests.test_native_served_line_stack"])
        rc, rec = train.image_verdict(need, partial, self.HEAD, [])
        self.assertEqual(rc, 1)
        self.assertEqual(rec["missing"], ["tests.test_native_served_line_stack"])

    def test_a_red_case_passes_only_as_a_native_known_red(self):
        need = train.image_modules(["packaging/fn"])
        run = self.ran(need)
        red = "tests.test_native_operator_verbs.C.test_status"
        run["modules"]["tests.test_native_operator_verbs"] = {"rc": 1, "cases": {red: "FAIL", "x.ok": "ok"}}
        rc, rec = train.image_verdict(need, run, self.HEAD, [])
        self.assertEqual((rc, rec["unexplained"]), (1, [red]))
        row = {"kind": "native", "subject": red, "item": "I", "owner": "o", "evidence": "e"}
        rc, rec = train.image_verdict(need, run, self.HEAD, [row])
        self.assertEqual((rc, rec["known_reds"]), (0, [red]))
        # a row of another kind with the same subject does not excuse it
        self.assertEqual(train.image_verdict(need, run, self.HEAD, [dict(row, kind="check")])[0], 1)

    def test_an_obliged_module_whose_every_test_skipped_refuses_and_is_named(self):
        need = train.image_modules(["packaging/fn"])
        run = self.ran(need)
        run["modules"]["tests.test_native_over_window"] = {"rc": 4, "cases": {}}
        rc, rec = train.image_verdict(need, run, self.HEAD, [])
        self.assertEqual((rc, rec["skipped"]), (1, ["tests.test_native_over_window"]))

    def test_a_skipped_case_of_an_obliged_module_refuses(self):
        need = train.image_modules(["packaging/fn"])
        run = self.ran(need)
        run["modules"]["tests.test_native_owner"] = {"rc": 0, "cases": {"o.T.a": "ok", "o.T.b": "skip"}}
        rc, rec = train.image_verdict(need, run, self.HEAD, [])
        self.assertEqual((rc, rec["skipped"]), (1, ["o.T.b"]))

    def test_a_skip_in_a_module_nothing_obliges_is_not_read(self):
        need = train.image_modules(["packaging/fn"])
        run = self.ran(need)
        run["modules"]["tests.test_native_mux"] = {"rc": 4, "cases": {}}
        self.assertEqual(train.image_verdict(need, run, self.HEAD, [])[0], 0)

    def test_a_failed_module_with_no_case_recorded_refuses(self):
        need = train.image_modules(["packaging/fn"])
        run = self.ran(need)
        run["modules"]["tests.test_native_owner"] = {"rc": 137, "cases": {}}
        rc, rec = train.image_verdict(need, run, self.HEAD, [])
        self.assertEqual(rc, 1)
        self.assertEqual(rec["unexplained"], ["tests.test_native_owner (rc 137, no case recorded)"])

    def test_a_later_run_supersedes_a_skipped_module_and_only_a_skipped_one(self):
        skipped = {"tests.test_native_over_window": {"rc": 4, "cases": {}},
                   "tests.test_native_owner": {"rc": 0, "cases": {"o.T.a": "ok", "o.T.b": "skip"}},
                   "tests.test_native_served_cost": {"rc": 0, "cases": {"s.T.a": "ok"}}}
        one = train.merge_image_run(None, self.HEAD, "hbox", "/r/main", skipped)
        rerun = {"tests.test_native_over_window": {"rc": 0, "cases": {"w.T.a": "ok"}},
                 "tests.test_native_owner": {"rc": 0, "cases": {"o.T.a": "ok", "o.T.b": "ok"}}}
        two = train.merge_image_run(one, self.HEAD, "hbox", "/r/fixtures", rerun)
        self.assertEqual({m: e["run"] for m, e in two["modules"].items()},
                         {"tests.test_native_over_window": "/r/fixtures",
                          "tests.test_native_owner": "/r/fixtures",
                          "tests.test_native_served_cost": "/r/main"})
        with self.assertRaises(train.TrainError):
            train.merge_image_run(two, self.HEAD, "hbox", "/r/third",
                                  {"tests.test_native_served_cost": {"rc": 0, "cases": {"s.T.a": "ok"}}})

    def test_runs_at_head_merge_by_module_and_a_module_from_two_runs_is_refused(self):
        a = {"tests.test_native_owner": {"rc": 0, "cases": {"o.T.a": "ok"}}}
        b = {"tests.test_native_heap_from_profile": {"rc": 1, "cases": {"h.T.a": "FAIL"}}}
        one = train.merge_image_run(None, self.HEAD, "hbox", "/r/main", a)
        both = train.merge_image_run(one, self.HEAD, "hbox", "/r/2g", b)
        self.assertEqual(both["runs"], {"/r/main": "hbox", "/r/2g": "hbox"})
        self.assertEqual({m: e["run"] for m, e in both["modules"].items()},
                         {"tests.test_native_owner": "/r/main",
                          "tests.test_native_heap_from_profile": "/r/2g"})
        with self.assertRaises(train.TrainError) as refused:
            train.merge_image_run(both, self.HEAD, "hbox", "/r/third", a)
        self.assertIn("tests.test_native_owner (/r/main)", str(refused.exception))
        # re-reading a run replaces that run's modules only
        again = train.merge_image_run(both, self.HEAD, "hbox", "/r/main",
                                      {"tests.test_native_owner": {"rc": 1, "cases": {"o.T.a": "FAIL"}}})
        self.assertEqual(again["modules"]["tests.test_native_owner"]["rc"], 1)
        self.assertIn("tests.test_native_heap_from_profile", again["modules"])
        # a record of another commit is replaced, never merged
        other = train.merge_image_run(dict(both, source="b" * 40), self.HEAD, "hbox", "/r/3", a)
        self.assertEqual(sorted(other["modules"]), ["tests.test_native_owner"])


class AddedRootTests(TrainBase):
    """certify selects the roots a train adds to ACL2_BOOKS, changed or not."""

    MAKEFILE = "ACL2_BOOKS ?= books/a \\\n\tbooks/b \\\n\ttests/acl2/b-tests\n\nOTHER = x\n"

    def test_the_root_list_is_ledgers_reading(self):
        self.assertEqual(train.makefile_root_list(self.MAKEFILE), ["books/a", "books/b", "tests/acl2/b-tests"])
        with self.assertRaises(train.TrainError):
            train.makefile_root_list("NOTHING = 1\n")

    def test_no_makefile_selects_nothing_and_a_new_makefile_selects_every_root(self):
        self.assertEqual(train._added_roots(train.Train(self.work)), [])
        (self.work / "Makefile").write_text(self.MAKEFILE)
        self.commit(self.work, "first Makefile")
        self.assertEqual(train._added_roots(train.Train(self.work)),
                         ["books/a", "books/b", "tests/acl2/b-tests"])

    def test_a_root_listed_by_the_train_is_selected_and_a_dropped_one_is_not(self):
        self.advance_dev({"Makefile": self.MAKEFILE})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "checkout", "-q", "-B", "integrate/t1", "origin/dev")
        (self.work / "Makefile").write_text(self.MAKEFILE.replace(
            "\tbooks/b \\\n", "\tbooks/kept-claim \\\n").replace(
            "tests/acl2/b-tests\n", "tests/acl2/b-tests \\\n\ttests/acl2/rehooked-tests\n"))
        self.commit(self.work, "roots")
        self.assertEqual(train._added_roots(train.Train(self.work)),
                         ["books/kept-claim", "tests/acl2/rehooked-tests"])


class ImageGateTests(TrainBase):
    """The image gate inside `gate` and `push`."""

    def launcher_train(self):
        (self.work / "packaging").mkdir(exist_ok=True)
        (self.work / "packaging/launcher-decide.sh").write_text("# decide\n")
        self.commit(self.work, "launcher change")

    def gate(self):
        g = self.train("gate")
        st = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        return g, st["gates"]["image"]

    def test_a_train_with_no_obliging_change_skips_the_image_gate(self):
        (self.work / "other.txt").write_text("x\n")
        self.commit(self.work, "unrelated")
        g, rec = self.gate()
        self.assertEqual(g.returncode, 0, g.stdout)
        self.assertEqual((rec["rc"], rec.get("skipped")), (0, True))
        self.assertIn("TRAIN-DONE gate rc=0", g.stdout)

    def test_a_launcher_train_without_an_image_run_cannot_push(self):
        self.launcher_train()
        before = self.origin_rev("dev")
        g, rec = self.gate()
        self.assertNotEqual(g.returncode, 0)
        self.assertEqual(rec["rc"], 1)
        self.assertIn("TRAIN-DONE gate rc=1", g.stdout)
        p = self.train("push")
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("gate image failed", p.stdout)
        self.assertEqual(self.origin_rev("dev"), before)

    def test_an_interrupted_image_run_blocks_until_the_missing_modules_ran(self):
        self.launcher_train()
        need = sorted(train.image_modules(["packaging/launcher-decide.sh"]))
        self.set_image(need[:-1])
        g, rec = self.gate()
        self.assertNotEqual(g.returncode, 0)
        self.assertEqual(rec["missing"], need[-1:])
        self.assertIn("NOT RUN on HEAD's image: " + need[-1], g.stdout)
        self.set_image(need)
        g, rec = self.gate()
        self.assertEqual(g.returncode, 0, g.stdout)
        p = self.train("push")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual(self.origin_rev("dev"), self.head())

    def test_image_without_a_run_record_refuses_by_name(self):
        p = self.train("image")
        self.assertEqual(p.returncode, 2)
        self.assertIn("no image run record", p.stdout)
        self.assertIn("TRAIN-DONE image rc=2", p.stdout)

    def image_runs(self, runs):
        """A stub ssh answering each run dir with its modules' rc and cases, and
        one hbox_native.sh record per label at HEAD."""
        stubs = self.tmp / "stubs"
        stubs.mkdir(exist_ok=True)
        lines = {d: "\n".join([f"RC {m} {rc}" for m, (rc, _) in mods.items()] + [
            "FN_TEST_BUDGET_RESULT " + json.dumps({"module": m, "cases": [[m + ".T.a", case]]})
            for m, (_, case) in mods.items()]) for d, mods in runs.items()}
        (stubs / "answers.json").write_text(json.dumps(lines))
        (stubs / "ssh").write_text("#!%s\nimport json, sys\nanswers = json.load(open(%r))\n"
                                   "print(next(v for d, v in answers.items() if d in sys.argv[-1]))\n"
                                   % (sys.executable, str(stubs / "answers.json")))
        (stubs / "ssh").chmod(0o755)
        records = self.work / "build/hbox-native"
        records.mkdir(parents=True, exist_ok=True)
        for d in runs:
            (records / f"{d.rsplit('/', 1)[-1]}.run").write_text(
                f"box=hbox\ndir={d}\nsource={self.head()}\n")
        return {"PATH": f"{stubs}:{os.environ['PATH']}"}

    def test_green_gate_then_drop_blocks_push_without_an_intervening_gate(self):
        self.launcher_train()
        need = sorted(train.image_modules(["packaging/launcher-decide.sh"]))
        env = self.image_runs({"/s/good": {m: (0, "ok") for m in need}})
        self.assertEqual(self.train("image", "--label", "good", extra_env=env).returncode, 0)
        self.assertEqual(self.gate()[0].returncode, 0)
        t = train.Train(self.work)
        before = t.load()
        origin = self.origin_rev("dev")
        self.assertEqual(self.train("image", "--drop", "good", extra_env=env).returncode, 0)
        self.assertNotIn("image", t.load()["gates"])
        self.assertEqual(t.load()["gates"], {k: v for k, v in before["gates"].items() if k != "image"})
        p = self.train("push")
        self.assertEqual(p.returncode, 2, p.stdout + p.stderr)
        self.assertIn("gate image has not run; push refused", p.stdout)
        self.assertEqual(self.origin_rev("dev"), origin)

    def test_successful_import_and_reread_invalidate_green_image_gate(self):
        self.launcher_train()
        need = sorted(train.image_modules(["packaging/launcher-decide.sh"]))
        self.set_image(need)
        self.assertEqual(self.gate()[0].returncode, 0)
        t = train.Train(self.work)
        for rc, case in ((0, "ok"), (1, "FAIL")):
            with self.subTest(rc=rc):
                env = self.image_runs({"/s/good": {m: (rc, case) for m in need}})
                self.assertEqual(self.train("image", "--label", "good", extra_env=env).returncode, 0)
                self.assertNotIn("image", t.load()["gates"])
                p = self.train("push")
                self.assertEqual(p.returncode, 2, p.stdout)
                self.assertIn("gate image has not run", p.stdout)
                if rc == 0:
                    self.assertEqual(self.gate()[0].returncode, 0)

    def test_refused_import_preserves_cached_gate_and_evidence(self):
        self.launcher_train()
        need = sorted(train.image_modules(["packaging/launcher-decide.sh"]))
        env = self.image_runs({"/s/good": {m: (0, "ok") for m in need}, "/s/duplicate": {need[0]: (0, "ok")}})
        self.assertEqual(self.train("image", "--label", "good", extra_env=env).returncode, 0)
        self.assertEqual(self.gate()[0].returncode, 0)
        t = train.Train(self.work)
        before = t.state_path.read_bytes()
        p = self.train("image", "--label", "duplicate", extra_env=env)
        self.assertEqual(p.returncode, 2, p.stdout)
        self.assertIn("already read from another run", p.stdout)
        self.assertEqual(t.state_path.read_bytes(), before)

    def test_move_of_input_into_docs_refuses_tree_and_source_reuse(self):
        path = "tests/native-probe.lisp"
        (self.work / path).write_text("(value-triple :probe)\n")
        self.commit(self.work, "probe input")
        source = self.head()
        env = self.image_runs({"/s/old": {"tests.test_native_probe": (0, "ok")}})
        (self.work / "docs").mkdir(exist_ok=True)
        (self.work / path).rename(self.work / "docs/native-probe.lisp")
        self.commit(self.work, "move input into docs")
        # Control: normal Git rename detection hides the deleted input.
        normal = sh(self.work, "git", "diff", "--name-only", source, self.head()).stdout.splitlines()
        self.assertEqual(normal, ["docs/native-probe.lisp"])
        record = self.work / "build/hbox-native/old.run"
        for tree, words in ((source, "verdict input(s)"), (self.head(), "image input(s)")):
            with self.subTest(tree=tree):
                record.write_text(f"box=hbox\ndir=/s/old\nsource={source}\ntree={tree}\n")
                before = train.Train(self.work).load()
                p = self.train("image", "--label", "old", extra_env=env)
                self.assertEqual(p.returncode, 2, p.stdout)
                self.assertIn(words, p.stdout)
                self.assertIn(f"first: {path}", p.stdout)
                self.assertEqual(train.Train(self.work).load(), before)

    def test_move_of_input_into_docs_refuses_carried_verdict(self):
        self.launcher_train()
        path = "tests/native-probe.lisp"
        (self.work / path).write_text("(value-triple :probe)\n")
        self.commit(self.work, "probe input")
        need = sorted(train.image_modules(["packaging/launcher-decide.sh"]))
        self.set_image(need)
        self.assertEqual(self.gate()[0].returncode, 0)
        (self.work / "docs").mkdir(exist_ok=True)
        (self.work / path).rename(self.work / "docs/native-probe.lisp")
        self.commit(self.work, "move verdict input into docs")
        g, rec = self.gate()
        self.assertEqual(g.returncode, 1, g.stdout)
        self.assertEqual(rec["rc"], 1)
        self.assertIn(f"first: {path}", rec["error"])

    def test_obligation_diff_keeps_a_book_moved_into_docs(self):
        (self.seed / "books").mkdir(exist_ok=True)
        self.advance_dev({"books/heap-figure.lisp": "(value-triple :heap)\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "origin/dev")
        (self.work / "docs").mkdir(exist_ok=True)
        (self.work / "books/heap-figure.lisp").rename(self.work / "docs/heap-figure.lisp")
        self.commit(self.work, "move heap input into docs")
        changed = train.changed_paths(train.Train(self.work))
        self.assertEqual(changed, ["books/heap-figure.lisp", "docs/heap-figure.lisp"])
        need = train.image_modules(changed, self.work)
        self.assertIn("tests.test_native_heap_from_profile", need)
        self.assertEqual(need["tests.test_native_heap_from_profile"], ["books/heap-figure.lisp"])

    def test_probe_only_train_requires_pin_carry_module(self):
        path = "tests/native_bp_pin_carry.lisp"
        suite = "tests/test_native_bp_pin_carry.py"
        self.advance_dev({path: "(value-triple :old-probe)\n", suite: (REPO / suite).read_text()})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "origin/dev")
        (self.work / path).write_text("(value-triple :new-probe)\n")
        self.commit(self.work, "only the Lisp probe changed")
        self.assertEqual(train.changed_paths(train.Train(self.work)), [path])
        g, rec = self.gate()
        self.assertEqual(g.returncode, 1, g.stdout + g.stderr)
        self.assertEqual(rec["need"], ["tests.test_native_bp_pin_carry"])
        self.assertIn("no image run recorded", rec["error"])
        self.set_image(rec["need"])
        self.assertEqual(self.gate()[0].returncode, 0)

    def test_removing_a_probe_reference_does_not_erase_its_obligation(self):
        path, suite = "tests/shared-probe.lisp", "tests/test_native_probe.py"
        self.advance_dev({path: "old\n", suite: 'probe = "tests/shared-probe.lisp"\n'})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "origin/dev")
        (self.work / path).write_text("new\n")
        (self.work / suite).write_text("probe = None\n")
        self.commit(self.work, "remove probe reference while changing probe")
        self.assertEqual(train.image_modules([path], self.work), {"tests.test_native_probe": [path]})
        (self.work / suite).unlink()
        self.commit(self.work, "delete consumer")
        self.assertEqual(train.image_modules([path, suite], self.work), {"tests.test_native_probe": [path, suite]})

    def test_drop_removes_one_run_without_ssh_and_allows_its_replacement(self):
        self.launcher_train()
        need = sorted(train.image_modules(["packaging/launcher-decide.sh"]))
        replaced = need[0]
        env = self.image_runs({"/s/native-standin": {replaced: (0, "ok")},
                               "/s/native-real": {m: (0, "ok") for m in need[1:]}})
        for label in ("native-standin", "native-real"):
            self.assertEqual(self.train("image", "--label", label, extra_env=env).returncode, 0)
        t = train.Train(self.work)
        before = t.load()
        # The record's label need not match the directory's basename.
        (self.work / "build/hbox-native/standin.run").write_text("box=hbox\ndir=/s/native-standin\n")
        marker = self.tmp / "unexpected-ssh"
        (self.tmp / "stubs/ssh").write_text(f"#!{sys.executable}\nfrom pathlib import Path\nPath({str(marker)!r}).touch()\nraise SystemExit(99)\n")
        p = self.train("image", "--drop", "standin", extra_env=env)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn(f"image dropped standin (/s/native-standin): {replaced}", p.stdout)
        self.assertFalse(marker.exists())
        after = t.load()
        self.assertEqual(after, dict(before, image={"source": self.head(),
                         "runs": {"/s/native-real": "hbox"},
                         "modules": {m: before["image"]["modules"][m] for m in need[1:]}}))
        g, rec = self.gate()
        self.assertNotEqual(g.returncode, 0)
        self.assertEqual(rec["missing"], [replaced])
        state_bytes = t.state_path.read_bytes()
        p = self.train("image", "--drop", "standin", extra_env=env)
        self.assertEqual(p.returncode, 2, p.stdout)
        self.assertIn("no image module entry", p.stdout)
        self.assertEqual(t.state_path.read_bytes(), state_bytes)
        self.assertFalse(marker.exists())
        env = self.image_runs({"/s/replacement": {replaced: (0, "ok")}})
        self.assertEqual(self.train("image", "--label", "replacement", extra_env=env).returncode, 0)
        self.assertEqual(self.gate()[0].returncode, 0)

    def test_drop_with_missing_record_is_local_and_unknown_label_preserves_state(self):
        t = train.Train(self.work)
        st = t.load()
        st["image"] = train.merge_image_run(None, self.head(), "hbox", "/s/native-old", {"a": {"rc": 0, "cases": {"a.T.a": "ok"}}})
        t.save(st)
        # A mocked subprocess proves neither accepted nor refused drops reach ssh.
        for label, rc in (("unknown", 2), ("old", 0)):
            before = t.state_path.read_bytes()
            with mock.patch.object(train.subprocess, "run", side_effect=AssertionError("no subprocess on drop")):
                with mock.patch.object(t, "head", return_value=st["image"]["source"]):
                    with contextlib.redirect_stdout(io.StringIO()) as output:
                        if rc:
                            with self.assertRaisesRegex(train.TrainError, "no recorded image run"):
                                train.cmd_image(t, SimpleNamespace(drop=label))
                        else:
                            self.assertEqual(train.cmd_image(t, SimpleNamespace(drop=label)), 0)
            if rc:
                self.assertEqual(t.state_path.read_bytes(), before)
            else:
                self.assertIn("image dropped old", output.getvalue())
        self.assertEqual(t.load()["image"]["modules"], {})

    def test_image_label_and_drop_are_mutually_exclusive(self):
        p = self.train("image", "--label", "one", "--drop", "two")
        self.assertEqual(p.returncode, 2)
        self.assertIn("not allowed with argument", p.stderr)

    def test_neutral_tree_changes_accept_run_with_or_without_image_reuse(self):
        self.launcher_train()
        built = self.head()
        need = sorted(train.image_modules(["packaging/launcher-decide.sh"]))
        (self.work / "tests/new_helper.py").write_text("value = 1\n")
        self.commit(self.work, "suite differs from image source")
        tree = self.head()
        env = self.image_runs({"/s/reuse": {m: (0, "ok") for m in need}})
        record = self.work / "build/hbox-native/reuse.run"
        (self.work / "docs").mkdir(exist_ok=True)
        (self.work / "docs/image.md").write_text("doc\n")
        (self.work / "planning").mkdir(exist_ok=True)
        (self.work / "planning/image.md").write_text("plan\n")
        self.commit(self.work, "only verdict-neutral changes from run tree")
        for source, tree_line in ((built, f"tree={tree}\n"), (tree, ""), (self.head(), f"tree={tree}\n")):
            with self.subTest(source=source, tree_line=tree_line):
                record.write_text(f"box=hbox\ndir=/s/reuse\nsource={source}\n{tree_line}")
                p = self.train("image", "--label", "reuse", extra_env=env)
                self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
                self.assertIn(f"image run tree {tree} accepted at HEAD {self.head()}", p.stdout)
                st = train.Train(self.work).load()
                self.assertEqual(st["image"]["source"], self.head())
                self.assertEqual(st["image"].get("images_from", {}), {"/s/reuse": source} if source != self.head() else {})
                if source != self.head():
                    self.assertIn(f"reuses the images of {source[:9]}", p.stdout)
                self.assertEqual(self.gate()[0].returncode, 0)

    def test_tree_changes_to_suites_or_host_refuse_before_ssh_even_when_source_is_head(self):
        for path in ("tests/new_helper.py", "host/new-adapter.lisp"):
            with self.subTest(path=path):
                tree = self.head()
                (self.work / path).parent.mkdir(exist_ok=True)
                (self.work / path).write_text("changed\n")
                self.commit(self.work, "non-neutral run tree")
                records = self.work / "build/hbox-native"
                records.mkdir(parents=True, exist_ok=True)
                (records / "old.run").write_text(f"box=hbox\ndir=/s/old\nsource={self.head()}\ntree={tree}\n")
                t = train.Train(self.work)
                before = t.load()
                with mock.patch.object(train.subprocess, "run", wraps=subprocess.run) as run:
                    with contextlib.redirect_stdout(io.StringIO()):
                        with self.assertRaisesRegex(train.TrainError, f"first: {path}"):
                            train.cmd_image(t, SimpleNamespace(label="old"))
                self.assertFalse(any("ssh" in call.args[0] for call in run.call_args_list))
                self.assertEqual(t.load(), before)

    def test_neutral_tree_reuse_still_refuses_an_image_input_changed_from_source(self):
        self.launcher_train()
        built = self.head()
        (self.work / "packaging/launcher-decide.sh").write_text("# new image input\n")
        self.commit(self.work, "changed source input")
        tree = self.head()
        env = self.image_runs({"/s/reuse": {"a": (0, "ok")}})
        (self.work / "docs").mkdir(exist_ok=True)
        (self.work / "docs/image.md").write_text("neutral\n")
        self.commit(self.work, "only neutral tree change")
        (self.work / "build/hbox-native/reuse.run").write_text(f"box=hbox\ndir=/s/reuse\nsource={built}\ntree={tree}\n")
        p = self.train("image", "--label", "reuse", extra_env=env)
        self.assertEqual(p.returncode, 2, p.stdout)
        self.assertIn("first: packaging/launcher-decide.sh", p.stdout)

    def test_image_run_with_unknown_tree_refuses(self):
        env = self.image_runs({"/s/reuse": {"a": (0, "ok")}})
        (self.work / "build/hbox-native/reuse.run").write_text(f"box=hbox\ndir=/s/reuse\nsource={self.head()}\ntree={'f' * 40}\n")
        p = self.train("image", "--label", "reuse", extra_env=env)
        self.assertEqual(p.returncode, 2, p.stdout)
        self.assertIn("its tree fffffffff is not a commit here", p.stdout)

    def test_deleted_bp_adapter_is_derived_from_the_train_base(self):
        path = "host/new-adapter.lisp"
        # Advance the fixture's base with an adapter, then delete it in the train.
        (self.seed / "host").mkdir(exist_ok=True)
        self.advance_dev({path: '(include-book "../books/bp-release")\n'})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "merge", "-q", "origin/dev")
        (self.work / path).write_text('(include-book "../books/store-node")\n')
        self.assertEqual(train.image_modules([path], self.work), {m: [path] for m in train.BP_NATIVES})
        (self.work / path).unlink()
        self.commit(self.work, "delete BP adapter")
        self.assertEqual(train.image_modules([path], self.work), {m: [path] for m in train.BP_NATIVES})

    def test_bp_adapter_gate_uses_its_own_tree_and_requires_the_bp_modules(self):
        path = "host/new-adapter.lisp"
        (self.work / "host").mkdir(exist_ok=True)
        (self.work / path).write_text('(include-book "../books/bp-release")\n')
        self.commit(self.work, "BP adapter")
        g, rec = self.gate()
        self.assertEqual(g.returncode, 1, g.stdout + g.stderr)
        self.assertEqual(rec["need"], sorted(train.BP_NATIVES))
        self.assertIn(path, g.stdout)
        t = train.Train(self.work)
        command = train.lane_check_box_commands(t, t.load()["gates"], [path])["image"]
        self.assertEqual(command[0], "BOX")
        self.assertEqual(command[1].split()[7:], sorted(train.BP_NATIVES))
        self.set_image(train.BP_NATIVES)
        self.assertEqual(self.gate()[0].returncode, 0)

    def test_a_run_on_heads_tree_reuses_a_ready_image_only_when_no_image_input_differs(self):
        self.launcher_train()
        built = self.head()
        (self.work / "planning").mkdir(exist_ok=True)
        (self.work / "planning/notes.md").write_text("n\n")
        (self.work / "tests/more_helper.py").write_text("x = 1\n")
        self.commit(self.work, "planning and a Python suite only")
        need = sorted(train.image_modules(["packaging/launcher-decide.sh"]))
        env = self.image_runs({"/s/reuse": {m: (0, "ok") for m in need}})
        record = self.work / "build/hbox-native/reuse.run"
        record.write_text(f"box=hbox\ndir=/s/reuse\nsource={built}\ntree={self.head()}\n")
        p = self.train("image", "--label", "reuse", extra_env=env)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn(f"reuses the images of {built[:9]}", p.stdout)
        g, rec = self.gate()
        self.assertEqual(g.returncode, 0, g.stdout)
        st = json.loads((self.work / "build/train/integrate__t1.json").read_text())
        self.assertEqual(st["image"]["images_from"], {"/s/reuse": built})
        # an image input changed since the images were built: refused by name
        (self.work / "packaging/launcher-decide.sh").write_text("# decide again\n")
        self.commit(self.work, "launcher again")
        record.write_text(f"box=hbox\ndir=/s/reuse\nsource={built}\ntree={self.head()}\n")
        p = self.train("image", "--label", "reuse", extra_env=env)
        self.assertEqual(p.returncode, 2, p.stdout)
        self.assertIn("1 image input(s) differ", p.stdout)
        self.assertIn("packaging/launcher-decide.sh", p.stdout)
        # a run whose tree is not HEAD is refused as before
        record.write_text(f"box=hbox\ndir=/s/reuse\nsource={built}\ntree={built}\n")
        p = self.train("image", "--label", "reuse", extra_env=env)
        self.assertEqual(p.returncode, 2, p.stdout)
        self.assertIn(f"not HEAD {self.head()[:9]}", p.stdout)

    def test_the_obliged_set_may_span_two_runs_at_head(self):
        self.launcher_train()
        need = sorted(train.image_modules(["packaging/launcher-decide.sh"]))
        heap = "tests.test_native_heap_from_profile"
        env = self.image_runs({"/s/main": {m: (0, "ok") for m in need if m != heap},
                               "/s/2gb": {heap: (0, "ok")}})
        for label in ("main", "2gb"):
            p = self.train("image", "--label", label, extra_env=env)
            self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        g, rec = self.gate()
        self.assertEqual(g.returncode, 0, g.stdout)
        self.assertEqual((rec["missing"], rec["runs"]), ([], ["/s/2gb", "/s/main"]))
        # a third run that repeats a module is refused and changes nothing
        env = self.image_runs({"/s/main": {}, "/s/2gb": {}, "/s/again": {heap: (1, "FAIL")}})
        p = self.train("image", "--label", "again", extra_env=env)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("already read from another run at HEAD", p.stdout)
        g, rec = self.gate()
        self.assertEqual(g.returncode, 0, g.stdout)


class RunIdentityTests(TrainBase):
    """Generation checks at both result-import boundaries; ssh is mocked."""

    def run_record(self, metadata):
        t = train.Train(self.work)
        head = self.head()
        path = self.work / "build/hbox-native/run.run"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"box=hbox\ndir=/s/run\nsource={head}\ntree={head}\n" + metadata)
        st = t.load()
        st["image"] = {"source": head, "runs": {}, "modules": {}}
        st["census"] = {"source": "unchanged"}
        st["gates"] = {"image": {"head": head, "rc": 0}, "other": {"rc": 0}}
        t.save(st)
        return t, head

    def results(self, command):
        if command == train.cmd_image:
            return ('RC tests.test_native_probe 0\nFN_TEST_BUDGET_RESULT '
                    + json.dumps({"module": "tests.test_native_probe", "cases": [["probe.T.ok", "ok"]]}) + "\n")
        return train.CENSUS_DONE + "\nCENSUS-LINE\n" + CensusTests.LINE

    def test_pending_image_and_census_records_refuse_before_ssh(self):
        for command in (train.cmd_image, train.cmd_census):
            with self.subTest(command=command.__name__):
                t, head = self.run_record("launch_id=new-generation\n")
                before = t.state_path.read_bytes()
                with mock.patch.object(t, "head", return_value=head), mock.patch.object(train.subprocess, "run") as ssh:
                    with self.assertRaisesRegex(train.TrainError, "pending; adopt: tools/hbox_native.sh adopt run"):
                        command(t, SimpleNamespace(label="run"))
                ssh.assert_not_called()
                self.assertEqual(t.state_path.read_bytes(), before)

    def test_mismatched_missing_and_duplicate_identities_preserve_state(self):
        for command in (train.cmd_image, train.cmd_census):
            for identity in ("TRAIN-RUN-IDENTITY old-generation 1 2 scope\n", "",
                             "TRAIN-RUN-IDENTITY new-generation 1 2 scope\n" * 2):
                with self.subTest(command=command.__name__, identity=identity):
                    t, head = self.run_record("launch_id=new-generation\npgid=42\n")
                    before = t.state_path.read_bytes()
                    result = subprocess.CompletedProcess([], 0, identity + self.results(command), "")
                    with mock.patch.object(t, "head", return_value=head), mock.patch.object(train.subprocess, "run", return_value=result) as ssh:
                        with self.assertRaisesRegex(train.TrainError, "run.identity launch_id.*expected 'new-generation'"):
                            command(t, SimpleNamespace(label="run"))
                    self.assertIn("run.identity", ssh.call_args.args[0][-1])
                    self.assertEqual(t.state_path.read_bytes(), before)

    def test_matching_identity_imports_image_and_census(self):
        for command in (train.cmd_image, train.cmd_census):
            with self.subTest(command=command.__name__):
                t, head = self.run_record("launch_id=new-generation\npgid=42\npid=43\nstarttime=99\n")
                result = subprocess.CompletedProcess([], 0, "TRAIN-RUN-IDENTITY new-generation 43 99 scope\n" + self.results(command), "")
                with mock.patch.object(t, "head", return_value=head), mock.patch.object(train.subprocess, "run", return_value=result) as ssh:
                    with contextlib.redirect_stdout(io.StringIO()):
                        self.assertEqual(command(t, SimpleNamespace(label="run")), 0)
                self.assertIn("run.identity", ssh.call_args.args[0][-1])
                st = t.load()
                if command == train.cmd_image:
                    self.assertEqual(st["image"]["modules"]["tests.test_native_probe"]["rc"], 0)
                    self.assertNotIn("image", st["gates"])
                    self.assertEqual(st["census"], {"source": "unchanged"})
                else:
                    self.assertEqual(st["census"]["figures"]["units"], 23068)
                    self.assertEqual(st["census"]["source"], head)
                    self.assertIn("image", st["gates"])

    def test_older_launcher_records_keep_their_identity_free_behavior(self):
        for command in (train.cmd_image, train.cmd_census):
            with self.subTest(command=command.__name__):
                t, head = self.run_record("pid=43\n")
                result = subprocess.CompletedProcess([], 0, self.results(command), "")
                with mock.patch.object(t, "head", return_value=head), mock.patch.object(train.subprocess, "run", return_value=result) as ssh:
                    with contextlib.redirect_stdout(io.StringIO()):
                        self.assertEqual(command(t, SimpleNamespace(label="run")), 0)
                self.assertNotIn("run.identity", ssh.call_args.args[0][-1])


if __name__ == "__main__":
    unittest.main()

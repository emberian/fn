"""Tests for tools/train.py against a throwaway origin + batch worktree with stub tools.

TRAIN_SCRIPT may point at an alternative copy of train.py (used to show a test
red against a variant that skips a rule).
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

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
if mode == "write" and name == "ledger":
    with open("planning/proofs.json", "a") as f:
        f.write("regen\\n")
sys.exit(int(os.environ.get("STUB_RC_%s_%s" % (name, mode), "0")))
'''
STUBS = ["tools/ledger.py", "tools/current_view.py", "tools/host_check.py",
         "tools/lock_discipline_check.py",
         "tools/secrets_check.py", "planning/repair/repair.py",
         "tools/main_last_check.py", "tools/interface_emit.py", "tools/extract/world.py",
         "tests/test_ledger.py", "tests/test_keystone_emit.py", "tests/test_train.py",
         "tests/test_farm.py", "tests/test_current_view.py", "tools/keystone_emit.py",
         "tests/test_keystone_critical.py", "tools/harness_check.py"]
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
    p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, env=env)
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
        (self.seed / "tools/remote_check.sh").write_text(REMOTE_STUB)
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
                               "keystone_emit --write-manifest"])
        subj = sh(self.work, "git", "log", "-1", "--format=%s").stdout
        self.assertTrue(subj.startswith("Regenerate train 1"), subj)

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
        for word in ("--affected-by books/b", "--timeout-seconds 1800",
                     "submit hbox", "books/wire-export", "books/image-world", "books/image-world-dtn",
                     "books/b", "tests/acl2/t"):
            self.assertIn(word, sub)
        # the affected closure, never the lane selection (direct includers)
        self.assertNotIn("--lane", sub.split())
        self.assertNotIn("books/b.lisp", sub)
        self.assertTrue(farm[1].startswith("farm --root") or "wait hbox run-stub-1" in farm[1], farm[1])
        self.assertNotIn("remote_check", " ".join(self.stub_log()))

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
        self.assertEqual(words.count("tests/acl2/special-witness"), 1)
        self.assertNotIn("tests/acl2/unrelated-witness", words)
        self.assertNotIn("tests/acl2/noncritical-witness", words)

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

class ImageModuleTests(unittest.TestCase):
    """The image gate's pure half: which modules a diff obliges, the box's
    lines parsed, and the verdict."""

    HEAD = "a" * 40

    def ran(self, modules, source=None):
        return {"source": source or self.HEAD, "dir": "/box/run",
                "modules": {m: {"rc": 0, "cases": {m + ".T.test_ok": "ok"}} for m in modules}}

    def test_a_launcher_change_obliges_the_served_natives_operator_verbs_and_heap_from_profile(self):
        need = train.image_modules(["packaging/launcher-decide.sh", "README.md"])
        self.assertEqual(set(need), {"tests.test_native_operator_verbs",
                                     "tests.test_native_heap_from_profile", *train.SERVED_NATIVES})
        self.assertIn("tests.test_native_served_line_stack", need)
        self.assertEqual(need["tests.test_native_owner"], ["packaging/launcher-decide.sh"])

    def test_heap_probe_and_host_native_oblige_and_unrelated_paths_do_not(self):
        self.assertTrue(train.image_modules(["books/heap-figure.lisp"]))
        self.assertTrue(train.image_modules(["host/native/admin.lisp"]))
        self.assertTrue(train.image_modules(["tools/extract/core_launcher.py"]))
        self.assertEqual(train.image_modules(["host/owner-host.lisp", "tools/train.py",
                                              "books/heap-figure-tests.lisp", "packaging/fn.md"]), {})

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

    def test_a_module_whose_every_test_skipped_passes_and_is_listed(self):
        need = train.image_modules(["packaging/fn"])
        run = self.ran(need)
        run["modules"]["tests.test_native_over_window"] = {"rc": 4, "cases": {}}
        rc, rec = train.image_verdict(need, run, self.HEAD, [])
        self.assertEqual((rc, rec["skipped"]), (0, ["tests.test_native_over_window"]))

    def test_a_failed_module_with_no_case_recorded_refuses(self):
        need = train.image_modules(["packaging/fn"])
        run = self.ran(need)
        run["modules"]["tests.test_native_owner"] = {"rc": 137, "cases": {}}
        rc, rec = train.image_verdict(need, run, self.HEAD, [])
        self.assertEqual(rc, 1)
        self.assertEqual(rec["unexplained"], ["tests.test_native_owner (rc 137, no case recorded)"])

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

    def set_image(self, modules):
        path = self.work / "build/train/integrate__t1.json"
        st = json.loads(path.read_text()) if path.exists() else {"lanes": []}
        st["image"] = {"source": self.head(), "box": "hbox", "dir": "/r",
                       "modules": {m: {"rc": 0, "cases": {m + ".T.a": "ok"}} for m in modules}}
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(st))

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


if __name__ == "__main__":
    unittest.main()

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
name = os.path.basename(sys.argv[0])[:-3]
args = [a for a in sys.argv[1:]]
mode = args[0].lstrip("-") if args else ""
with open(os.environ["STUB_LOG"], "a") as f:
    f.write(name + " " + " ".join(args) + "\\n")
if name == "lock_discipline_check":
    keys = json.load(open("lockkeys.json"))
    # the checker's current shape: `new` is a list of key strings
    print(json.dumps({"new": list(keys), "stale": []}))
    sys.exit(0)
if mode == "write" and name == "ledger":
    with open("planning/proofs.json", "a") as f:
        f.write("regen\\n")
sys.exit(int(os.environ.get("STUB_RC_%s_%s" % (name, mode), "0")))
'''
STUBS = ["tools/ledger.py", "tools/current_view.py", "tools/host_check.py",
         "tools/lock_discipline_check.py",
         "tools/secrets_check.py", "planning/repair/repair.py",
         "tools/main_last_check.py", "tools/interface_emit.py", "tools/extract/world.py",
         "tools/build_lists_check.py"]
REMOTE_STUB = '''#!/bin/sh
echo "remote_check $*" >> "$STUB_LOG"
for out in planning/interfaces.json specs/wire-grammar.json; do
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
  for out in planning/interfaces.json specs/wire-grammar.json; do
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
        (self.seed / ".gitignore").write_text("build/\n")
        (self.seed / "lockkeys.json").write_text("[]\n")
        (self.seed / "src.txt").write_text("a\nb\nc\n")
        (self.seed / "specs").mkdir(exist_ok=True)
        (self.seed / "specs/wire-grammar.json").write_text("base\n")
        (self.seed / "planning/evidence-index.tsv").write_text("e0\n")
        (self.seed / "planning/decisions.md").write_text("d0\n")
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
        sha = self.lane("a", {"specs/wire-grammar.json": "lane version\n", "src.txt": "a\nb\nc\nlane\n"})
        self.advance_dev({"specs/wire-grammar.json": "dev version\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
        p = self.train("merge", f"a@{sha}")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual((self.work / "specs/wire-grammar.json").read_text(), "dev version\n")
        self.assertIn("lane", (self.work / "src.txt").read_text())
        parents = sh(self.work, "git", "rev-list", "--parents", "-n1", "HEAD").stdout.split()
        self.assertEqual(len(parents), 3, "expected a merge commit")
        self.assertIn(f"Merge lane/a @{sha} into integrate/t1", sh(self.work, "git", "log", "-1", "--format=%s").stdout)

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

    def test_evidence_index_union_keeps_both_sides_and_dedupes(self):
        a = self.lane("a", {"planning/evidence-index.tsv": "e0\nshared\nfrom-a\n",
                            "planning/decisions.md": "d0\nda\n"})
        self.advance_dev({"planning/evidence-index.tsv": "e0\nshared\nfrom-dev\n",
                          "planning/decisions.md": "d0\ndd\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
        p = self.train("merge", f"a@{a}")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        lines = (self.work / "planning/evidence-index.tsv").read_text().splitlines()
        self.assertEqual(sorted(lines), ["e0", "from-a", "from-dev", "shared"])
        dec = (self.work / "planning/decisions.md").read_text()
        self.assertIn("da", dec)
        self.assertIn("dd", dec)


class RegenTests(TrainBase):
    def test_regen_order_is_fixed_and_cites_nothing(self):
        p = self.train("regen")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        log = [l.split()[0] + " " + (l.split()[1] if len(l.split()) > 1 else "") for l in self.stub_log()]
        self.assertEqual(log, ["ledger --write"])
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

    def test_lock_delta_warns_but_does_not_block_unless_strict(self):
        self.ready()
        sh(self.work, "git", "checkout", "-q", "-B", "integrate/t1")
        (self.work / "lockkeys.json").write_text('["k1"]\n')
        self.commit(self.work, "adds a lock key")
        g = self.train("gate")
        self.assertEqual(g.returncode, 0, g.stdout)
        self.assertIn("WARNING", g.stdout)
        self.assertIn("k1", g.stdout)
        self.assertNotEqual(self.train("gate", "--strict-lock").returncode, 0)

    def test_host_load_runs_only_when_host_changed(self):
        self.ready()
        self.train("gate")
        self.assertNotIn("host_check --load", self.stub_log())
        (self.work / "host").mkdir()
        (self.work / "host/x.c").write_text("x\n")
        self.commit(self.work, "host change")
        self.train("gate")
        self.assertIn("host_check --load", self.stub_log())

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
        for check in ("interface_emit --check", "world --check", "build_lists_check", "host_check --read",
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

    def test_boxstep_records_and_commits_the_emits_then_the_gate_passes_at_head(self):
        (self.seed / "books").mkdir(exist_ok=True)
        self.merge({"books/b.lisp": "changed\n"})
        self.assertNotEqual(self.train("gate").returncode, 0)
        b = self.train("boxstep", "persvati", extra_env={"STUB_EMIT": "emitted"})
        self.assertEqual(b.returncode, 0, b.stdout + b.stderr)
        self.assertEqual(self.box()["sha"], self.head())
        self.assertEqual((self.work / "planning/interfaces.json").read_text(), "emitted\n")
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
        for word in ("--lane", "--affected-by books/b", "--timeout-seconds 1800",
                     "submit hbox", "books/wire-export", "books/b", "tests/acl2/t"):
            self.assertIn(word, sub)
        self.assertNotIn("books/b.lisp", sub)
        self.assertTrue(farm[1].startswith("farm --root") or "wait hbox run-stub-1" in farm[1], farm[1])
        self.assertNotIn("remote_check", " ".join(self.stub_log()))

    def test_certify_emits_in_the_run_tree_commits_and_records_the_split(self):
        self.books_train()
        c = self.train("certify", "hbox")
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)
        ssh = [l for l in self.stub_log() if l.startswith("ssh ")]
        self.assertEqual(len(ssh), 1, ssh)
        for word in (str(self.ftree), "timeout", "swarm-build", "interface_emit.py --write --check",
                     "protocol_emit.py --wire --check", "host_check.py --world"):
            self.assertIn(word, ssh[0])
        self.assertNotIn("certify_books", ssh[0])
        self.assertEqual((self.work / "planning/interfaces.json").read_text(), "emitted\n")
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

    def test_a_books_free_train_certifies_wire_export_alone(self):
        self.merge({"tools/x.py": "x\n"})
        c = self.train("certify", "hbox")
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)
        sub = [l for l in self.stub_log() if l.startswith("farm") and " submit " in l][0]
        self.assertNotIn("--lane", sub)
        self.assertNotIn("--affected-by", sub)
        self.assertTrue(sub.endswith("submit hbox books/wire-export"), sub)

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


if __name__ == "__main__":
    unittest.main()

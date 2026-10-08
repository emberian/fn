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
if mode == "write" and name in ("ledger", "current_view"):
    with open("planning/%s.out" % name, "a") as f:
        f.write("regen\\n")
if name == "repair" and "report" in args:
    with open("planning/repair/STATUS.md", "a") as f:
        f.write("regen\\n")
sys.exit(int(os.environ.get("STUB_RC_%s_%s" % (name, mode), "0")))
'''
STUBS = ["tools/ledger.py", "tools/current_view.py", "tools/host_check.py",
         "tools/evidence_manifests.py", "tools/lock_discipline_check.py",
         "tools/secrets_check.py", "planning/repair/repair.py",
         "tools/main_last_check.py", "tools/interface_emit.py", "tools/extract/world.py"]
REMOTE_STUB = '''#!/bin/sh
echo "remote_check $*" >> "$STUB_LOG"
for out in planning/interfaces.json specs/wire-grammar.json; do
  [ -n "$STUB_EMIT" ] && mkdir -p "$(dirname $out)" && echo "$STUB_EMIT" > "$out"
done
exit "${STUB_RC_remote_check:-0}"
'''


def sh(cwd, *argv, env=None, check=True):
    p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, env=env)
    if check and p.returncode != 0:
        raise AssertionError(f"{argv} rc {p.returncode}\n{p.stdout}\n{p.stderr}")
    return p


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
        (self.seed / "planning/ledger.json").write_text("base\n")
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
        sha = self.lane("a", {"planning/ledger.json": "lane version\n", "src.txt": "a\nb\nc\nlane\n"})
        self.advance_dev({"planning/ledger.json": "dev version\n"})
        sh(self.work, "git", "fetch", "-q", "origin")
        sh(self.work, "git", "reset", "-q", "--hard", "origin/dev")
        p = self.train("merge", f"a@{sha}")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual((self.work / "planning/ledger.json").read_text(), "dev version\n")
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
    def test_cite_runs_before_ledger_and_order_is_fixed(self):
        (self.tmp / "src" / "build" / "acl2" / "certify-x").mkdir(parents=True)
        p = self.train("regen", "--cite", "certify-x", "--cite-from", str(self.tmp / "src"))
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        log = [l.split()[0] + " " + (l.split()[1] if len(l.split()) > 1 else "") for l in self.stub_log()]
        self.assertEqual(log, ["evidence_manifests add", "ledger --write", "current_view --write", "repair report"])
        self.assertTrue((self.work / "build/acl2/certify-x").is_dir())
        subj = sh(self.work, "git", "log", "-1", "--format=%s").stdout
        self.assertTrue(subj.startswith("Regenerate train 1"), subj)

    def test_regen_failure_stops_the_train(self):
        p = self.train("regen", extra_env={"STUB_RC_current_view_write": "1"})
        self.assertNotEqual(p.returncode, 0)
        self.assertNotIn("repair report", self.stub_log())


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


if __name__ == "__main__":
    unittest.main()

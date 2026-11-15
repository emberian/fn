"""No-server controls for author-world identity and startup cleanup."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("scoped_author", ROOT / "tools/scoped_app_author.py")
author = importlib.util.module_from_spec(spec)
spec.loader.exec_module(author)


class AuthorIdentity(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "tools").mkdir()
        (self.root / "books").mkdir()
        (self.root / "tools/proof_repl.py").write_text("pinned tool\n")
        (self.root / "books/warm.lisp").write_text("original parent\n")
        self.binding = {"sha256": author.digest(self.root / "books/warm.lisp"), "key": "original-key"}
        self.plan = {"source_commit": "fixture", "qualified": ["books/warm"],
                     "books": {"books/warm": dict(self.binding)}, "source_order": [],
                     "entry_roots": ["books/warm"],
                     "proof_repl_sha256": author.digest(self.root / "tools/proof_repl.py")}
        self.state = {"session": "fixture", "passed": {},
                      "qualified_bindings": {"books/warm": dict(self.binding)},
                      "proof_repl_sha256": self.plan["proof_repl_sha256"]}
        self.state_path = self.root / "state.json"
        self.root_patch = patch.object(author, "ROOT", self.root)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)

    def refused_before_rpc(self, plan, state):
        self.state_path.write_text(json.dumps(state))
        with patch.object(author, "same_server") as status, patch.object(author, "invoke") as invoke:
            with self.assertRaises((AssertionError, KeyError)):
                author.replay(plan, self.state_path, "fixture", self.root, float("inf"))
            status.assert_not_called()
            invoke.assert_not_called()

    def test_changed_warm_parent_cannot_be_relabelled_by_new_plan(self):
        (self.root / "books/warm.lisp").write_text("replacement parent\n")
        self.plan["books"]["books/warm"]["sha256"] = author.digest(self.root / "books/warm.lisp")
        self.refused_before_rpc(self.plan, self.state)

    def test_missing_initial_bindings_refuse_before_rpc(self):
        del self.state["qualified_bindings"]
        self.refused_before_rpc(self.plan, self.state)

    def test_warm_set_cannot_gain_or_lose_loaded_books(self):
        for qualified in ([], ["books/warm", "books/never-loaded"]):
            with self.subTest(qualified=qualified):
                plan = copy.deepcopy(self.plan)
                plan["qualified"] = qualified
                self.refused_before_rpc(plan, self.state)

    def test_replaced_server_refuses_before_status_rpc(self):
        self.state["server"] = {"pid": 101, "started_at": 1, "start_ticks": 2}
        pr = types.SimpleNamespace(read_state=Mock(return_value={"pid": 102, "started_at": 1}), ask=Mock())
        with patch.dict(sys.modules, {"proof_repl": pr}):
            with self.assertRaises(AssertionError):
                author.same_server(self.state)
        pr.ask.assert_not_called()

    def run_fake_start(self, existing=False):
        plan_path = self.root / "plan.json"
        plan_path.write_text(json.dumps(self.plan))
        session_dir = self.root / "session"
        if existing:
            session_dir.mkdir()
        scope = self.root / "cgroup/test"
        scope.mkdir(parents=True)
        (scope / "memory.max").write_text("6442450944")
        (scope / "memory.swap.max").write_text("0")
        proc = self.root / "proc-cgroup"
        proc.write_text("0::/test\n")
        def paths(value):
            return {"/proc/self/cgroup": proc, "/sys/fs/cgroup": self.root / "cgroup"}.get(str(value), Path(value))
        calls = []
        def invoke(args, *_):
            calls.append(args[0])
            if args[0] == "start":
                raise subprocess.TimeoutExpired("fake-start", 1)
            return 0
        pr = types.SimpleNamespace(session_dir=lambda _: session_dir)
        argv = ["author", "campaign", "--plan", str(plan_path), "--state", str(self.state_path),
                "--logs", str(self.root / "logs"), "--session", "fixture",
                "--queue", str(self.root / "queue"), "--seconds", "1"]
        expected = AssertionError if existing else subprocess.TimeoutExpired
        with patch.dict(sys.modules, {"proof_repl": pr}), patch.object(sys, "argv", argv), \
             patch.object(author, "validate"), patch.object(author, "invoke", side_effect=invoke), \
             patch.object(author, "Path", side_effect=paths), patch.object(author.signal, "signal"):
            with self.assertRaises(expected):
                author.main()
        return calls

    def test_start_timeout_stops_the_new_owned_session(self):
        self.assertEqual(self.run_fake_start(), ["start", "stop"])

    def test_existing_session_is_neither_started_nor_stopped(self):
        self.assertEqual(self.run_fake_start(existing=True), [])


if __name__ == "__main__":
    unittest.main()

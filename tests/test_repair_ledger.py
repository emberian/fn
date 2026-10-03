"""planning/repair/repair.py: the claim/verify guardrails refuse what they should."""
import json, os, shutil, subprocess, sys, tempfile, unittest

TOOL = os.path.join(os.path.dirname(__file__), "..", "planning", "repair", "repair.py")


def sh(cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, shell=True, capture_output=True, text=True)


class RepairVerifyTests(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.mkdtemp(prefix="repair-test-")
        r = self.d
        os.makedirs(f"{r}/planning/repair/items")
        shutil.copy(TOOL, f"{r}/planning/repair/repair.py")
        with open(f"{r}/planning/repair/forbidden.txt", "w") as f:
            f.write("host/native/owner.lisp\n")
        with open(f"{r}/planning/repair/items/T1.json", "w") as f:
            json.dump({"id": "T1", "state": "open", "title": "t", "notes": []}, f)
        os.makedirs(f"{r}/src")
        with open(f"{r}/src/a.py", "w") as f:
            f.write("X = 1\n")
        sh("git init -q && git add -A && git -c user.email=t@t -c user.name=t commit -q -m base", r)
        self.base = sh("git rev-parse HEAD", r).stdout.strip()
        self.tool = [sys.executable, f"{r}/planning/repair/repair.py"]

    def tearDown(self):
        shutil.rmtree(self.d, ignore_errors=True)

    def run_tool(self, *args):
        return subprocess.run(self.tool + list(args), cwd=self.d, capture_output=True, text=True)

    def commit(self, path, text, msg):
        os.makedirs(os.path.dirname(f"{self.d}/{path}"), exist_ok=True)
        with open(f"{self.d}/{path}", "w") as f:
            f.write(text)
        sh(f"git add -A && git -c user.email=t@t -c user.name=t commit -q -m '{msg}'", self.d)

    def test_a_good_fix_verifies(self):
        self.run_tool("claim", "T1", "--files", "src/*.py",
                      "--test", "python3 -c 'import sys; sys.path.insert(0,\"src\"); import a; assert a.X == 2'")
        self.commit("src/a.py", "X = 2\n", "T1: fix X")
        r = self.run_tool("verify", "T1", "--base", self.base)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_outside_scope_is_refused(self):
        self.run_tool("claim", "T1", "--files", "src/a.py")
        self.commit("src/b.py", "Y = 1\n", "T1: stray file")
        r = self.run_tool("verify", "T1", "--base", self.base)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("outside the claimed scope", r.stdout)

    def test_forbidden_zone_is_refused(self):
        self.run_tool("claim", "T1", "--files", "host/native/*")
        self.commit("host/native/owner.lisp", "(x)\n", "T1: touch owner")
        r = self.run_tool("verify", "T1", "--base", self.base)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("forbidden zone", r.stdout)

    def test_a_test_that_passes_at_base_is_refused(self):
        self.run_tool("claim", "T1", "--files", "src/*.py", "--test", "true")
        self.commit("src/a.py", "X = 2\n", "T1: fix")
        r = self.run_tool("verify", "T1", "--base", self.base)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("PASSES at the base", r.stdout)

    def test_over_budget_and_unnamed_commit_are_refused(self):
        self.run_tool("claim", "T1", "--files", "src/*.py", "--budget", "3")
        self.commit("src/a.py", "".join(f"X{i} = {i}\n" for i in range(10)), "no id here")
        r = self.run_tool("verify", "T1", "--base", self.base)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("over the budget", r.stdout)
        self.assertIn("no commit", r.stdout)


if __name__ == "__main__":
    unittest.main()

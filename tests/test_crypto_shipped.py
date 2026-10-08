"""tools/crypto_shipped.py: the D64 transformation (fn ships its own OpenSSL 3.5.8).

Two layers.  The engine is tested on a tiny rules file and a temporary tree
with the expected diff written out literally.  The rules table is tested on
every real rule in tools/crypto_shipped.json, each in a one-file temporary tree
holding its own old text between filler lines: the kind's detector finds the
site, the dry-run diff is exactly old -> new, apply is idempotent (a second
dry-run is empty), the detector no longer fires, and check fails before and
passes after.  LANDED is the ratchet: the profiles whose rewrite is committed
in this tree, which `check` must pass on the real files.
"""
import difflib
import io
import json
import re
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import crypto_shipped as cs  # noqa: E402

LANDED = ("linux", "boxes", "macos", "tests")

MINI = {
    "profiles": {"linux": {"desc": "x"}, "docs": {"desc": "x", "requires_flag": "--after-tls"}},
    "kinds": {
        "sys-pair": {"profile": "linux", "desc": "d", "files": ["pkg/*.sh"], "pattern": "system pair"},
        "tank": {"profile": "linux", "desc": "d", "files": ["pkg/*.sh"], "pattern": "/tank/x"},
        "prose": {"profile": "docs", "desc": "d", "files": ["docs/*.md"], "pattern": "system's TLS"},
    },
    "rules": [
        {"id": "r1", "kind": "sys-pair", "file": "pkg/a.sh", "old": ["# falls back to the system pair"],
         "new": ["# no fallback"]},
        {"id": "r2", "kind": "tank", "file": "pkg/a.sh", "old": ["p=${P:-/tank/x}"],
         "new": ["p=${P:?}"]},
        {"id": "r3", "kind": "prose", "file": "docs/i.md", "old": ["the system's TLS library."],
         "new": ["its own OpenSSL."]},
    ],
    "allow": [{"file": "pkg/floor.sh", "pattern": "/tank/x", "reason": "documents the build box"}],
    "owed": [{"profile": "linux", "owner": "P", "file": "books/b.lisp", "pattern": "decide",
              "reason": "owed: books (P)"}],
}
FILES = {
    "pkg/a.sh": "set -e\n# falls back to the system pair\np=${P:-/tank/x}\necho $p\n",
    "pkg/floor.sh": "# built into /tank/x\n",
    "docs/i.md": "The release brings the system's TLS library.\n",
    "books/b.lisp": "(defun decide ())\n",
}


def write_tree(base: Path, files: dict) -> None:
    for rel, text in files.items():
        (base / rel).parent.mkdir(parents=True, exist_ok=True)
        (base / rel).write_text(text)


def run(root: Path, rules: Path, *argv):
    out, err = io.StringIO(), io.StringIO()
    code = cs.main(["--root", str(root), "--rules", str(rules), *argv], out=out, err=err)
    return code, out.getvalue(), err.getvalue()


class EngineTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "tree"
        write_tree(self.root, FILES)
        self.rules = Path(self.tmp.name) / "rules.json"
        self.rules.write_text(json.dumps(MINI))

    def test_plan_lists_each_site_with_its_rewrite_and_its_owner(self):
        code, out, _ = run(self.root, self.rules, "plan", "--profile", "linux")
        self.assertEqual(code, 0)
        self.assertIn("rule  pending  sys-pair", out)
        self.assertIn("site  sys-pair                     pkg/a.sh:2  UNHANDLED", out)
        self.assertIn("site  tank                         pkg/a.sh:3  UNHANDLED", out)
        self.assertIn("allow: documents the build box", out)
        self.assertIn("owed-linux", out)
        self.assertNotIn("docs/i.md", out)

    def test_dry_run_diff_is_exactly_the_rewrite_and_writes_nothing(self):
        code, out, _ = run(self.root, self.rules, "apply", "--profile", "linux", "--dry-run")
        self.assertEqual(code, 0)
        expected = "".join(difflib.unified_diff(
            FILES["pkg/a.sh"].splitlines(True),
            "set -e\n# no fallback\np=${P:?}\necho $p\n".splitlines(True), "a/pkg/a.sh", "b/pkg/a.sh"))
        self.assertEqual(out, expected)
        self.assertEqual((self.root / "pkg/a.sh").read_text(), FILES["pkg/a.sh"])

    def test_apply_is_idempotent_and_check_goes_from_fail_to_ok(self):
        code, out, _ = run(self.root, self.rules, "check", "--profile", "linux")
        self.assertEqual(code, 1, out)
        self.assertIn("owed: P", out)
        self.assertEqual(run(self.root, self.rules, "apply", "--profile", "linux")[0], 0)
        self.assertEqual((self.root / "pkg/a.sh").read_text(), "set -e\n# no fallback\np=${P:?}\necho $p\n")
        self.assertEqual(run(self.root, self.rules, "apply", "--profile", "linux", "--dry-run")[1], "")
        code, out, _ = run(self.root, self.rules, "check", "--profile", "linux")
        self.assertEqual(code, 0, out)
        self.assertIn("owed: P", out)
        self.assertEqual(run(self.root, self.rules, "check", "--profile", "linux", "--strict")[0], 1)

    def test_profile_limits_the_rewrite(self):
        run(self.root, self.rules, "apply", "--profile", "linux")
        self.assertEqual((self.root / "docs/i.md").read_text(), FILES["docs/i.md"])

    def test_a_profile_that_states_the_end_state_needs_its_flag(self):
        code, _out, err = run(self.root, self.rules, "apply", "--profile", "docs")
        self.assertEqual(code, 2)
        self.assertIn("--after-tls", err)
        self.assertEqual((self.root / "docs/i.md").read_text(), FILES["docs/i.md"])
        self.assertEqual(run(self.root, self.rules, "apply", "--profile", "docs", "--after-tls")[0], 0)
        self.assertEqual((self.root / "docs/i.md").read_text(), "The release brings its own OpenSSL.\n")

    def test_default_profiles_leave_out_the_flagged_one(self):
        run(self.root, self.rules, "apply")
        self.assertEqual((self.root / "docs/i.md").read_text(), FILES["docs/i.md"])

    def test_drift_stops_the_run_and_writes_nothing(self):
        (self.root / "pkg/a.sh").write_text("# something else entirely\np=${P:-/tank/x}\n")
        code, _out, err = run(self.root, self.rules, "apply", "--profile", "linux")
        self.assertEqual(code, 3)
        self.assertIn("drift: [r1]", err)
        self.assertEqual((self.root / "pkg/a.sh").read_text(), "# something else entirely\np=${P:-/tank/x}\n")

    def test_a_new_unhandled_site_fails_check(self):
        run(self.root, self.rules, "apply", "--profile", "linux")
        (self.root / "pkg/new.sh").write_text("# the system pair again\n")
        code, out, _ = run(self.root, self.rules, "check", "--profile", "linux")
        self.assertEqual(code, 1)
        self.assertIn("FAIL  sys-pair pkg/new.sh:1", out)

    def test_an_unknown_profile_is_refused(self):
        with self.assertRaises(SystemExit):
            run(self.root, self.rules, "plan", "--profile", "windows")


class RulesTableTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(cs.RULES.read_text())

    def one_rule_tree(self, rule, base):
        kind = self.data["kinds"][rule["kind"]]
        data = {"profiles": self.data["profiles"], "kinds": {rule["kind"]: kind},
                "rules": [rule], "allow": [], "owed": []}
        rules = base / "rules.json"
        rules.write_text(json.dumps(data))
        root = base / "tree"
        old = "\n".join(rule["old"])
        write_tree(root, {rule["file"]: "filler one\n" + old + "\nfiller two\n"})
        return root, rules, kind["profile"]

    def test_every_rule_is_a_rewrite_of_its_kinds_site(self):
        for rule in self.data["rules"]:
            with self.subTest(rule=rule["id"]), tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp)
                kind = self.data["kinds"][rule["kind"]]
                self.assertTrue(any(Path(rule["file"]).match(g) for g in kind["files"]),
                                "the rule's file is outside its kind's files")
                self.assertNotEqual(rule["old"], rule["new"])
                root, rules, profile = self.one_rule_tree(rule, base)
                before = (root / rule["file"]).read_text()
                pattern = re.compile(kind["pattern"])
                fires = any(pattern.search(x) for x in rule["old"])
                self.assertTrue(fires or any(
                    any(pattern.search(x) for x in other["old"])
                    for other in self.data["rules"] if other["kind"] == rule["kind"]),
                    "the detector fires on no rule of this kind")
                self.assertFalse(any(pattern.search(x) for x in rule["new"]),
                                 "the detector still fires on the new text")
                code, out, _ = run(root, rules, "plan", "--profile", profile)
                if fires:
                    self.assertIn(f"site  {rule['kind']}", out)
                self.assertEqual(run(root, rules, "check", "--profile", profile)[0], 1)
                flag = ["--after-tls"] if self.data["profiles"][profile].get("requires_flag") else []
                code, diff, _ = run(root, rules, "apply", "--profile", profile, "--dry-run", *flag)
                self.assertEqual(code, 0)
                expected = before.replace("\n".join(rule["old"]), "\n".join(rule["new"]), 1)
                self.assertEqual(diff, "".join(difflib.unified_diff(
                    before.splitlines(True), expected.splitlines(True),
                    "a/" + rule["file"], "b/" + rule["file"])))
                self.assertEqual(run(root, rules, "apply", "--profile", profile, *flag)[0], 0)
                self.assertEqual((root / rule["file"]).read_text(), expected)
                self.assertEqual(run(root, rules, "apply", "--profile", profile, "--dry-run", *flag)[1], "")
                self.assertEqual(run(root, rules, "apply", "--profile", profile, *flag)[0], 0)
                self.assertEqual((root / rule["file"]).read_text(), expected)
                code, out, _ = run(root, rules, "check", "--profile", profile)
                self.assertEqual(code, 0, out)

    def test_rule_ids_are_unique_and_kinds_belong_to_profiles(self):
        ids = [r["id"] for r in self.data["rules"]]
        self.assertEqual(len(ids), len(set(ids)))
        for name, kind in self.data["kinds"].items():
            self.assertIn(kind["profile"], self.data["profiles"], name)

    def test_the_owed_list_names_the_books_and_the_host_fallback(self):
        owed = {(e["file"], e["owner"]) for e in self.data["owed"]}
        self.assertIn(("books/tls-key-exchange.lisp", "P"), owed)
        self.assertIn(("host/native/tls.lisp", "joint P/N"), owed)
        reasons = " ".join(e["reason"] for e in self.data["owed"] if e["owner"] == "P")
        self.assertIn("owed: books (P)", reasons)

    def test_the_real_tree_is_clean_for_the_landed_profiles(self):
        for profile in LANDED:
            with self.subTest(profile=profile):
                code, out, _ = run(ROOT, cs.RULES, "check", "--profile", profile)
                self.assertEqual(code, 0, out)


if __name__ == "__main__":
    unittest.main()

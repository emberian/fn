"""tools/scenario_suite.py: the scenario tiers are well formed and runnable."""
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import scenario_suite  # noqa: E402

GOOD = "".join(f"{t}\tmodule\ttests.test_native_x\tDUR\twhy\n" for t in scenario_suite.TIERS)


def tree(tmp, tiers=GOOD):
    root = pathlib.Path(tmp)
    (root / "tests/scenarios").mkdir(parents=True)
    (root / "tests/test_native_x.py").write_text(
        'IMAGE = native_image("FN_NATIVE_HOST")\nFLAG = environ.get("FN_RUN_X")\n'
        "class XTests:\n    pass\n")
    (root / "tests/test_native_src.py").write_text("SOURCE = 1\n")
    (root / scenario_suite.TIERS_FILE).write_text("# comment\n" + tiers)
    return root


class ScenarioSuiteTests(unittest.TestCase):
    def test_the_tree_tiers_are_well_formed(self):
        self.assertEqual(scenario_suite.findings(), [])

    def test_a_well_formed_file_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(scenario_suite.findings(tree(tmp)), [])

    def test_each_malformation_is_named(self):
        bad = GOOD + ("smoke\tmodule\ttests.test_native_x\tDUR\tagain\n"
                      "smoke\tmodule\ttests.test_native_gone\tDUR\twhy\n"
                      "smoke\tmodule\ttests.test_native_x.NoSuch\tDUR\twhy\n"
                      "smoke\tmodule\ttests.test_native_src\tDUR\twhy\n"
                      "smoke\tenv\tFN_RUN_UNREAD=1\tCUR\twhy\n"
                      "smoke\tmodule\ttests.test_native_x.XTests\tNOPE\twhy\n"
                      "nightly\ttool\tpython3 x.py\tDUR\twhy\n")
        with tempfile.TemporaryDirectory() as tmp:
            found = "\n".join(scenario_suite.findings(tree(tmp, bad)))
        for expected in ("already in tier smoke", "test_native_gone: no such test module",
                         "no class NoSuch", "test_native_src: reads no image variable",
                         "FN_RUN_UNREAD: no test module reads it", "unknown question code",
                         "unknown tier 'nightly'"):
            self.assertIn(expected, found)

    def test_an_empty_tier_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            found = scenario_suite.findings(tree(tmp, GOOD.replace("scale\tmodule", "scale\ttool")))
        self.assertIn("tier scale lists no module", "\n".join(found))

    def test_run_hands_the_tier_to_hbox_native_against_the_published_set(self):
        import contextlib
        import io
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = scenario_suite.main(["run", "smoke", "--image-set", "a" * 40, "--box", "hbox",
                                        "--dry-run"])
        self.assertEqual(code, 0)
        line = out.getvalue().splitlines()[0]
        self.assertIn("--box hbox --image-set " + "a" * 40, line)
        self.assertIn("--images developer,production,dtn,dtn-developer", line)
        self.assertIn(" " + "a" * 40 + " tests.", line)


    def test_run_without_a_box_is_a_boxq_job(self):
        import contextlib
        import io
        if not (scenario_suite.ROOT / "tools/boxq.py").is_file():
            self.skipTest("tools/boxq.py (lane cloud) is not in this tree")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = scenario_suite.main(["run", "peer", "--image-set", "a" * 40, "--dry-run"])
        self.assertEqual(code, 0)
        line = out.getvalue().splitlines()[0]
        self.assertIn("tools/boxq.py submit --kind native --priority lane --image-set " + "a" * 40, line)
        self.assertIn(" -- --allow-skips --env ", line)

AFFECTS = ("tests/native_harness.py\tALL\tharness\n"
           "tests/test_*.py\tSELF\tself\n"
           "host/native/feed-service.lisp\tPEER\tfeed\n"
           "host/native/*.lisp\tDUR\tthe rest of the host (first match wins)\n"
           "docs/*\tNONE\tprose\n")
MAP = ("module\tquality\tquestions\n"
       "test_native_x\tREAL\tDUR\n"
       "test_native_peer\tREAL\tPEER,AUTH\n"
       "test_native_web\tREAL\tWEB\n"
       "test_native_mock\tMOCK\tPEER\n")


class AffectedTests(unittest.TestCase):
    def tree(self, tmp):
        root = tree(tmp)
        (root / scenario_suite.AFFECTS_FILE).write_text("# rules\n" + AFFECTS)
        (root / "planning").mkdir()
        (root / scenario_suite.MODULE_MAP).write_text(MAP + "test_native_gone\tREAL\tDUR\n")
        for name in ("test_native_peer", "test_native_web", "test_native_mock"):
            (root / "tests" / (name + ".py")).write_text("")
        return root

    def test_the_tree_rules_are_well_formed(self):
        self.assertEqual(scenario_suite.affect_findings(), [])

    def test_a_rule_selects_by_question_code_after_the_smoke_floor(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.tree(tmp)
            got = scenario_suite.affected(["host/native/feed-service.lisp"], root)
        # tests.test_native_x is the smoke tier (the floor); the first
        # matching rule (PEER) wins over host/native/*.lisp (DUR).
        self.assertEqual(list(got), ["tests.test_native_x", "tests.test_native_peer"])
        self.assertIn("always", got["tests.test_native_x"])

    def test_mock_modules_none_rules_and_self(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.tree(tmp)
            self.assertEqual(list(scenario_suite.affected(["docs/a.md"], root)), ["tests.test_native_x"])
            self.assertEqual(list(scenario_suite.affected(["tests/test_native_web.py"], root)),
                             ["tests.test_native_x", "tests.test_native_web"])
            self.assertEqual(list(scenario_suite.affected(["tests/test_native_mock.py"], root)),
                             ["tests.test_native_x"])

    def test_an_unclassified_host_file_selects_every_native(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.tree(tmp)
            got = scenario_suite.affected(["host/new-thing-host.lisp"], root)
            harness = scenario_suite.affected(["tests/native_harness.py"], root)
        self.assertEqual(set(got), {"tests.test_native_x", "tests.test_native_peer", "tests.test_native_web"})
        self.assertEqual(set(harness), set(got))
        self.assertIn("unclassified", got["tests.test_native_web"])

    def test_a_helper_change_selects_the_modules_that_mention_what_changed(self):
        import subprocess
        with tempfile.TemporaryDirectory() as tmp:
            root = self.tree(tmp)
            helper = root / "tests" / "native_harness.py"
            helper.write_text("import os\n\ndef a():\n    return 1\n\n"
                              "def b():\n    return a()\n\nclass Node:\n"
                              "    def start(self):\n        return 2\n")
            git = ["git", "-C", str(root), "-c", "user.email=t@t", "-c", "user.name=t"]
            subprocess.run(git + ["init", "-q"], check=True)
            subprocess.run(git + ["add", "-A"], check=True)
            subprocess.run(git + ["commit", "-qm", "base"], check=True)
            (root / "tests" / "test_native_web.py").write_text("from tests.native_harness import b\nb()\n")
            (root / "tests" / "test_native_peer.py").write_text("node.start()\n")
            helper.write_text(helper.read_text().replace("return 1", "return 3")
                              .replace("import os", "import os\nimport re"))
            names = scenario_suite.helper_names("tests/native_harness.py", "HEAD", root)
            got = scenario_suite.affected(["tests/native_harness.py"], root, since="HEAD")
            # a changed, b calls a: both; Node.start untouched; the import is not a change.
            self.assertEqual(names, {"a", "b"})
            self.assertEqual(list(got), ["tests.test_native_x", "tests.test_native_web"])
            # A module-level statement changes: the file's rule (ALL) again.
            helper.write_text(helper.read_text() + "LIMIT = 5\n")
            self.assertIsNone(scenario_suite.helper_names("tests/native_harness.py", "HEAD", root))

    def test_a_bad_code_is_named(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.tree(tmp)
            (root / scenario_suite.AFFECTS_FILE).write_text("host/*\tNOPE\twhy\n")
            self.assertIn("unknown code", "\n".join(scenario_suite.affect_findings(root)))


if __name__ == "__main__":
    unittest.main()

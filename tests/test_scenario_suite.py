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
            code = scenario_suite.main(["run", "smoke", "--image-set", "a" * 40, "--dry-run"])
        self.assertEqual(code, 0)
        line = out.getvalue().splitlines()[0]
        self.assertIn("--box hbox --image-set " + "a" * 40, line)
        self.assertIn("--images developer,production,dtn,dtn-developer", line)
        self.assertIn(" " + "a" * 40 + " tests.", line)


if __name__ == "__main__":
    unittest.main()

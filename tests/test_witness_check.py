"""tools/witness_check.py: each tests/*.sh witness is classed, cited and run."""
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import witness_check  # noqa: E402


def tree(tmp):
    root = pathlib.Path(tmp)
    (root / "tests/scenarios").mkdir(parents=True)
    (root / "planning").mkdir()
    (root / "tests/scenarios/catalog.json").write_text('{"e": ["tests/cited_raw.lisp"]}')
    (root / "planning/release-v6.6.0.md").write_text("| 15a | `sh tests/test_img.sh` |\n")
    (root / "tests/test_native_raw_scripts.py").write_text('RAW_MARK = "# witness: raw"\n')
    (root / "tests/test_a_raw.sh").write_text(
        "#!/bin/sh\n# witness: raw\nsbcl --script tests/cited_raw.lisp\n")
    (root / "tests/test_img.sh").write_text("#!/bin/sh\n# witness: needs-image\n# tests/cited_raw.lisp\n")
    return root


class WitnessTests(unittest.TestCase):
    def test_a_classed_cited_run_witness_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(witness_check.findings(tree(tmp), {}), [])

    def test_unmarked_uncited_and_unlisted_are_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = tree(tmp)
            (root / "tests/bare.sh").write_text("#!/bin/sh\necho hi\n")
            (root / "tests/test_img2.sh").write_text("#!/bin/sh\n# witness: needs-image\n")
            found = witness_check.findings(root, {})
            self.assertTrue(any(f.startswith("tests/bare.sh: no `# witness") for f in found))
            self.assertTrue(any("test_img2.sh: needs-image, but the convergence" in f for f in found))
            self.assertTrue(any("test_img2.sh: no scenario-catalog row" in f for f in found))

    def test_known_only_shrinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            found = witness_check.findings(tree(tmp), {"tests/test_a_raw.sh": "x", "tests/gone.sh": "x"})
            self.assertEqual(len(found), 2)
            self.assertTrue(any("passes now" in f for f in found))
            self.assertTrue(any("gone" in f for f in found))

    def test_the_tree_is_clean(self):
        self.assertEqual(witness_check.findings(), [])


if __name__ == "__main__":
    unittest.main()

"""tools/spec_cite_check.py: a spec cannot cite a name the tree no longer defines (PKT-312)."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import spec_cite_check as scc  # noqa: E402

DEFINED = {"fn-bpn-limits-compose-at-the-codec-widths", "fn-sn-step"}
SPEC = ("specs/bp.md",
        "D-9: raised only with `fn-bpn-limits-compose`.\n"
        "Now `fn-bpn-limits-compose-at-the-codec-widths` and `FN-SN-STEP`.\n"
        "Prose: `fn-bpn`, `fn-bpn-*`, `fn-<rec>-shapep`, `fn-hybrid-v1`, "
        "`(fn-sn-step s)`, `books/x.lisp`.\n")


class SpecCiteCheckTests(unittest.TestCase):
    def test_a_retired_theorem_name_is_undefined_and_fails(self):
        result = scc.check(DEFINED, [SPEC], {})
        self.assertEqual(result.unlisted, {"fn-bpn-limits-compose": ["specs/bp.md:1"]})
        self.assertFalse(result.ok)
        self.assertEqual(result.resolved, 2)  # case-insensitive
        self.assertEqual(result.ruled, {"template": 2, "short": 1, "tag": 1})
        self.assertEqual(result.checked, 7)  # the call form and the path are not names

    def test_a_listed_stale_citation_is_counted_not_failed_and_only_in_its_file(self):
        listing = {"stale": {"PKT-446": {"fn-bpn-limits-compose": ["specs/bp.md"]}}}
        result = scc.check(DEFINED, [SPEC], listing)
        self.assertTrue(result.ok)
        self.assertEqual(result.stale, {"fn-bpn-limits-compose": ["specs/bp.md:1"]})
        other = ("docs/new.md", "see `fn-bpn-limits-compose`\n")
        result = scc.check(DEFINED, [SPEC, other], listing)
        self.assertEqual(result.unlisted, {"fn-bpn-limits-compose": ["docs/new.md:1"]})

    def test_a_repaired_citation_makes_its_entry_unused(self):
        listing = {"stale": {"PKT-446": {"fn-bpn-limits-compose": ["specs/bp.md"]}},
                   "exemptions": {"fn-gone-name": "was prose"}}
        repaired = ("specs/bp.md", "`fn-bpn-limits-compose-at-the-codec-widths`\n")
        result = scc.check(DEFINED, [repaired], listing)
        self.assertFalse(result.ok)
        self.assertEqual(len(result.unused), 2)

    def test_an_exemption_needs_its_reason_and_resolves(self):
        listing = {"exemptions": {"fn-bpn-limits-compose": "a historical name in a changelog"}}
        result = scc.check(DEFINED, [SPEC], listing)
        self.assertTrue(result.ok)
        self.assertEqual(result.exempted, {"fn-bpn-limits-compose": 1})

    def test_a_slash_abbreviation_resolves_only_when_every_expansion_does(self):
        self.assertEqual(scc.abbreviated("fnn-metadata-frontier-frame/-decode/-next"),
                         ["fnn-metadata-frontier-frame", "fnn-metadata-frontier-decode",
                          "fnn-metadata-frontier-next"])
        defined = {"fn-a-frame", "fn-a-decode"}
        good = ("specs/x.md", "`fn-a-frame/-decode`\n")
        bad = ("specs/x.md", "`fn-a-frame/-decode/-next`\n")
        self.assertTrue(scc.check(defined, [good], {}).ok)
        self.assertEqual(list(scc.check(defined, [bad], {}).unlisted),
                         ["fn-a-frame/-decode/-next"])

    def test_a_record_name_is_defined(self):
        # (fn-defrecord fn-node-state ...) in books/node.lisp: prose names the
        # record kind, which no defun spells.
        self.assertIn("fn-node-state", scc.defined_names())

    def test_the_tree_is_green_under_strict(self):
        self.assertEqual(scc.main(["--summary", "--strict"]), 0)


if __name__ == "__main__":
    unittest.main()

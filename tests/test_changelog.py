"""tools/changelog.py: the merge-subject parser and the one-line rule."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import changelog  # noqa: E402


class MergePartsTests(unittest.TestCase):
    def test_the_subject_shapes_on_dev(self):
        cases = {
            "Merge lane/tls-reload (c7c423e8, batch AM): `fn operator CONFIG tls reload`":
                ("tls-reload", "`fn operator CONFIG tls reload`"),
            "Batch AP: merge lane/group-access (a24408d9): PRF-222, per-login group access":
                ("group-access", "PRF-222, per-login group access"),
            "Merge lane/sanding: tin logs in over a TLS-only listener":
                ("sanding", "tin logs in over a TLS-only listener"),
            "Merge lane/x (a (nested) b; c): the message":
                ("x", "the message"),
            "Merge lane/y (a), more words (b; c): the message":
                ("y", "the message"),
        }
        for subject, expected in cases.items():
            self.assertEqual(changelog.merge_parts(subject), expected, subject)

    def test_a_direct_commit_is_not_a_merge(self):
        self.assertIsNone(changelog.merge_parts("Regenerate ledger and current view"))

    def test_first_clause_drops_leading_ids_and_cuts_at_a_clause(self):
        self.assertEqual(changelog.first_clause("PRF-222, NNT-046, per-login group access; more"),
                         "per-login group access")
        long = "word " * 60
        out = changelog.first_clause(long)
        self.assertTrue(out.endswith(" ...") and len(out) <= 154, out)

    def test_capability_first_match_and_other(self):
        self.assertEqual(changelog.capability("bp-catalog"), "Delay-tolerant networking (BP, TCPCL)")
        self.assertEqual(changelog.capability("release-glibc-floor"), "Release, packaging and deployment")
        self.assertEqual(changelog.capability("zzz-unknown"), "Other")


class PreviousReleaseTests(unittest.TestCase):
    """The range starts at the previous release in D37's sequence, not at
    the numerically largest tag."""

    def test_the_first_release_has_none(self):
        self.assertIsNone(changelog.previous_release("6.6.0", []))
        self.assertIsNone(changelog.previous_release("6.6.0", ["v6.6.0", "other"]))

    def test_sequence_order_not_numeric(self):
        self.assertEqual(changelog.previous_release("6.7.0", ["v6.6.4", "v6.6.5"]), "v6.6.5")
        self.assertEqual(changelog.previous_release("6.6.6", ["v6.6.5", "v6.7.9", "v6.7.10"]),
                         "v6.7.10")
        self.assertEqual(changelog.previous_release("6.6.6.6", ["v6.7.3", "v6.6.6", "v6.6.6.6"]),
                         "v6.6.6")

    def test_tags_after_version_and_strays_are_ignored(self):
        self.assertEqual(changelog.previous_release("6.6.2", ["v6.6.1", "v6.6.3", "v1.2.3"]),
                         "v6.6.1")


if __name__ == "__main__":
    unittest.main()

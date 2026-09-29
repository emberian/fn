"""tools/alphabet_check.py: the readers on small forms, and the tree's two
hand-written families agree today (a writer kind the dispatcher lacks is
exactly what the make check step refuses)."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "tools"))

import alphabet_check  # noqa: E402


class Readers(unittest.TestCase):
    def test_kinds_in_equal_kind_arms(self):
        form = "(defun f (kind) (cond ((equal kind :a) 1) ((equal kind :b-c) 2) (t 0)))"
        self.assertEqual(alphabet_check.kinds_in(form, r"\(equal kind (:[a-z][a-z0-9-]*)\)"),
                         {":a", ":b-c"})

    def test_cond_predicates(self):
        form = "(defun g (x) (cond ((fn-held-p x) 1) ((fn-stxe-p x) 2) ((fn-cpe-eventp x) 3) (t nil)))"
        self.assertEqual(alphabet_check.cond_predicates(form),
                         {"fn-held-p", "fn-stxe-p", "fn-cpe-eventp"})

    def test_findings_name_the_missing_kind(self):
        config = {"declared": {":a"}, "encoder": {":a"}, "decoder": {":a"},
                  "dispatcher": {":a"}, "writers": {":a", ":new"}}
        store = {"encoder": {"fn-held-p"}, "decoder": {"fn-held-p"}, "kind": {"fn-held-p"},
                 "dispatcher": {"fn-held-p", "fn-old-p"}}
        failures, notes = alphabet_check.findings(config, store)
        self.assertEqual(len(failures), 4)
        self.assertTrue(all(":new" in f for f in failures))
        self.assertEqual(notes, ["store event dispatcher arms no encoder produces: fn-old-p"])


class Tree(unittest.TestCase):
    def test_the_tree_agrees(self):
        config, store = alphabet_check.config_tables(), alphabet_check.store_event_tables()
        failures, _ = alphabet_check.findings(config, store)
        self.assertEqual(failures, [])
        self.assertIn(":set-limit", config["dispatcher"])
        self.assertIn("fn-store-retention-event-p", store["dispatcher"])
        self.assertGreaterEqual(len(config["writers"]), 20)


if __name__ == "__main__":
    unittest.main()

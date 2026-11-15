import json
import sys
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from rewrite_boot_evidence_phases import EVIDENCE_OPERATIONS, one, rewrite, rows, symbol, value


class BootEvidenceDeclarations(unittest.TestCase):
    def setUp(self):
        self.fixture = json.loads((ROOT / "tests/fixtures/lisp_rewrite/boot_evidence_phases.json").read_text())

    def test_complete_class_transform_and_idempotence(self):
        after, count = rewrite(self.fixture["before"], self.fixture["arms"])
        self.assertEqual(count, 14)
        self.assertEqual(after, self.fixture["after"])
        self.assertEqual(rewrite(after, self.fixture["arms"]), (after, 0))
        self.assertIn('; :checkpoint-evidence-check text must survive unchanged.', after)
        self.assertIn('(defconst *note* ":checkpoint-evidence-next")', after)

    def test_actual_state_arm_order_and_custody_are_complete(self):
        source = (ROOT / "books/boot-kind.lisp").read_text()
        arms = (ROOT / "books/boot.lisp").read_text()
        kind = one("(defmachine fn2-boot ?*rest)", source)
        states = [symbol(node) for node in value(kind, ":states").items]
        declared = rows(value(kind, ":arms"))
        self.assertEqual(list(declared), states)
        actual = rows(value(one("(defmachine-arms fn2-boot :declare ?*rest)", arms), ":arms"))
        self.assertEqual(set(actual), set(states))
        holds = rows(value(kind, ":holds"))
        for phase in EVIDENCE_OPERATIONS:
            self.assertEqual([symbol(node) for node in holds[phase].items], [phase, ":storage-window"])
        self.assertEqual(rewrite(source, arms), (source, 0))

    def test_no_custody_guess_for_new_phase_or_placeholder(self):
        for bad in (
            self.fixture["before"].replace(":checkpoint-evidence-next :checkpoint-census", ":checkpoint-evidence-next :checkpoint-evidence-unknown :checkpoint-census"),
            self.fixture["before"].replace(":holds (", ":holds ((:checkpoint-evidence-check) ", 1),
            self.fixture["before"].replace(":holds (", ":holds ((:checkpoint-evidence-check :retained) ", 1),
        ):
            with self.subTest(source=bad), self.assertRaises(ValueError):
                rewrite(bad, self.fixture["arms"])

    def test_absent_actual_operation_is_not_repaired_with_stub(self):
        bad = self.fixture["arms"].replace("fn2-boot-checkpoint-evidence-copy", "unrelated-operation")
        with self.assertRaises(ValueError):
            rewrite(self.fixture["before"], bad)

    def test_other_missing_arms_and_duplicate_states_are_refused(self):
        for bad in (
            self.fixture["before"].replace("(:failed)", ""),
            self.fixture["before"].replace(":states (:free", ":states (:free :free"),
        ):
            with self.subTest(source=bad), self.assertRaises(ValueError):
                rewrite(bad, self.fixture["arms"])


if __name__ == "__main__":
    unittest.main()

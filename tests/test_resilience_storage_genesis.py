"""Synthetic scanner oracle teeth; no native-image evidence."""
import unittest
from tools.resilience.adapters.storage_genesis import Observer, judge


class StorageGenesisTests(unittest.TestCase):
    def fixture(self):
        observer = Observer()
        original, alternate = bytes(range(80)), bytes(reversed(range(80)))
        damaged = bytearray(original)
        damaged[40] ^= 1
        observer("genesis-valid-pair", original=original, alternate=alternate,
                 original_digest=["digest state same", "digest genesis A"],
                 alternate_digest=["digest state same", "digest genesis B"],
                 validation="both prior native digest commands succeeded")
        observer("checksum-breaking-refusal", original=original, mutated=bytes(damaged),
                 offset=40, xor=1, exit_code=1, stdout=b"", stderr=b"reason=genesis-damaged")
        observer("intact-alternate-chain-refusal", replacement=alternate,
                 exit_code=1, stdout=b"", stderr=b"chain refused")
        observer.journal.environment("image-artifact-coordinate", source="a" * 40,
                                     launcher="synthetic", manifest="synthetic/MANIFEST.json", manifest_sha256="b" * 64)
        return observer.journal

    def test_distinct_mutation_classes_and_pending_native(self):
        verdict = judge(self.fixture(), "a" * 40)
        self.assertEqual(verdict.kind, "consistent")
        self.assertIn("storage-native-qualification", verdict.pending_rules)
        self.assertEqual(len(verdict.witnesses_observed), 2)

    def test_unobserved_alternate_validity_fails_closed(self):
        journal = self.fixture()
        journal.records[0].pop("validation")
        self.assertEqual(judge(journal, "a" * 40).kind, "harness-failure")

    def test_valid_swap_acceptance_is_named_violation(self):
        journal = self.fixture()
        journal.records[2]["exit_code"] = 0
        verdict = judge(journal, "a" * 40)
        self.assertEqual(verdict.kind, "violation")
        self.assertEqual(verdict.cause, "intact-alternate-chain-refused")

    def test_recomputed_or_changed_swap_is_not_retained_intact_frame(self):
        journal = self.fixture()
        journal.records[2]["replacement"]["octets_hex"] = "00"
        self.assertEqual(judge(journal, "a" * 40).kind, "harness-failure")

    def test_missing_image_and_reordered_or_truncated_events_fail_closed(self):
        for alter in (lambda j: j.records.pop(), lambda j: j.records.pop(1)):
            journal = self.fixture()
            alter(journal)
            self.assertEqual(judge(journal, "a" * 40).kind, "harness-failure")

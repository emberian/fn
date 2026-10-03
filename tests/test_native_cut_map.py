import unittest

from tests.campaign import native_cuts


class NativeCutMapTests(unittest.TestCase):
    def test_every_declared_native_cut_is_a_model_program_cut(self):
        native_cuts.verify_native_cut_map()

    def test_log_cuts_match_the_log_programs(self):
        self.assertEqual(native_cuts.verify_log_cut_inventory(), (13, 7))
        native_cuts.verify_log_cut_map()
        native_cuts.verify_post_log_cut_map()
        native_cuts.verify_log_segment_cut_map()

    def test_segment_inventory_has_separate_recovery_outcomes(self):
        rows = native_cuts.segment_cut_inventory()
        self.assertEqual([step.kind for step in native_cuts.model_steps(
            "fn-lgs-rotate-program", native_cuts.SEGMENT_BOOK)],
            ["rename", "cut", "write", "cut"])
        self.assertEqual([row.name for row in rows],
                         ["rotate-created", "rotate-fenced", "rotate-renamed",
                          "rotate-headed", "rotate-durable", "drop-unlinked", "drop-durable"])
        self.assertEqual([row.surviving for row in rows],
                         ["old-active"] * 2 + ["old-and-next"] * 3 + ["next-only"] * 2)
        self.assertEqual({row.outcome for row in rows}, {"kill"})
        self.assertTrue(set(row.name for row in rows).isdisjoint(
            cut.name for cut in native_cuts.LOG_CUTS))

    def test_statement_cut_follows_its_barrier(self):
        native_cuts.verify_statement_cut_map()

    def test_compaction_is_rotation(self):
        native_cuts.verify_compact_is_rotation()

    def test_outcomes_remain_explicit(self):
        self.assertEqual({cut.outcome for cut in native_cuts.ALL_CUTS}, {"kill"})
        # Outside a batch the record is absent before its append and present
        # after (a batch of one commits before its place); "either" is the
        # served batch's log-written (POST_LOG_CUTS).
        self.assertEqual({cut.candidate for cut in native_cuts.POST_CUTS},
                         {"absent", "present"})
        self.assertEqual({cut.candidate for cut in native_cuts.POST_LOG_CUTS},
                         {"absent", "either", "present"})


if __name__ == "__main__":
    unittest.main()

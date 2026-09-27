import unittest

from tests.campaign import native_cuts


class NativeCutMapTests(unittest.TestCase):
    def test_every_declared_native_cut_is_a_model_program_cut(self):
        native_cuts.verify_native_cut_map()

    def test_log_cuts_match_the_log_programs(self):
        native_cuts.verify_log_cut_map()
        native_cuts.verify_post_log_cut_map()
        native_cuts.verify_log_segment_cut_map()

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

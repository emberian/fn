import unittest

from tests.campaign import native_cuts


class NativeCutMapTests(unittest.TestCase):
    def test_every_declared_native_cut_is_a_model_program_cut(self):
        native_cuts.verify_native_cut_map()

    def test_checkpoint_cuts_match_native_and_reclaim_program(self):
        native_cuts.verify_checkpoint_cut_map()

    def test_outcomes_remain_explicit(self):
        self.assertEqual({cut.outcome for cut in native_cuts.ALL_CUTS}, {"kill"})
        self.assertEqual({cut.candidate for cut in native_cuts.POST_CUTS},
                         {"absent", "either", "present"})


if __name__ == "__main__":
    unittest.main()

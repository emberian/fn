"""Small deterministic checks for the external native benchmark harness."""
import unittest

from tests.bench.native_shared_owner import article, percentile, stats


class NativeSharedOwnerBenchTests(unittest.TestCase):
    def test_article_profile_is_exact_and_unique(self):
        first_id, first = article(1, 1024)
        second_id, second = article(2, 1024)
        self.assertNotEqual(first_id, second_id)
        self.assertEqual(len(first), 1202)
        self.assertTrue(first.endswith(b"\r\n"))
        self.assertIn(("Message-ID: " + first_id + "\r\n").encode("ascii"), first)

    def test_nearest_rank_percentile_and_summary(self):
        values = list(range(1, 21))
        self.assertEqual(percentile(values, .95), 19)
        self.assertEqual(stats(values)["p50_seconds"], 10.5)


if __name__ == "__main__":
    unittest.main()

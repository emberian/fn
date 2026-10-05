"""The scaling gate (smoke tier): serving work is linear in the article.

D27's promise, "bound work, never data", was broken twice without a test
noticing (PERF-REGRESSION-20261005): a per-octet borrow protocol and a
re-digest of the whole protected prefix per window, which made ARTICLE
quadratic.  list_codec_check catches octet lists; nothing caught per-octet
protocols or quadratic work.  This does: store articles of N and 8N octets,
time the ARTICLE end to end on a live owner (request to the terminating dot),
and fail when the 8N time is more than 10x the N time (linear is 8x, plus a
fixed cost that only lowers the ratio).

Sizes default to 64 KiB and 512 KiB; FN_SCALING_N overrides N in octets.
Run with FN_NATIVE_HOST naming the image under test.
"""
import os
import time
import unittest

from tests.native_harness import EXIT_OK, Client
from tests.test_native_bounds_join import JoinFixture, article, post, read_article

N = int(os.environ.get("FN_SCALING_N", str(64 * 1024)))
RATIO_LIMIT = 10.0
MAX_ARTICLE = 1 << 20
INIT_PROFILE = ("--profile", "development", "--max-transactions", "256",
                "--max-history-octets", str(64 << 20),
                "--max-record-octets", str(MAX_ARTICLE + 65536),
                "--max-article-octets", str(MAX_ARTICLE),
                "--max-groups-per-article", "16")


def timed_article(client, message_id):
    """(seconds to the terminating dot, octets served)."""
    start = time.monotonic()
    status, body = read_article(client, message_id)
    elapsed = time.monotonic() - start
    assert body is not None, status
    return elapsed, len(body)


class ScalingTests(JoinFixture):
    def test_article_time_is_linear_in_the_article(self):
        self.assertLessEqual(8 * N, MAX_ARTICLE)
        created = self.op("init", *INIT_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.node.start(image=self.image)
        times = {}
        with Client(self.port, timeout=600) as client:
            for size in (N, 8 * N):
                message_id = "<scaling-{}@example.invalid>".format(size)
                reply = post(client, article(message_id, size))
                self.assertTrue(reply.startswith("240"), reply)
                times[size] = timed_article(client, message_id)
                print("ARTICLE", size, "%.3f s" % times[size][0], flush=True)
        self.node.stop()
        small, large = times[N], times[8 * N]
        self.assertGreater(large[1], 8 * N)
        ratio = large[0] / max(small[0], 1e-3)
        self.assertLessEqual(
            ratio, RATIO_LIMIT,
            "ARTICLE of {} octets took {:.3f} s, of {}: {:.3f} s; ratio {:.1f} exceeds {}: "
            "serving work is superlinear in the article".format(
                N, small[0], 8 * N, large[0], ratio, RATIO_LIMIT))


if __name__ == "__main__":
    unittest.main()

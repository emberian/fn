"""The stalled-feed native case probes a held reply without a stream timeout (NATIVE-R2-OFFLOCK-STALL-TEST)."""
import unittest
from pathlib import Path


class ProbeTests(unittest.TestCase):
    def test_the_stalled_feed_case_sets_no_timeout_on_its_stream(self):
        source = Path(__file__).with_name("test_native_owner_offlock.py").read_text()
        self.assertFalse("except (socket.timeout, TimeoutError)" in source,
                         "the stalled-feed case must probe with select, not a timeout on a makefile stream")


if __name__ == "__main__":
    unittest.main()

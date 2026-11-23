"""Native BLAKE3 in tools/fn_admin.py and logical POST latency in tools/load/driver.py.

Needs `sh host/build-blake3.sh build/lib` first (or FN2_BLAKE3_LIBRARY)."""
from __future__ import annotations

import statistics
import sys
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))

import fn_admin  # noqa: E402
from tools.load import driver  # noqa: E402

LENGTHS = (0, 1, 63, 64, 65, 1023, 1024, 1025, 4096, 65536)


class NativeBlake3(unittest.TestCase):
    def test_native_loaded_and_agrees(self):
        self.assertIsNotNone(fn_admin._load_native_blake3(), "build host/build-blake3.sh build/lib first")
        for n in LENGTHS:
            payload = bytes((i * 131 + 7) & 0xFF for i in range(n))
            with self.subTest(n=n):
                self.assertEqual(fn_admin.blake3(payload), fn_admin._blake3_py(payload))

    def test_known_vector(self):
        # BLAKE3 of the empty input (official test vector).
        self.assertEqual(fn_admin.blake3(b"").hex(),
                         "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")

    def test_fnct_seal_64k_fast_and_round_trips(self):
        payload = b"x" * 65536
        times = []
        for _ in range(9):
            t0 = time.perf_counter()
            frame = fn_admin.fnct_seal(4, payload)
            times.append(time.perf_counter() - t0)
        self.assertLess(statistics.median(times) * 1000.0, 5.0)
        self.assertEqual(fn_admin.fnct_open(frame), (4, payload))
        # tooth: a flipped trailer bit is refused
        bad = frame[:-1] + bytes([frame[-1] ^ 1])
        with self.assertRaises(fn_admin.WireError):
            fn_admin.fnct_open(bad)


class _Stream:
    def write(self, b):
        pass


class _Conn:
    """Replies 441 to the first POST, then 340 and 240."""
    def __init__(self, posts):
        self._posts = list(posts)
        self._final = []
        self.stream = _Stream()
        self.sock = None

    def line(self, cmd):
        assert cmd == "POST"
        first, final = self._posts.pop(0)
        if final is not None:
            self._final.append(final)
        return first

    def readline(self):
        return self._final.pop(0)


class LogicalPostLatency(unittest.TestCase):
    def test_retry_counts_and_backoff_is_logical(self):
        ctr = driver.Counters()
        conn = _Conn([(b"441 busy\r\n", None), (b"340 ok\r\n", b"240 ok\r\n")])
        service_s, logical_s, attempts = driver.post_one_detailed(conn, ctr, 0)
        self.assertEqual(attempts, 2)
        self.assertIsNotNone(service_s)
        self.assertGreaterEqual(logical_s - service_s, 0.20)
        self.assertEqual(ctr.refused, 1)

    def test_first_try_logical_equals_service(self):
        ctr = driver.Counters()
        conn = _Conn([(b"340 ok\r\n", b"240 ok\r\n")])
        service_s, logical_s, attempts = driver.post_one_detailed(conn, ctr, 0)
        self.assertEqual(attempts, 1)
        self.assertLess(logical_s - service_s, 0.20)

    def test_post_one_keeps_service_seconds(self):
        conn = _Conn([(b"441 busy\r\n", None), (b"340 ok\r\n", b"240 ok\r\n")])
        d = driver.post_one(conn, driver.Counters(), 0)
        self.assertIsInstance(d, float)
        self.assertLess(d, 0.20)

    def test_exhaustion(self):
        conn = _Conn([(b"441 busy\r\n", None)] * 2)
        self.assertEqual(driver.post_one_detailed(conn, driver.Counters(), 0, retries=2), (None, None, 2))


if __name__ == "__main__":
    unittest.main()

import unittest
import zlib
from tests.compress_peer_oracle import check


class CompressPeerOracleTests(unittest.TestCase):
    def rows(self):
        encoder = zlib.compressobj(wbits=-15)
        return [(reply.hex(), (encoder.compress(reply) + encoder.flush(zlib.Z_SYNC_FLUSH)).hex())
                for reply in [b"201 backend ready\r\n", b"201 backend ready\r\n", b"205 closing\r\n"]]

    def test_persistent_exact_replies(self):
        self.assertTrue(check(self.rows()))

    def test_wrong_reply_rejected(self):
        rows = self.rows()
        rows[1] = (b"wrong\r\n".hex(), rows[1][1])
        with self.assertRaises(AssertionError):
            check(rows)

    def test_reset_stream_rejected(self):
        rows = self.rows()
        fresh = zlib.compressobj(wbits=-15)
        rows[1] = (rows[1][0], (fresh.compress(bytes.fromhex(rows[1][0])) + fresh.flush(zlib.Z_FINISH)).hex())
        with self.assertRaises((AssertionError, zlib.error)):
            check(rows)

    def test_missing_output_rejected(self):
        rows = self.rows()
        rows[1] = (rows[1][0], "")
        with self.assertRaises(AssertionError):
            check(rows)

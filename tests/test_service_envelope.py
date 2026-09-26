"""The envelope harness's pure parts (tools/service_envelope.py): the signed
mix, the Message-IDs the readers may ask for, the step grammar and the
summary a record quotes.  The native rows themselves run on hbox."""

import contextlib
import io
import unittest

from tools import service_envelope as se


class ServiceEnvelopeTests(unittest.TestCase):
    def test_the_signed_mix_is_one_in_k_and_never_at_zero(self):
        signed = [i for i in range(10000) if se.is_signed(i, 256)]
        self.assertEqual(len(signed), 39)
        self.assertNotIn(0, signed)
        self.assertEqual([i for i in range(100) if se.is_signed(i, 0)], [])

    def test_readers_ask_only_for_unsigned_articles_of_the_preload(self):
        # Articles past `loaded` were posted by the measured rows or never
        # posted (a signed row's slot): a reader must not ask for them.
        state = {"loaded": 300, "count": 325, "signed_every": 64}
        ids = se.present_msgids(state)
        numbers = [int(x[5:11]) for x in ids]
        self.assertTrue(all(n < 300 and not se.is_signed(n, 64) for n in numbers))
        self.assertGreater(len(ids), 40)

    def test_the_steps_are_refused_unless_load_goes_with_load_to(self):
        for argv in (["--steps", "load,latency"], ["--steps", "latency", "--load-to", "10"],
                     ["--steps", "latency,warm"]):
            with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
                se.main(["measure", "--image", "/nonexistent", "--dir", "/nonexistent/d", "--json", "/dev/null",
                         "--label", "t", "--revision", "r"] + argv)

    def test_the_summary_quotes_the_terminator_interval_and_the_peak(self):
        row = {"p95_ms": 2.0}
        out = {"n_at_start": 10000, "n": 10150, "filesystem": {"type": "zfs"},
               "opens": [{"n": 10000, "after": "stop", "seconds": 5.0, "memory": {"hwm_kib": 7}}],
               "rows": {"greeting": row, "over40": row, "over100": row,
                        "post": {"terminator_to_reply": {"p95_ms": 160.0}, "command_to_reply": {"p95_ms": 170.0}},
                        "signed": {"terminator_to_reply": {"p95_ms": 300.0}},
                        "rate1": {"post_per_s": 6.0}, "rate8": {"post_per_s": 7.5},
                        "memory_after_rate": {"hwm_kib": 9}}}
        s = se.summary_rows(out)
        self.assertEqual((s["post_p95_ms"], s["signed_p95_ms"]), (160.0, 300.0))
        self.assertEqual(s["rates_post_per_s"], {"rate1": 6.0, "rate8": 7.5})
        self.assertEqual(s["peak_rss_kib"], 9)
        self.assertEqual(s["opens"], [(10000, "stop", None, 5.0)])

    def test_the_open_mode_is_the_owners_own_line(self):
        err = b"CONTROL x\nOWNER-OPEN open=checkpoint:8650 suffix=1351\naccepted reader connection=0\n"
        self.assertEqual(se.open_mode(err), "open=checkpoint:8650 suffix=1351")
        self.assertEqual(se.open_mode(b"OWNER-OPEN open=full-replay reason=absent\n"),
                         "open=full-replay reason=absent")
        self.assertIsNone(se.open_mode(b"LISTENING 127.0.0.1 1\n"))


if __name__ == "__main__":
    unittest.main()

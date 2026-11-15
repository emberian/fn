"""Exact-byte acceptance controls for the native APPEND/FETCH restart fixture."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("native_append_fetch", Path(__file__).with_name("native-append-fetch-restart.py"))
campaign = importlib.util.module_from_spec(spec)
spec.loader.exec_module(campaign)


class ExactFetch(unittest.TestCase):
    def test_crossing_articles_reject_a_previous_article_reply(self):
        first = campaign.crossing_article("<native-append-fetch-0@example.invalid>")
        second = campaign.crossing_article("<native-append-fetch-1@example.invalid>")
        self.assertEqual(len(first), 6144)
        self.assertEqual(len(second), 6144)
        self.assertNotEqual(first, second)
        for article in (first, second):
            self.assertIn(b"\r\n.", article)
            self.assertTrue(article.endswith(b"\r\n"))
        stale = dict(outcome="accepted", article_hex=first.hex(), octets=len(first))
        with self.assertRaises(AssertionError):
            campaign.exact_fetch(stale, second)

    def test_full_binary_article_and_changed_reply_controls(self):
        article = b"Header: exact\r\n\r\n\x00\xff.dot\r\n"
        good = dict(outcome="accepted", article_hex=article.hex(), octets=len(article))
        self.assertEqual(campaign.exact_fetch(good, article), article)
        for changed in (
            dict(good, article_hex=article[:-1].hex()),
            dict(good, article_hex=(article[:-1] + b"x").hex()),
            dict(good, octets=len(article) + 1),
            dict(outcome="refused"),
        ):
            with self.assertRaises(AssertionError):
                campaign.exact_fetch(changed, article)


if __name__ == "__main__":
    unittest.main()

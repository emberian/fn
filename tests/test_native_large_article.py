"""Generation controls only; no native process or admission claim."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("large", Path(__file__).with_name("native-large-article-refusal.py"))
large = importlib.util.module_from_spec(spec)
spec.loader.exec_module(large)


class Payload(unittest.TestCase):
    def test_distinct_windows_and_articles(self):
        first = large.large_article("<large-refused-0@example.invalid>", b"first")
        other = large.large_article("<large-refused-1@example.invalid>", b"other")
        for article in (first, other):
            self.assertEqual(len(article), 98304)
            self.assertTrue(article.endswith(b"\r\n"))
            self.assertIn(b"\r\n\r\n.", article)
            chunks = [article[n:n + 4096] for n in range(0, len(article), 4096)]
            self.assertEqual(len(set(chunks)), len(chunks))
            self.assertTrue(all(len(line) < 998 for line in article.split(b"\r\n")))
        for offset in range(0, len(first), 4096):
            self.assertNotEqual(first[offset:offset + 4096], other[offset:offset + 4096])
        self.assertNotEqual(first[65536:], other[65536:])


if __name__ == "__main__":
    unittest.main()

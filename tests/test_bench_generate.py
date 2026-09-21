"""Benchmark source must be accepted-shaped before it can measure posting."""
import unittest

from tests.bench.generate import article_octets, message_id


class ArticleSourceTests(unittest.TestCase):
    def test_exact_sizes_have_only_complete_crlf_lines(self):
        groups = ["fn.letters", "fn.test"]
        # 503 was one of the old refusal-shaped sample sizes: it used to cut
        # a line terminator.  The range also covers each remainder modulo the
        # old 74-octet body line unit.
        for size in range(160, 504):
            msgid = message_id(7, size)
            article = article_octets(7, size, size, msgid, groups)
            self.assertEqual(len(article), size)
            self.assertTrue(article.endswith(b"\r\n"))
            self.assertNotIn(b"\n", article.replace(b"\r\n", b""))
            self.assertIn(b"Message-ID: " + msgid + b"\r\n", article)
            self.assertIn(b"Newsgroups: fn.letters,fn.test\r\n", article)

    def test_folded_stress_source_is_also_complete_crlf(self):
        msgid = message_id(9, 1)
        article = article_octets(9, 1, 12000, msgid, ["fn.letters"], "folded")
        self.assertEqual(len(article), 12000)
        self.assertTrue(article.endswith(b"\r\n"))
        self.assertNotIn(b"\n", article.replace(b"\r\n", b""))


if __name__ == "__main__":
    unittest.main()

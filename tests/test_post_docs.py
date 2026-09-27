"""tools/post_docs.py and tools/docs_articles.py: the guides as Usenet articles."""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import docs_articles  # noqa: E402
import post_docs  # noqa: E402


class ArticlesTests(unittest.TestCase):
    def test_the_committed_articles_are_well_formed(self):
        self.assertEqual(docs_articles.check(docs_articles.load()), [])

    def test_a_stale_message_id_and_a_wide_line_are_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "fn-faq-1.txt"
            text = (docs_articles.ARTICLES / "fn-faq-1.txt").read_text()
            path.write_text(text.replace("Last-modified: 2026-09-27", "Last-modified: 2026-09-28")
                            + "x" * 73 + "\n")
            errors = docs_articles.check([docs_articles.parse(path)])
        self.assertTrue(any("should be <fn-faq-1-20260928@" in e for e in errors), errors)
        self.assertTrue(any("73 columns" in e for e in errors), errors)

    def test_wire_is_crlf_and_dot_stuffed(self):
        a = docs_articles.Article(Path("x.txt"), [("Subject", "s")], ".dot\nplain\n")
        self.assertEqual(a.wire([("Supersedes", "<o@h>")]),
                         b"Subject: s\r\nSupersedes: <o@h>\r\n\r\n..dot\r\nplain\r\n")


class SupersedeTests(unittest.TestCase):
    def article(self, mid):
        return docs_articles.Article(Path("x.txt"), [("Message-ID", mid)], "")

    def test_the_newest_older_version_of_the_same_stem_is_superseded(self):
        new = self.article("<fn-faq-3-20261001@fn.fg-goose.online>")
        ids = ["<fn-faq-3-20260927@fn.fg-goose.online>", "<fn-faq-3-20260929@fn.fg-goose.online>",
               "<fn-faq-3-openbsd-20260927@fn.fg-goose.online>",
               "<fn-faq-3-20261002@fn.fg-goose.online>", "<fn-faq-3-20260930@other.example>"]
        self.assertEqual(post_docs.older_version(new, ids), "<fn-faq-3-20260929@fn.fg-goose.online>")

    def test_nothing_older_means_no_supersedes(self):
        new = self.article("<fn-faq-3-20260927@fn.fg-goose.online>")
        self.assertIsNone(post_docs.older_version(new, ["<fn-faq-3-openbsd-20260927@fn.fg-goose.online>"]))


if __name__ == "__main__":
    unittest.main()

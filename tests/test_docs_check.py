"""tools/docs_check.py: the docs' commands and reply lines against the code."""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import docs_check  # noqa: E402


class DocsCheckTests(unittest.TestCase):
    def setUp(self):
        self.found = docs_check.inventory()

    def test_the_committed_book_is_what_the_docs_say(self):
        self.assertEqual(docs_check.ARGV_FILE.read_text(encoding="utf-8"),
                         docs_check.argv_file(self.found))

    def test_a_row_cites_its_section_never_a_line_number(self):
        # PKT-493: prose inserted above an invocation, in another section or
        # in its own, leaves the generated book byte-identical; a new
        # invocation changes it (so --check fails until it is regenerated
        # and certified, where ACL2's grammar decides the new row).
        import tempfile
        text = (docs_check.ROOT / "docs" / "operator.md").read_text(encoding="utf-8")
        head, _, rest = text.partition("\n## Native component entry\n")
        self.assertTrue(rest)

        def book(doc):
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                (root / "docs").mkdir()
                (root / "docs" / "operator.md").write_text(doc, encoding="utf-8")
                saved = docs_check.ROOT, docs_check.DOCS
                docs_check.ROOT, docs_check.DOCS = root, [root / "docs" / "operator.md"]
                try:
                    return docs_check.argv_file(docs_check.inventory())
                finally:
                    docs_check.ROOT, docs_check.DOCS = saved

        base = book(text)
        self.assertNotRegex(base, r'\("docs/operator\.md" [0-9]+ ')
        self.assertIn('("docs/operator.md#native-component-entry" 1 "help")', base)
        moved = head + "\nA new paragraph.\n\n## Native component entry\n\nMore prose.\n" + rest
        self.assertEqual(book(moved), base)
        self.assertEqual(book("Preamble line.\n" * 40 + text), base)
        added = head + ("\n## Native component entry\n\n`fn operator CONFIG store inspekt`\n"
                        + rest)
        self.assertNotEqual(book(added), base)
        self.assertIn('("docs/operator.md#native-component-entry" 1 "store" "inspekt")',
                      book(added))

    def test_section_slugs_are_fence_aware_and_numbered_on_repeat(self):
        slugs = docs_check.section_slugs(
            "intro\n# Running fn\n```\n# a comment\n```\n## Settle: `store inspect`\n"
            "x\n## Settle: `store inspect`\ny\n")
        self.assertEqual(slugs[1], "top")
        self.assertEqual(slugs[4], "running-fn")
        self.assertEqual(slugs[7], "settle-store-inspect")
        self.assertEqual(slugs[9], "settle-store-inspect-1")

    def test_every_python_invocation_parses_and_a_wrong_one_does_not(self):
        self.assertEqual(docs_check.parse_python(self.found), [])
        wrong = [("fn_client", "docs/x.md", 1, "fn_client.py fetch 1", ["fetch", "1"], None),
                 ("fn_web", "docs/x.md", 2, "fn_web.py --plane", ["--plane"], None),
                 ("bin/fn", "docs/x.md", 3, "fn --config c ruin", ["--config", "c", "ruin"],
                  None)]
        self.assertEqual(len(docs_check.parse_python(wrong)), 3)

    def test_every_reply_line_is_printable_and_an_invented_one_is_not(self):
        self.assertEqual(docs_check.check_replies(self.found), [])
        invented = [("reply", "docs/x.md", 1, "503 more matching articles than this command "
                     "may read", None, None),
                    ("reply", "docs/x.md", 2, "refused operator status NO-SUCH-REASON",
                     None, None)]
        self.assertEqual(len(docs_check.check_replies(invented)), 2)

    def test_shell_words_and_placeholders(self):
        self.assertEqual(docs_check.shell_words('"${NODE[@]}" show \'<a@b>\' | jq .',
                                                {"NODE": ["--node", "h:1"]}),
                         ["--node", "h:1", "show", "<a@b>"])
        self.assertEqual(docs_check.expand(["peer", "remove", "NAME"]),
                         (["peer", "remove", "peer1"], None))
        self.assertIsNone(docs_check.expand(["VERB", "..."])[0])


if __name__ == "__main__":
    unittest.main()

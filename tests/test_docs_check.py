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

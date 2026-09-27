"""tools/fn_agent.py's presentation of an article (PRF-252, CNS-007).

The native exchange is tests/test_native_agent_wait.py; this checks only the
client-side split of served octets into the fields an agent reads."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import fn_agent  # noqa: E402


class ArticleFieldsTests(unittest.TestCase):
    def test_fields_and_body(self):
        fields = fn_agent.article_fields(
            b"Path: n!not-for-mail\r\nFrom: alice <a@x.invalid>\r\n"
            b"Newsgroups: fn.bob, fn.alice\r\nSubject: a long\r\n\tsubject\r\n"
            b"Message-ID: <q@x.invalid>\r\nReferences: <p@x.invalid>\r\n"
            b" <o@x.invalid>\r\n\r\nline one\r\n\r\nline three\r\n")
        self.assertEqual(fields["message_id"], "<q@x.invalid>")
        self.assertEqual(fields["groups"], ["fn.bob", "fn.alice"])
        self.assertEqual(fields["from"], "alice <a@x.invalid>")
        self.assertEqual(fields["subject"], "a long subject")
        self.assertEqual(fields["references"], ["<p@x.invalid>", "<o@x.invalid>"])
        self.assertEqual(fields["body"], "line one\n\nline three\n")

    def test_field_names_are_case_insensitive_and_absent_ones_empty(self):
        fields = fn_agent.article_fields(b"message-id: <m@x>\r\n\r\nbody\r\n")
        self.assertEqual(fields["message_id"], "<m@x>")
        self.assertEqual(fields["references"], [])
        self.assertEqual(fields["groups"], [])

    def test_timeout_bound_is_the_node_bound(self):
        with self.assertRaises(SystemExit):
            fn_agent.main(["/nonexistent.json", "next", "--timeout", "3601"])


class WithdrawalTests(unittest.TestCase):
    """PKT-710: a withdrawal report (the native decoder's
    `fn-consumer-withdrawn-v1 MSGID-HEX`) is presented as its Message-ID,
    never as an article."""

    def agent(self, line, code=0):
        import subprocess
        agent = fn_agent.Agent.__new__(fn_agent.Agent)
        agent.native = lambda *words, **kw: subprocess.CompletedProcess(
            words, code, stdout=line, stderr=b"")
        return agent

    def test_withdrawn_report_is_its_message_id(self):
        record = self.agent(b"fn-consumer-withdrawn-v1 " + b"<q@x.invalid>".hex().encode()
                            + b"\n").project(None, "report")
        self.assertEqual(record, {"kind": "withdrawn", "message_id": "<q@x.invalid>"})

    def test_article_line_is_still_an_article(self):
        article = b"Message-ID: <q@x.invalid>\r\n\r\nhello\r\n"
        record = self.agent(b"fn-consumer-article-v1 " + b"<q@x.invalid>".hex().encode()
                            + b" " + article.hex().encode() + b"\n").project(None, "report")
        self.assertEqual(record["kind"], "article")
        self.assertEqual(record["body"], "hello\n")


if __name__ == "__main__":
    unittest.main()

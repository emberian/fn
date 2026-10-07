"""ARTICLE-PATH-UNVERIFIED-GUARDS: a served ARTICLE writes nothing on the
owner's stdout.

The served ARTICLE path (books/article-stream, books/article-stream-owner,
entered from host/native through fn-asto-*) ran functions that were not
guard-verified, so ACL2 executed their *1* code with guard checking
inhibited and printed "ACL2 Warning [Guards] ... Guard-checking will be
inhibited ... FN-AST-RENDER-WINDOW-AUX" on the node's stdout for every
ARTICLE.  With every function on that path guard-verified the owner runs the
compiled executable and prints nothing.  Red before: the warning line;
green after: stdout unchanged across POST + ARTICLE + BODY."""
import unittest
from tests.native_harness import Client, Node, native_image, requires

IMAGE = native_image("FN_NATIVE_HOST", "build/fn-host-developer")


@requires(IMAGE)
class NativeArticleQuietTests(unittest.TestCase):
    def test_served_article_writes_nothing_on_stdout(self):
        node = Node(self, IMAGE, name="article-quiet")
        node.init()
        owner = node.start()
        wire = (b"From: a@example.invalid\r\nNewsgroups: fn.test\r\n"
                b"Subject: quiet\r\nMessage-ID: <quiet@fn.invalid>\r\n\r\n"
                b"one\r\n.leading dot\r\n")
        with node.log_on_failure(owner):
            with Client(node.port, timeout=60) as client:
                _, final = client.post(wire)
                self.assertTrue(final.startswith(b"240"), final)
                before = owner.stdout.end
                status, served = client.multiline("ARTICLE <quiet@fn.invalid>")
                self.assertTrue(status.startswith(b"220 "), status)
                self.assertIn(b"..leading dot\r\n", served)
                status, _ = client.multiline("BODY <quiet@fn.invalid>")
                self.assertTrue(status.startswith(b"222 "), status)
            printed = owner.stdout.since(before)
            self.assertNotIn(b"ACL2 Warning", printed, printed[-2000:])
            self.assertNotIn(b"Guard-checking will be inhibited", printed, printed[-2000:])


if __name__ == "__main__":
    unittest.main()

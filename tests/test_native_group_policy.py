"""Read-only groups on a running node (O2; NNT-040, PRF-196, SCN-125).

Subjects:

* `operator CONFIG group policy NAME n|y`, offline and live, stages
  (:set-group-status NAME STATUS 0 nil), configuration delta code 21
  (books/native-admin.lisp `fn-native-admin-plan-deltas`; the fold's keystone
  `fn-cfg-set-group-status-sets-the-status`, books/config-invariants.lisp).
* The served POST step refuses an ordinary article naming a closed group with
  the 441 of `fn-post-refusal-line :group-read-only`, and LIST ACTIVE lists
  that group with status `n` from the same list
  (`fn-gst-post-gate-refuses-exactly-a-listed-n-group`,
  books/group-status.lisp, called by books/nntp-post.lisp
  `fn-nntp-post-step`).
* A connection keeps the configuration it pinned; a new connection sees the
  change; a restart replays it.

The source checks are always active.  The executable witnesses need the saved
image; when it is absent they skip and name the image they wanted.
"""
import unittest

from tests.native_harness import EXIT_OK, EXIT_REFUSED, ROOT, Node, native_image, requires


IMAGE = native_image("FN_NATIVE_HOST")

READ_ONLY = (b"441 posting failed; a group this article names is read-only here "
             b"(LIST ACTIVE status n)")


class GroupPolicySourceTests(unittest.TestCase):
    def test_the_post_step_gates_an_accepted_article(self):
        post = (ROOT / "books" / "nntp-post.lisp").read_text(encoding="ascii")
        start = post.index("(defun fn-nntp-post-step ")
        body = post[start:post.index("(defun", start + 10)]
        self.assertIn("(fn-post-gated-decision", body)
        self.assertIn("(fn-post-command-env config observation injection wire-event)", body)
        start = post.index("(defun fn-post-gated-decision")
        gated = post[start:post.index("(defthm", start)]
        self.assertLess(gated.index("(fn-inj-decide"), gated.index("(fn-gst-post-gate"))
        self.assertIn("(fn-inj-refuse :group-read-only)", gated)

    def test_the_owner_installs_the_closed_list(self):
        agent = (ROOT / "books" / "owner-agent.lisp").read_text(encoding="ascii")
        self.assertIn("(fn-cfg-closed-names (fn-cfg-value cfg)", agent)
        host = (ROOT / "host" / "owner-host.lisp").read_text(encoding="ascii")
        start = host.index("(defun fn-owner-posting-configure")
        body = host[start:host.index("(defun", start + 10)]
        self.assertIn("(fn-inj-config-closed cfg)", body)

    def test_the_delta_code_is_21(self):
        config = (ROOT / "books" / "config.lisp").read_text(encoding="ascii")
        self.assertIn("((equal kind :set-group-status) 21)", config)
        self.assertIn("((equal code 21) :set-group-status)", config)


@requires(IMAGE)
class GroupPolicyImageTests(unittest.TestCase):
    """The served POST and LIST ACTIVE run only in a saved image."""

    def setUp(self):
        self.node = Node(self, IMAGE)
        self.node.init()
        self.node.operator("group", "create", "fn.ro", expect=EXIT_OK)

    def operator(self, *words, timeout=180):
        return self.node.operator(*words, timeout=timeout)

    def reader(self):
        client = self.node.session()
        self.addCleanup(client.close)
        return client

    def active(self, client):
        status, rows = client.multiline("LIST ACTIVE")
        self.assertTrue(status.startswith(b"215"), status)
        return {row.split()[0]: row.split()[3] for row in rows.splitlines()}

    def post(self, client, group, tag):
        # Subject before Newsgroups: the octets this witness has always sent.
        article = ("From: poster@example.invalid\r\nSubject: {}\r\n"
                   "Newsgroups: {}\r\nMessage-ID: <{}@example.invalid>\r\n\r\n"
                   "Hello.\r\n").format(tag, group, tag)
        first, final = client.post(article.encode("ascii"))
        self.assertTrue(first.startswith(b"340"), first)
        return final.rstrip(b"\r\n")

    def test_read_only_group_offline_live_and_after_restart(self):
        # Offline: refused by name for an unknown group and an unserved value.
        self.assertEqual(self.operator("group", "policy", "fn.absent", "n").returncode,
                         EXIT_REFUSED)
        self.assertNotEqual(self.operator("group", "policy", "fn.ro", "m").returncode,
                            EXIT_OK)
        closed = self.operator("group", "policy", "fn.ro", "n")
        self.assertEqual(closed.returncode, EXIT_OK, closed.stderr.decode())

        owner = self.node.start()
        pinned = self.reader()
        self.assertEqual(self.active(pinned),
                         {b"fn.ro": b"n", b"fn.test": b"y"})
        # POST to the closed group, alone and cross-posted: 441 by name.
        self.assertEqual(self.post(pinned, "fn.ro", "ro-1"), READ_ONLY)
        self.assertEqual(self.post(pinned, "fn.test,fn.ro", "ro-2"),
                         READ_ONLY)
        # The open group accepts, and nothing of the refused posts is stored.
        self.assertTrue(self.post(pinned, "fn.test", "ok-1")
                        .startswith(b"240"))
        status = pinned.command("STAT <ro-1@example.invalid>")
        self.assertTrue(status.startswith(b"430"), status)

        # Live: reopen the group.  A new connection sees "y" and posts; the
        # connection that pinned the old configuration keeps its answer.
        opened = self.operator("group", "policy", "fn.ro", "y")
        self.assertEqual(opened.returncode, EXIT_OK, opened.stderr.decode())
        fresh = self.reader()
        self.assertEqual(self.active(fresh),
                         {b"fn.ro": b"y", b"fn.test": b"y"})
        self.assertTrue(self.post(fresh, "fn.ro", "ro-3")
                        .startswith(b"240"))
        # Live again: close it; a new connection is refused.
        closed = self.operator("group", "policy", "fn.ro", "n")
        self.assertEqual(closed.returncode, EXIT_OK, closed.stderr.decode())
        third = self.reader()
        self.assertEqual(self.post(third, "fn.ro", "ro-4"), READ_ONLY)
        self.node.stop(process=owner)

        # A restart replays the last record: fn.ro is "n".
        restarted = self.node.start()
        after = self.reader()
        self.assertEqual(self.active(after),
                         {b"fn.ro": b"n", b"fn.test": b"y"})
        self.assertEqual(self.post(after, "fn.ro", "ro-5"), READ_ONLY)
        self.node.stop(process=restarted)


if __name__ == "__main__":
    unittest.main()

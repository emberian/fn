"""tools/fn_client.py against the fake node, one test per behaviour.

The fake wraps its socket in real TLS, so the handshake, the login and the
posting handshake are exercised end to end over loopback.  Each test names the
one thing about the node it changes and the outcome that change must produce,
and asserts the exit code every time, because the exit code is what an agent
shelling to this reads.  Nothing here runs against a deployed node.

The three outcomes are the point (AGENTS.md, D13): `accepted`, `refused` and
`uncertain` have to stay apart, so the two 441 lines that
`books/nntp-post.lisp` keeps distinct are asserted to land on 1 and on 3, and
a post whose reply never arrives is asserted to land on 3 with its Message-ID
in the output rather than on either of the others.
"""
import contextlib
import io
import json
import os
import pathlib
import shutil
import sys
import tempfile
import unittest
from unittest import mock

from tests.fake_node import FakeNode, make_pair

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import fn_client  # noqa: E402


@unittest.skipUnless(shutil.which("openssl"), "no openssl to make a certificate")
class FnClientTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.dir = pathlib.Path(cls.tmp.name)
        cls.cert, cls.key = make_pair(cls.dir)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def setUp(self):
        self.work = pathlib.Path(tempfile.mkdtemp(dir=self.dir))
        self.state = self.work / "state.json"

    def serve(self, **kw):
        node = FakeNode(self.cert, self.key, **kw)
        node.start()
        self.addCleanup(node.stop)
        return node

    def run_client(self, node, argv, password="right", plain=False, credentials=None,
                   stdin=""):
        out, err = io.StringIO(), io.StringIO()
        base = ["--node", "127.0.0.1:%d" % node.port, "--timeout", "10",
                "--state", str(self.state)]
        base += ["--plain"] if plain else ["--cafile", str(self.cert)]
        if credentials:
            base += ["--credentials", str(credentials)]
        environ = {"FN_CLIENT_USER": "yue", "FN_CLIENT_PASSWORD": password}
        with mock.patch.dict(os.environ, environ):
            with mock.patch.object(sys, "stdin", io.StringIO(stdin)):
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    code = fn_client.main(base + list(argv))
        return code, out.getvalue(), err.getvalue()

    def document(self, text):
        return json.loads(text)

    def marks(self):
        return json.loads(self.state.read_text())["watermarks"] if self.state.exists() else {}

    # ---- the four subcommands over TLS and a login ----------------------

    def test_groups_lists_each_served_name_with_its_water_marks(self):
        node = self.serve(groups=("fn.agents", "fn.humans"))
        node.seed("fn.agents", "first", "one")
        node.seed("fn.agents", "second", "two")
        code, out, err = self.run_client(node, ["groups"])
        self.assertEqual(code, 0, err)
        self.assertEqual(err.split()[0], "done")
        self.assertRegex(out, r"fn\.agents\s+2\s+1\s+2")
        self.assertRegex(out, r"fn\.humans\s+0\s+1\s+0")

    def test_read_prints_the_headers_and_the_body_and_advances_the_watermark(self):
        node = self.serve()
        node.seed("fn.agents", "first", "hello from tulip")
        code, out, err = self.run_client(node, ["read", "fn.agents"])
        self.assertEqual(code, 0, err)
        self.assertIn("Subject: first", out)
        self.assertIn("hello from tulip", out)
        self.assertEqual(self.marks(), {"fn.agents": 1})
        again = self.run_client(node, ["read", "fn.agents"])
        self.assertEqual(again[0], 0, again[2])
        self.assertIn("no articles in fn.agents after 1", again[1])

    def test_show_fetches_one_article_by_message_id_and_leaves_the_watermark_alone(self):
        node = self.serve()
        node.seed("fn.agents", "one", "body one", msgid="<one@fake.invalid>")
        node.seed("fn.agents", "two", "body two", msgid="<two@fake.invalid>")
        code, out, err = self.run_client(node, ["show", "<two@fake.invalid>"])
        self.assertEqual(code, 0, err)
        self.assertIn("body two", out)
        self.assertNotIn("body one", out)
        self.assertEqual(self.marks(), {})

    def test_show_by_message_id_carries_no_article_number_in_json(self):
        # The hbox node answered `220 0 <id> article follows` to ARTICLE by
        # Message-ID, as RFC 3977 section 6.2.1 says, and --json carried
        # `"number": 0` although the text rendering already knew 0 is not an
        # article number.  An agent keying on the JSON would file it as 0.
        node = self.serve()
        node.seed("fn.agents", "one", "body one", msgid="<one@fake.invalid>")
        code, out, err = self.run_client(node, ["show", "<one@fake.invalid>", "--json"])
        self.assertEqual(code, 0, err)
        document = self.document(out)
        self.assertTrue(any(one.startswith("220 0 ") for one in document["status_lines"]))
        self.assertIsNone(document["articles"][0]["number"])
        code, out, err = self.run_client(node, ["show", "1", "--group", "fn.agents", "--json"])
        self.assertEqual(code, 0, err)
        self.assertEqual(self.document(out)["articles"][0]["number"], 1)

    def test_post_sends_the_article_and_the_node_can_read_it_back(self):
        node = self.serve()
        body = self.work / "body.txt"
        body.write_text("yue was here\n")
        code, out, err = self.run_client(
            node, ["post", "fn.agents", "--subject", "hi", "--body-file", str(body)])
        self.assertEqual(code, 0, err)
        self.assertEqual(err.split()[0], "accepted")
        msgid = [one for one in node.articles if one.startswith("<fn-client.")]
        self.assertEqual(len(msgid), 1)
        self.assertIn(msgid[0], err)
        self.assertIn("yue was here", node.articles[msgid[0]])
        back = self.run_client(node, ["show", msgid[0]])
        self.assertEqual(back[0], 0, back[2])
        self.assertIn("yue was here", back[1])

    def test_post_takes_the_body_from_standard_input_and_the_given_message_id(self):
        node = self.serve()
        code, out, err = self.run_client(
            node, ["post", "fn.agents", "--subject", "hi", "--message-id",
                   "<chosen@yue.invalid>", "--references", "<earlier@yue.invalid>"],
            stdin="from stdin\n")
        self.assertEqual(code, 0, err)
        self.assertIn("from stdin", node.articles["<chosen@yue.invalid>"])
        self.assertIn("References: <earlier@yue.invalid>",
                      node.articles["<chosen@yue.invalid>"])

    # ---- the channel and the login --------------------------------------

    def test_plain_against_a_node_that_needs_no_login_reads_without_tls_or_authinfo(self):
        node = self.serve(protected_only=False, require_auth=False)
        node.seed("fn.agents", "open", "no login here")
        code, out, err = self.run_client(node, ["read", "fn.agents"], plain=True)
        self.assertEqual(code, 0, err)
        self.assertIn("no login here", out)
        self.assertNotIn("STARTTLS", node.seen)
        self.assertEqual([one for one in node.seen if one.startswith("AUTHINFO")], [])

    def test_a_command_before_the_login_is_refused_with_the_node_480(self):
        node = self.serve(protected_only=False)
        node.seed("fn.agents", "closed", "needs a login")
        code, out, err = self.run_client(node, ["read", "fn.agents"], plain=True)
        self.assertEqual(code, 1)
        self.assertIn("480 authentication required", err)
        self.assertNotIn("needs a login", out)
        self.assertEqual(self.marks(), {})

    def test_authinfo_before_tls_is_reported_as_the_node_483_and_no_password_is_sent(self):
        node = self.serve(offer_starttls=False)
        code, out, err = self.run_client(node, ["groups"])
        self.assertEqual(code, 1)
        self.assertIn("483 a protected channel is required", err)
        self.assertIn("no STARTTLS", err)
        self.assertNotIn("AUTHINFO PASS *", node.seen)

    def test_a_node_that_would_take_the_password_in_the_clear_never_gets_it(self):
        node = self.serve(offer_starttls=False, protected_only=False)
        code, out, err = self.run_client(node, ["groups"])
        self.assertEqual(code, 1)
        self.assertIn("381", err)
        self.assertIn("in the clear", err)
        self.assertNotIn("AUTHINFO PASS *", node.seen)

    def test_a_wrong_password_is_the_node_481_and_not_an_uncertain_outcome(self):
        node = self.serve()
        code, out, err = self.run_client(node, ["groups"], password="wrong")
        self.assertEqual(code, 1)
        self.assertIn("481 authentication failed", err)

    def test_a_node_that_is_not_listening_is_uncertain_and_not_refused(self):
        node = self.serve()
        node.stop()
        code, out, err = self.run_client(node, ["groups"])
        self.assertEqual(code, 3)
        self.assertEqual(err.split()[0], "uncertain")

    def test_a_node_that_accepts_and_then_closes_is_uncertain_and_not_a_traceback(self):
        # The frozen 915d5c72 node behind an `ssh -L` tunnel, once its owner
        # had stopped: the forwarder accepted on this side and closed before
        # the greeting.  The greeting is read inside the Session constructor,
        # so this arrives as `Disconnected` and not as an `OSError`, and the
        # client used to let it out as a traceback with the refused exit.
        node = self.serve(drop_before_greeting=True)
        code, out, err = self.run_client(node, ["groups"], plain=True)
        self.assertEqual(code, 3, err)
        self.assertEqual(err.split()[0], "uncertain")
        self.assertIn("closed the connection", err)

    def test_a_node_named_by_an_ipv6_address_is_reached_at_that_address(self):
        # `[listener] host` admits `::1` (docs/operator.md), and the tunnel
        # the same page prescribes listens on `::1` as well as 127.0.0.1.
        # `--node [::1]:PORT` used to fail the name lookup and report the
        # node unreachable while it was serving.
        try:
            node = self.serve(host="::1", protected_only=False, require_auth=False)
        except OSError as exc:                       # no IPv6 loopback here
            self.skipTest("no ::1 to listen on: %s" % exc)
        node.seed("fn.agents", "over six", "the address is the whole token")
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = fn_client.main(["--node", "[::1]:%d" % node.port, "--plain", "--timeout",
                                   "10", "--state", str(self.state), "read", "fn.agents"])
        self.assertEqual(code, 0, err.getvalue())
        self.assertIn("the address is the whole token", out.getvalue())
        self.assertIn("[::1]:%d" % node.port, err.getvalue())

    def test_the_node_address_is_split_where_rfc_3986_says_and_nowhere_else(self):
        self.assertEqual(fn_client.split_node("192.168.50.39:1119"), ("192.168.50.39", "1119"))
        self.assertEqual(fn_client.split_node("hbox"), ("hbox", str(fn_client.DEFAULT_PORT)))
        self.assertEqual(fn_client.split_node("[::1]:11340"), ("::1", "11340"))
        self.assertEqual(fn_client.split_node("[::1]"), ("::1", str(fn_client.DEFAULT_PORT)))
        # The one that mattered: `::1` is an address, not `::` at port 1.
        self.assertEqual(fn_client.split_node("::1"), ("::1", str(fn_client.DEFAULT_PORT)))
        self.assertEqual(fn_client.split_node("[::1"), (None, None))
        for bad in ("[::1", "[::1]:0", "[::1]:99999", "host:not-a-port"):
            with self.subTest(node=bad):
                with contextlib.redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit) as stop:
                        fn_client.main(["--node", bad, "--plain", "groups"])
                self.assertEqual(stop.exception.code, 2)

    def test_a_certificate_the_client_does_not_trust_is_refused_and_nothing_follows_the_382(self):
        # The hbox node from the dabebb84 image, 2026-09-22, with a --cafile
        # that was not its certificate: the node answered 382, the handshake
        # failed verification, and the client reported `uncertain` on exit 3,
        # dropped the 382 from the status lines, and then wrote a cleartext
        # QUIT onto the stream the node was reading as TLS.  What happened is
        # known exactly -- no command reached the node after the 382 -- so
        # the outcome is refused, and not one octet follows the handshake.
        other = pathlib.Path(tempfile.mkdtemp(dir=self.work))
        cert, _ = make_pair(other)
        node = self.serve()
        sent = []
        original = fn_client.Session.send

        def spy(session, text):
            sent.append(text)
            original(session, text)

        out, err = io.StringIO(), io.StringIO()
        with mock.patch.dict(os.environ, {"FN_CLIENT_USER": "yue",
                                          "FN_CLIENT_PASSWORD": "right"}):
            with mock.patch.object(fn_client.Session, "send", spy):
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    code = fn_client.main(["--node", "127.0.0.1:%d" % node.port, "--cafile",
                                           str(cert), "--timeout", "10", "--state",
                                           str(self.state), "--json", "groups"])
        self.assertEqual(code, 1, err.getvalue())
        document = self.document(out.getvalue())
        self.assertEqual(document["outcome"], "refused")
        self.assertIn("did not verify against --cafile", document["detail"])
        self.assertTrue(any(one.startswith("382") for one in document["status_lines"]))
        self.assertEqual(sent, ["CAPABILITIES", "STARTTLS"])
        self.assertNotIn("AUTHINFO PASS *", node.seen)

    def test_a_handshake_the_node_abandons_is_uncertain_and_not_refused(self):
        # The other arm of the split above: the node said 382 and then closed
        # instead of negotiating.  Nothing verified or failed to verify; the
        # connection failed, which stays uncertain.
        node = self.serve(close_after_382=True)
        code, out, err = self.run_client(node, ["groups"])
        self.assertEqual(code, 3, err)
        self.assertEqual(err.split()[0], "uncertain")
        self.assertIn("handshake", err)

    # ---- posting refusals and the uncertain outcome ---------------------

    def test_a_login_enrolled_without_posting_is_the_node_440(self):
        node = self.serve(accept_post=False)
        code, out, err = self.run_client(
            node, ["post", "fn.agents", "--subject", "hi"], stdin="body\n")
        self.assertEqual(code, 1)
        self.assertIn("440 posting not permitted for this principal", err)

    def test_a_refused_article_is_the_node_441_and_exits_refused(self):
        node = self.serve(refuse_post=True)
        code, out, err = self.run_client(
            node, ["post", "fn.agents", "--subject", "hi"], stdin="body\n")
        self.assertEqual(code, 1)
        self.assertIn("441 posting failed; the article was refused", err)
        self.assertNotIn("uncertain", err)

    def test_the_node_uncertain_441_is_uncertain_and_never_reported_as_refused(self):
        node = self.serve(uncertain_post=True)
        code, out, err = self.run_client(
            node, ["post", "fn.agents", "--subject", "hi"], stdin="body\n")
        self.assertEqual(code, 3)
        self.assertEqual(err.split()[0], "uncertain")
        self.assertIn("do not repost", err)
        self.assertIn("@yue.invalid>", err)

    def test_a_post_whose_reply_never_arrives_exits_uncertain_and_prints_the_message_id(self):
        node = self.serve(drop_after_article=True)
        code, out, err = self.run_client(
            node, ["post", "fn.agents", "--subject", "hi"], stdin="body\n")
        self.assertEqual(code, 3)
        self.assertEqual(err.split()[0], "uncertain")
        self.assertIn("may or may not be durable", err)
        sent = [one for one in node.articles if one.startswith("<fn-client.")]
        self.assertEqual(len(sent), 0, "the fake stored nothing; the client cannot know that")
        self.assertRegex(err, r"<fn-client\.\d{8}T\d{6}Z\.[0-9a-f]{8}@yue\.invalid>")

    # ---- NNT-019: a lost reply is settled by re-sending the same article --

    def lost_post(self, node, draft):
        code, out, err = self.run_client(
            node, ["post", "fn.agents", "--subject", "hi", "--draft", str(draft)],
            stdin="the exact body\n")
        self.assertEqual(code, 3, err)
        return json.loads(draft.read_text())

    def test_a_lost_reply_then_withdrawal_reconciles_to_already_stored(self):
        node = self.serve(d25=True, commit_then_drop=True)
        draft = self.work / "draft.json"
        kept = self.lost_post(node, draft)
        msgid = kept["message_id"]
        self.assertEqual(kept["original"]["outcome"], "uncertain")
        self.assertIn(msgid, node.articles)                  # it WAS stored
        node.withdrawn.add(msgid)
        code, out, err = self.run_client(node, ["show", msgid, "--json"])
        self.assertEqual(code, 1)
        self.assertEqual(self.document(out)["visibility"], "not-visible")
        self.assertIn("not evidence about acceptance", err)
        held = dict(node.articles)
        code, out, err = self.run_client(node, ["reconcile", str(draft), "--json"])
        self.assertEqual(code, 0, err)
        document = self.document(out)
        self.assertEqual((document["outcome"], document["settled"]),
                         ("accepted", "already-stored"))
        self.assertEqual(document["message_id"], msgid)
        self.assertEqual(node.articles, held)                 # nothing stored twice
        final = json.loads(draft.read_text())
        self.assertEqual(final["original"]["outcome"], "uncertain")   # never rewritten
        self.assertEqual([r["settled"] for r in final["reconciliations"]], ["already-stored"])

    def test_a_reconcile_where_nothing_was_stored_is_the_one_acceptance(self):
        node = self.serve(d25=True, drop_after_article=True)
        draft = self.work / "draft.json"
        kept = self.lost_post(node, draft)
        self.assertNotIn(kept["message_id"], node.articles)
        node.drop_after_article = False
        code, out, err = self.run_client(node, ["reconcile", str(draft), "--json"])
        self.assertEqual(code, 0, err)
        self.assertEqual(self.document(out)["settled"], "accepted-now")
        self.assertEqual(node.articles[kept["message_id"]], kept["lines"])

    def test_a_different_article_under_the_message_id_settles_as_refused(self):
        node = self.serve(d25=True, drop_after_article=True)
        draft = self.work / "draft.json"
        kept = self.lost_post(node, draft)
        node.drop_after_article = False
        node.inject("fn.agents", [line.replace("the exact body", "someone else's")
                                  for line in kept["lines"]])
        code, out, err = self.run_client(node, ["reconcile", str(draft), "--json"])
        self.assertEqual(code, 1, err)
        self.assertEqual(self.document(out)["settled"], "conflict")

    def test_a_resend_refused_for_another_reason_is_unresolved_and_never_absent(self):
        node = self.serve(d25=True, commit_then_drop=True)
        draft = self.work / "draft.json"
        self.lost_post(node, draft)
        node.accept_post = False            # the login lost its posting permission
        code, out, err = self.run_client(node, ["reconcile", str(draft), "--json"])
        self.assertEqual(code, 4, err)
        document = self.document(out)
        self.assertEqual((document["outcome"], document["settled"]),
                         ("unresolved", "unresolved"))
        self.assertIn("440", err)
        final = json.loads(draft.read_text())
        self.assertEqual(final["original"]["outcome"], "uncertain")
        self.assertEqual(final["reconciliations"][-1]["outcome"], "unresolved")

    def test_a_lost_reconcile_reply_is_unresolved(self):
        node = self.serve(d25=True, drop_after_article=True)
        draft = self.work / "draft.json"
        self.lost_post(node, draft)
        code, out, err = self.run_client(node, ["reconcile", str(draft)])
        self.assertEqual(code, 4, err)
        self.assertTrue(err.startswith("unresolved"), err)

    def test_an_accepted_draft_is_not_resent(self):
        node = self.serve(d25=True)
        draft = self.work / "draft.json"
        code, out, err = self.run_client(
            node, ["post", "fn.agents", "--subject", "hi", "--draft", str(draft)],
            stdin="body\n")
        self.assertEqual(code, 0, err)
        seen = len(node.seen)
        code, out, err = self.run_client(node, ["reconcile", str(draft)])
        self.assertEqual(code, 0, err)
        self.assertIn("nothing to reconcile", err)
        self.assertEqual(len(node.seen), seen)

    def test_an_existing_draft_path_is_a_usage_error_and_nothing_is_sent(self):
        node = self.serve(d25=True)
        draft = self.work / "draft.json"
        draft.write_text("{}")
        with self.assertRaises(SystemExit) as stopped:
            self.run_client(node, ["post", "fn.agents", "--subject", "hi",
                                   "--draft", str(draft)], stdin="body\n")
        self.assertEqual(stopped.exception.code, 2)
        self.assertEqual(node.articles, {})

    # ---- the watermark ---------------------------------------------------

    def test_the_watermark_is_written_only_after_the_articles_have_been_printed(self):
        node = self.serve()
        node.seed("fn.agents", "ordered", "the body")
        seen = []
        out, err = io.StringIO(), io.StringIO()
        original = fn_client.save_state

        def spy(path, node_name, marks):
            seen.append(out.getvalue())
            original(path, node_name, marks)

        with mock.patch.dict(os.environ, {"FN_CLIENT_USER": "yue",
                                          "FN_CLIENT_PASSWORD": "right"}):
            with mock.patch.object(fn_client, "save_state", spy):
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    code = fn_client.main(["--node", "127.0.0.1:%d" % node.port, "--cafile",
                                           str(self.cert), "--timeout", "10", "--state",
                                           str(self.state), "read", "fn.agents"])
        self.assertEqual(code, 0, err.getvalue())
        self.assertEqual(len(seen), 1)
        self.assertIn("the body", seen[0])

    def test_a_refused_read_leaves_the_watermark_where_the_last_good_read_left_it(self):
        node = self.serve(protected_only=False)
        node.seed("fn.agents", "one", "body one")
        node.seed("fn.agents", "two", "body two")
        self.assertEqual(self.run_client(node, ["read", "fn.agents"])[0], 0)
        self.assertEqual(self.marks(), {"fn.agents": 2})
        node.seed("fn.agents", "three", "body three")
        code, out, err = self.run_client(node, ["read", "fn.agents"], plain=True)
        self.assertEqual(code, 1)
        self.assertIn("480", err)
        self.assertEqual(self.marks(), {"fn.agents": 2})
        self.assertEqual(self.run_client(node, ["read", "fn.agents"])[0], 0)
        self.assertEqual(self.marks(), {"fn.agents": 3})

    def test_an_article_refused_in_the_middle_of_a_range_leaves_the_watermark_alone(self):
        node = self.serve(fail_article=2)
        for word in ("one", "two", "three"):
            node.seed("fn.agents", word, "body " + word)
        code, out, err = self.run_client(node, ["read", "fn.agents"])
        self.assertEqual(code, 1)
        self.assertIn("403 internal fault", err)
        self.assertIn("body one", out, "what was already read is still printed")
        self.assertNotIn("body three", out)
        self.assertEqual(self.marks(), {})

    def test_since_and_all_choose_the_window_without_consulting_the_watermark(self):
        node = self.serve()
        for word in ("one", "two", "three"):
            node.seed("fn.agents", word, "body " + word)
        self.assertEqual(self.run_client(node, ["read", "fn.agents"])[0], 0)
        code, out, err = self.run_client(node, ["read", "fn.agents", "--since", "1"])
        self.assertEqual(code, 0, err)
        self.assertNotIn("body one", out)
        self.assertIn("body two", out)
        code, out, err = self.run_client(node, ["read", "fn.agents", "--all"])
        self.assertEqual(code, 0, err)
        self.assertIn("body one", out)
        self.assertIn("body three", out)

    def test_a_watermark_that_cannot_be_saved_keeps_the_node_outcome_and_says_so(self):
        # The read happened and the article is out; only this side's note of
        # how far it got failed.  That is not the node refusing, so it must
        # not arrive as the refused exit -- and it used to arrive as a
        # traceback on exit 1.
        blocked = self.work / "not-a-directory"
        blocked.write_text("")
        self.state = blocked / "state.json"
        node = self.serve()
        node.seed("fn.agents", "one", "body one")
        code, out, err = self.run_client(node, ["read", "fn.agents"])
        self.assertEqual(code, 0, err)
        self.assertIn("body one", out)
        self.assertIn("the watermark was not saved", err)
        self.assertIn("offers these articles again", err)
        self.assertFalse(self.state.exists())

    def test_a_negative_since_is_a_usage_error_and_never_reaches_the_node(self):
        # It used to reach it: `OVER 0-N` and then `ARTICLE 0`, which the
        # frozen 915d5c72 node answered `501 syntax error` twice, so a
        # client-side mistake came back wearing the node's refusal.
        node = self.serve()
        node.seed("fn.agents", "one", "body one")
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as stop:
                self.run_client(node, ["read", "fn.agents", "--since", "-1"])
        self.assertEqual(stop.exception.code, 2)
        self.assertEqual(node.seen, [])

    def test_a_441_line_this_fake_had_never_sent_is_still_a_refusal(self):
        # The frozen 915d5c72 node answered this to an article whose Subject
        # held non-ASCII octets.  books/nntp-post.lisp has more than twenty
        # such lines and the fake knew two of them; a client that recognised
        # a refusal by its wording rather than by its code would have shipped
        # an uncertain outcome for a plain refusal.
        node = self.serve(refuse_post=True,
                          refusal="441 posting failed; the article is not valid syntax")
        code, out, err = self.run_client(
            node, ["post", "fn.agents", "--subject", "hi"], stdin="body\n")
        self.assertEqual(code, 1)
        self.assertIn("441 posting failed; the article is not valid syntax", err)
        self.assertNotIn("uncertain", err)

    def test_a_read_of_a_group_the_node_does_not_carry_is_the_node_411(self):
        node = self.serve()
        code, out, err = self.run_client(node, ["read", "fn.absent"])
        self.assertEqual(code, 1)
        self.assertIn("411 no such newsgroup", err)
        self.assertEqual(self.marks(), {})

    # ---- the secret, the credential file, and the JSON ------------------

    def test_the_password_reaches_neither_the_output_nor_the_state(self):
        node = self.serve(password="s3cret-word-9")
        node.seed("fn.agents", "one", "body one")
        code, out, err = self.run_client(node, ["read", "fn.agents", "--json"],
                                         password="s3cret-word-9")
        self.assertEqual(code, 0, err)
        self.assertNotIn("s3cret-word-9", out)
        self.assertNotIn("s3cret-word-9", err)
        self.assertNotIn("s3cret-word-9", self.state.read_text())

    def test_a_status_line_that_quotes_the_password_back_is_not_printed(self):
        node = self.serve(echo_password=True)
        code, out, err = self.run_client(node, ["groups"], password="s3cret-word-9")
        self.assertEqual(code, 1)
        self.assertNotIn("s3cret-word-9", out)
        self.assertNotIn("s3cret-word-9", err)
        self.assertIn("held the password", err)

    def test_a_credentials_file_the_group_can_read_is_a_usage_error(self):
        path = self.work / "credentials"
        path.write_text("yue right\n")
        os.chmod(str(path), 0o644)
        node = self.serve()
        with self.assertRaises(SystemExit) as stop:
            self.run_client(node, ["groups"], credentials=path)
        self.assertEqual(stop.exception.code, 2)
        self.assertEqual(node.seen, [])

    def test_a_credentials_file_at_0600_logs_in_and_keeps_the_password_off_argv(self):
        path = self.work / "credentials"
        path.write_text("yue right\n")
        os.chmod(str(path), 0o600)
        node = self.serve()
        code, out, err = self.run_client(node, ["groups"], password="", credentials=path)
        self.assertEqual(code, 0, err)
        self.assertIn("AUTHINFO PASS *", node.seen)

    def test_json_carries_every_status_line_the_node_sent_and_the_exit_code(self):
        node = self.serve()
        node.seed("fn.agents", "one", "body one")
        code, out, err = self.run_client(node, ["read", "fn.agents", "--json"])
        self.assertEqual(code, 0, err)
        document = self.document(out)
        self.assertEqual(document["outcome"], "done")
        self.assertEqual(document["exit"], 0)
        self.assertEqual(document["watermark_after"], 1)
        self.assertIsNone(document["watermark_before"])
        self.assertIn("200 fake node ready", document["status_lines"])
        self.assertIn("281 authentication accepted", document["status_lines"])
        self.assertTrue(any(one.startswith("382") for one in document["status_lines"]))
        self.assertEqual(document["articles"][0]["subject"], "one")
        self.assertEqual(document["articles"][0]["body"], ["body one"])

    def test_a_refusal_in_json_carries_the_status_line_and_the_refused_exit(self):
        node = self.serve()
        code, out, err = self.run_client(node, ["read", "fn.absent", "--json"])
        self.assertEqual(code, 1)
        document = self.document(out)
        self.assertEqual(document["outcome"], "refused")
        self.assertEqual(document["exit"], 1)
        self.assertIn("411", document["detail"])

    def test_naming_no_subcommand_or_no_channel_choice_is_a_usage_error(self):
        for argv in ([], ["groups"], ["--plain", "--cafile", str(self.cert), "groups"]):
            with self.subTest(argv=argv):
                with contextlib.redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit) as stop:
                        fn_client.main(argv)
                self.assertEqual(stop.exception.code, 2)


if __name__ == "__main__":
    unittest.main()

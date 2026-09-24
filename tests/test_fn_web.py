"""The separate web client against an actual NNTP socket and HTTP requests."""
from concurrent.futures import ThreadPoolExecutor
import http.client
import html
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile
import threading
import unittest
from unittest import mock
from types import SimpleNamespace
from urllib.parse import urlencode

from tests.fake_node import FakeNode, make_pair

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import fn_web  # noqa: E402


@unittest.skipUnless(shutil.which("openssl"), "openssl is required for the socket fixture")
class WebClientTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.cert, cls.key = make_pair(Path(cls.temporary.name))

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def setUp(self):
        self.node = FakeNode(self.cert, self.key,
                             protected_only=False, require_auth=False)
        self.node.start()
        args = SimpleNamespace(host="127.0.0.1", port=self.node.port,
                               timeout=5.0, plain=True, cafile=None)
        self.server = fn_web.WebServer(0, fn_web.Backend(args, "", ""))
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()

    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join(5)
        self.node.stop()
        if hasattr(self, "outbox_temp"):
            self.outbox_temp.cleanup()

    def enable_outbox(self):
        self.outbox_temp = tempfile.TemporaryDirectory()
        self.outbox_path = Path(self.outbox_temp.name) / "submissions"
        self.restart_outbox()

    def restart_outbox(self):
        backend = self.server.backend
        self.server.shutdown()
        self.server.server_close()
        self.thread.join(5)
        self.server = fn_web.WebServer(0, backend, self.outbox_path)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()

    def request(self, method, path, body=None, origin=True):
        connection = http.client.HTTPConnection("127.0.0.1", self.server.server_port,
                                                 timeout=10)
        headers = {}
        if method == "POST":
            headers["Content-Type"] = "application/x-www-form-urlencoded"
            if origin:
                headers["Origin"] = "http://127.0.0.1:%d" % self.server.server_port
            submission_id = (body or {}).get("submission_id") or self.form_id()
            body = urlencode({"csrf": self.server.token, "submission_id": submission_id,
                              "group": "fn.agents",
                              "subject": "hello", "sender": "human <h@local.invalid>",
                              "references": "", "body": "A real post"} | (body or {}))
        connection.request(method, path, body=body, headers=headers)
        reply = connection.getresponse()
        data = reply.read().decode("utf-8")
        result = reply.status, dict(reply.getheaders()), data
        connection.close()
        return result

    def form_id(self):
        status, _, page = self.request("GET", "/compose?group=fn.agents")
        self.assertEqual(status, 200)
        return re.search(r"name='submission_id' value='([^']+)'", page).group(1)

    def post(self, body=None, origin=True):
        status, headers, page = self.request("POST", "/post", body, origin)
        if status == 303:
            return self.request("GET", headers["Location"])
        return status, headers, page

    def test_groups_recent_article_and_escaped_source(self):
        self.node.inject("fn.agents", ["From: <script>alert(1)</script>",
                                       "Newsgroups: fn.agents",
                                       "Subject: Hello <img src=https://bad.invalid/x>",
                                       "Message-ID: <one@fake.invalid>",
                                       "Path: peer!other", "Injection-Info: gateway",
                                       "FN-Statement: opaque-evidence", "",
                                       "<script>steal()</script>"])
        status, headers, page = self.request("GET", "/")
        self.assertEqual(status, 200)
        self.assertIn("fn.agents", page)
        self.assertIn("default-src 'none'", headers["Content-Security-Policy"])
        self.assertEqual(headers["Cache-Control"], "no-store")
        self.assertEqual(headers["Referrer-Policy"], "same-origin")
        status, _, page = self.request("GET", "/g?name=fn.agents")
        self.assertEqual(status, 200)
        self.assertIn("Hello &lt;img src=https://bad.invalid/x&gt;", page)
        self.assertIn("/a?group=fn.agents&amp;number=1", page)
        status, _, page = self.request("GET", "/a?group=fn.agents&number=1")
        self.assertEqual(status, 200)
        self.assertIn("&lt;script&gt;steal()&lt;/script&gt;", page)
        self.assertNotIn("<script>steal()", page)
        self.assertIn("FN-Statement present; not verified here", page)
        self.assertIn("Path: peer!other", page)
        self.assertIn("Viewing does not acknowledge application processing", page)

    def test_recent_window_and_older_newer_boundaries_are_number_based(self):
        for number in range(1, 96):
            self.node.seed("fn.agents", "slot-%03d" % number, "body")

        status, _, recent = self.request("GET", "/g?name=fn.agents")
        self.assertEqual(status, 200)
        self.assertIn("Local article numbers 56–95", recent)
        self.assertIn("slot-095", recent)
        self.assertNotIn("slot-055", recent)
        self.assertIn("start=16&amp;end=55", recent)
        self.assertNotIn("rel='next'", recent)
        self.assertIn("OVER 56-95", self.node.seen)

        status, _, oldest = self.request(
            "GET", "/g?name=fn.agents&start=1&end=40")
        self.assertEqual(status, 200)
        self.assertIn("Local article numbers 1–40", oldest)
        self.assertNotIn("rel='prev'", oldest)
        self.assertIn("start=41&amp;end=80", oldest)
        self.assertIn("OVER 1-40", self.node.seen)

        # Current low is the terminal older boundary even if an explicit
        # request names historical number slots below it.
        for number in range(1, 31):
            self.node.numbers["fn.agents"].pop(number)
        status, _, at_low = self.request(
            "GET", "/g?name=fn.agents&start=31&end=70")
        self.assertEqual(status, 200)
        self.assertIn("group currently spans 31–95", at_low)
        self.assertNotIn("rel='prev'", at_low)

    def test_empty_group_has_no_window_or_overview_request(self):
        self.node.numbers["fn.empty"] = {}
        # A native group may retain a high local-number watermark after its
        # articles are gone; GROUP then reports 0, watermark, watermark - 1.
        self.node.summary_overrides["fn.empty"] = (0, 100, 99)
        status, _, page = self.request("GET", "/g?name=fn.empty")
        self.assertEqual(status, 200)
        self.assertIn("No local article numbers", page)
        self.assertIn("No articles in this number window", page)
        self.assertIn("group currently has no articles", page)
        self.assertNotIn("rel='prev'", page)
        self.assertNotIn("rel='next'", page)
        self.assertNotIn("OVER", self.node.seen)
        self.assertIn("GROUP fn.empty", self.node.seen)

        # An explicit requested window remains explicit, while the empty
        # group has no older/newer frontier to navigate.
        status, _, explicit = self.request(
            "GET", "/g?name=fn.empty&start=5&end=10")
        self.assertEqual(status, 200)
        self.assertIn("Local article numbers 5–10", explicit)
        self.assertNotIn("rel='prev'", explicit)
        self.assertNotIn("rel='next'", explicit)
        self.assertIn("OVER 5-10", self.node.seen)

    def test_sparse_and_empty_windows_keep_the_requested_slots_navigable(self):
        for number in range(1, 101):
            self.node.seed("fn.agents", "slot-%03d" % number, "body")
        table = self.node.numbers["fn.agents"]
        keep = {42, 55, 80, 100}
        for number in list(table):
            if number not in keep and number >= 41:
                del table[number]

        status, _, sparse = self.request(
            "GET", "/g?name=fn.agents&start=41&end=80")
        self.assertEqual(status, 200)
        self.assertIn("slot-042", sparse)
        self.assertIn("slot-055", sparse)
        self.assertIn("slot-080", sparse)
        self.assertNotIn("slot-041", sparse)
        self.assertIn("OVER 41-80", self.node.seen)

        # Slots 81–99 are real holes, while article 100 keeps the group
        # frontier there. The empty window still offers both directions.
        status, _, empty = self.request(
            "GET", "/g?name=fn.agents&start=81&end=99")
        self.assertEqual(status, 200)
        self.assertIn("No articles in this number window", empty)
        self.assertIn("start=41&amp;end=80", empty)
        self.assertIn("start=100&amp;end=139", empty)
        self.assertIn("OVER 81-99", self.node.seen)

    def test_explicit_window_does_not_slide_when_new_articles_arrive(self):
        for number in range(1, 101):
            self.node.seed("fn.agents", "slot-%03d" % number, "body")
        path = "/g?name=fn.agents&start=61&end=100"
        status, _, before = self.request("GET", path)
        self.assertEqual(status, 200)
        self.assertIn("Local article numbers 61–100", before)
        self.assertIn("slot-100", before)
        self.assertNotIn("slot-060", before)

        self.node.seed("fn.agents", "arrived-after-request", "body")
        status, _, after = self.request("GET", path)
        self.assertEqual(status, 200)
        self.assertIn("Local article numbers 61–100", after)
        self.assertNotIn("arrived-after-request", after)
        self.assertIn("group currently spans 1–101", after)
        self.assertIn("start=101&amp;end=140", after)
        self.assertEqual(self.node.seen.count("OVER 61-100"), 2)

    def test_invalid_window_is_refused_before_any_nntp_command(self):
        invalid = (
            "start=-1&end=20",
            "start=1&end=10000000000",
            "start=1&end=41",
            "start=20&end=19",
            "start=1",
            "start=1&start=2&end=3",
        )
        for query in invalid:
            with self.subTest(query=query):
                status, _, page = self.request(
                    "GET", "/g?name=fn.agents&" + query)
                self.assertEqual(status, 400)
                self.assertIn("window", page)
        self.assertEqual(self.node.seen, [])

    def test_historical_server_report_is_bound_to_article_and_never_inferred(self):
        verified = "<reported@example.invalid>"
        legacy = "<legacy@example.invalid>"
        unsupported = "<unsupported@example.invalid>"
        malformed = "<malformed@example.invalid>"
        unverified = "<unverified@example.invalid>"
        absent = "<absent@example.invalid>"
        for msgid, subject in ((verified, "verified"), (legacy, "legacy"),
                               (unsupported, "unsupported"), (malformed, "malformed"),
                               (unverified, "unverified"), (absent, "absent")):
            self.node.inject("fn.agents", ["Newsgroups: fn.agents", "Subject: " + subject,
                                            "Message-ID: " + msgid,
                                            "FN-Statement: present", ""])
        self.node.verdicts.update({
            verified: "verified " + "ab" * 32 + " keyring 7",
            legacy: "verified legacy keyring 6",
            unsupported: "future-verdict opaque",
            malformed: "verified " + "ab" * 31 + "zz keyring 7",
            unverified: "unverified signature keyring 9",
        })
        status, _, page = self.request("GET", "/a?group=fn.agents&number=1")
        self.assertEqual(status, 200)
        self.assertIn("Server report of historical verification verdict: verified by principal " +
                      "ab" * 32 + " under keyring generation 7", page)
        self.assertIn("not an independent cryptographic check or current authorization", page)
        self.assertIn("HDR :fn-verified 1", self.node.seen)

        status, _, legacy_page = self.request("GET", "/a?group=fn.agents&number=2")
        self.assertEqual(status, 200)
        self.assertIn("verified (legacy recorded detail) under keyring generation 6", legacy_page)
        for number in (3, 4):
            status, _, unavailable = self.request(
                "GET", "/a?group=fn.agents&number=%d" % number)
            self.assertEqual(status, 200)
            self.assertIn("Server report of historical verification verdict: unavailable.",
                          unavailable)

        status, _, rejected = self.request("GET", "/a?group=fn.agents&number=5")
        self.assertEqual(status, 200)
        self.assertIn("Server report of historical verification verdict: "
                      "unverified: signature, keyring generation 9", rejected)

        # Header presence alone never upgrades an absent server record.
        status, _, absent = self.request("GET", "/a?group=fn.agents&number=6")
        self.assertEqual(status, 200)
        self.assertIn("Server report of historical verification verdict: absent: no-field", absent)

    def test_thread_order_follows_the_last_present_reference_and_survives_cycles(self):
        row = lambda n, mid, refs="": {"number": n, "message_id": mid, "references": refs,
                                       "subject": "", "from": "", "date": ""}
        rows = [row(1, "<a>"), row(2, "<b>"), row(3, "<c>", "<a>"),
                row(4, "<d>", "<a> <c>"), row(5, "<e>", "<gone> <b>"),
                row(6, "<f>", "<outside>"), row(7, "<x>", "<y>"), row(8, "<y>", "<x>")]
        order = [(r["number"], depth, outside) for r, depth, outside in fn_web.thread_rows(rows)]
        self.assertEqual(order, [(1, 0, False), (3, 1, False), (4, 2, False),
                                 (2, 0, False), (5, 1, False), (6, 0, True),
                                 (7, 0, True), (8, 0, True)])

    def test_reply_subject_and_references_keep_first_and_last_three(self):
        self.assertEqual(fn_web.reply_subject("hello"), "Re: hello")
        self.assertEqual(fn_web.reply_subject("RE: hello"), "RE: hello")
        ids = ["<%03d-%s@example.invalid>" % (n, "x" * 30) for n in range(40)]
        refs = fn_web.reply_references(" ".join(ids[:-1]), ids[-1]).split()
        self.assertLessEqual(len(" ".join(refs)), fn_web.MAX_REFERENCES)
        self.assertEqual(refs[0], ids[0])
        self.assertEqual(refs[-3:], ids[-3:])
        self.assertEqual(fn_web.reply_references("", "<p@x>"), "<p@x>")

    def test_unread_is_exact_with_the_nodes_list_counts(self):
        with tempfile.TemporaryDirectory() as temporary:
            marks = fn_web.ReadMarks(Path(temporary) / "m.json", "127.0.0.1:1119", "ember")
            marks.mark("fn.agents", 3, "<three@x>")
            marks.mark("fn.agents", 5, "<five@x>")
            # No count (a node without LIST COUNTS): the span, an upper bound.
            self.assertEqual(marks.unread({"group": "fn.agents", "first": 1, "last": 10,
                                           "count": None}), (8, False))
            # The count fills the span: every number holds an article.
            self.assertEqual(marks.unread({"group": "fn.agents", "first": 1, "last": 10,
                                           "count": 10}), (8, True))
            # Gaps: the node's LISTGROUP numbers decide; 5 was removed.
            self.assertEqual(marks.unread({"group": "fn.agents", "first": 1, "last": 10,
                                           "count": 4, "numbers": [1, 3, 7, 10]}), (3, True))
            self.assertEqual(marks.unread({"group": "fn.empty", "first": 1, "last": 0,
                                           "count": 0}), (0, True))

    def test_read_marks_are_local_per_principal_and_refuse_a_foreign_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "marks" / "m.json"
            marks = fn_web.ReadMarks(path, "127.0.0.1:1119", "ember")
            self.assertEqual(marks.unread_upper("fn.agents", 1, 10), 10)
            marks.mark("fn.agents", 1, "<one@x>")
            marks.mark("fn.agents", 3, "<three@x>")
            self.assertEqual(marks.unread_upper("fn.agents", 1, 10), 8)
            self.assertEqual(json.loads(path.read_text())["groups"]["fn.agents"]["through"], 1)
            self.assertEqual(oct(path.stat().st_mode & 0o777), "0o600")
            again = fn_web.ReadMarks(path, "127.0.0.1:1119", "ember")
            self.assertTrue(again.is_read("fn.agents", 3))
            self.assertFalse(again.is_read("fn.agents", 2))
            self.assertEqual(again.last("fn.agents"), {"number": 3, "message_id": "<three@x>"})
            other = fn_web.ReadMarks(path, "127.0.0.1:1119", "yue")
            self.assertIn("another node or principal", other.error)
            other.mark("fn.agents", 9, "<nine@x>")
            self.assertEqual(json.loads(path.read_text())["user"], "ember")

    def test_verdict_badge_kind_never_invents_a_verdict(self):
        self.assertEqual(fn_web.verdict_kind(None), "unavailable")
        self.assertEqual(fn_web.verdict_kind(fn_web.parse_verdict_hdr(
            "4 verified " + "ab" * 32 + " keyring 2", 4)), "verified")
        self.assertEqual(fn_web.verdict_kind(fn_web.parse_verdict_hdr(
            "4 unverified signature keyring 2", 4)), "unverified")
        self.assertEqual(fn_web.verdict_kind(fn_web.parse_verdict_hdr(
            "4 absent no-record", 4)), "absent")

    def test_verdict_parser_rejects_malformed_and_unbounded_values(self):
        self.assertIsNone(fn_web.parse_verdict_hdr("4 verified " + "a" * 100000, 4))
        self.assertIsNone(fn_web.parse_verdict_hdr("4 unverified signature", 4))
        self.assertIsNone(fn_web.parse_verdict_hdr("1 verified " + "ab" * 32 +
                                                   " keyring 1", 4))

    def test_article_header_message_id_cannot_redirect_verdict_lookup(self):
        actual = "<server-slot@example.invalid>"
        header_claim = "<different-header-id@example.invalid>"
        number = self.node.inject("fn.agents", ["Newsgroups: fn.agents",
                                                  "Subject: slot identity",
                                                  "Message-ID: " + actual,
                                                  "FN-Statement: present", ""])
        self.node.articles[actual] = ["Newsgroups: fn.agents", "Subject: slot identity",
                                      "Message-ID: " + header_claim,
                                      "FN-Statement: present", ""]
        self.node.verdicts[actual] = "unverified signature keyring 3"
        self.node.verdicts[header_claim] = "verified " + "cd" * 32 + " keyring 99"

        status, _, page = self.request("GET", "/a?group=fn.agents&number=%d" % number)
        self.assertEqual(status, 200)
        self.assertIn("unverified: signature, keyring generation 3", page)
        self.assertNotIn("keyring generation 99", page)
        self.assertIn("HDR :fn-verified %d" % number, self.node.seen)

    def test_composer_posts_via_nntp_and_keeps_three_outcomes(self):
        accepted = self.post()
        self.assertEqual(accepted[0], 200)
        self.assertIn("accepted", accepted[2])
        self.assertEqual(len(self.node.articles), 1)
        stored = next(iter(self.node.articles.values()))
        self.assertIn("A real post", stored)
        self.assertNotIn("Path:", stored)

        self.node.refuse_post = True
        refused = self.post()
        self.assertEqual(refused[0], 200)
        self.assertIn("<span class='badge refused'>refused</span>", refused[2])

        self.node.refuse_post = False
        self.node.uncertain_post = True
        uncertain = self.post()
        self.assertEqual(uncertain[0], 200)
        self.assertIn("<span class='badge uncertain'>uncertain</span>", uncertain[2])
        self.assertIn("do not repost", uncertain[2])
        self.assertEqual(len(self.node.articles), 1)

    def test_form_origin_and_size_are_checked_before_nntp_post(self):
        denied = self.post(origin=False)
        self.assertEqual(denied[0], 403)
        oversized = self.post(body={"body": "x" * 25000})
        self.assertEqual(oversized[0], 400)
        wrong_group = self.post(body={"group": "fn.humans"})
        self.assertEqual(wrong_group[0], 400)
        self.assertEqual(self.node.articles, {})

    def test_post_connection_loss_keeps_settlement_identifier(self):
        self.node.drop_before_greeting = True
        status, _, page = self.post()
        self.assertEqual(status, 200)
        self.assertIn("<span class='badge uncertain'>uncertain</span>", page)
        self.assertIn("Check whether the node serves this Message-ID", page)
        self.assertIn("&lt;fn-client.", page)

    def test_double_submit_and_refresh_keep_one_exact_article(self):
        token = self.form_id()
        def send(body):
            return self.request("POST", "/post", {
                "submission_id": token, "body": body})
        with ThreadPoolExecutor(max_workers=2) as pool:
            first, second = list(pool.map(send, ("first source", "other source")))
        self.assertEqual(first[0], 303)
        self.assertEqual(second[0], 303)
        self.assertEqual(first[1]["Location"], second[1]["Location"])
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.assertEqual(len(self.node.articles), 1)
        page1 = self.request("GET", first[1]["Location"])[2]
        page2 = self.request("GET", first[1]["Location"])[2]
        self.assertEqual(page1, page2)
        old = next(iter(self.node.articles.values()))
        self.assertIn("first source" if "first source" in old else "other source", old)
        self.assertEqual(self.request("POST", "/post", {
            "submission_id": token, "body": "third source"})[0], 303)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.assertEqual(next(iter(self.node.articles.values())), old)

    def test_uncertain_settlement_is_read_only_and_unknown_token_never_posts(self):
        token = self.form_id()
        self.node.uncertain_post = True
        status, headers, _ = self.request("POST", "/post", {
            "submission_id": token})
        self.assertEqual(status, 303)
        result = self.request("GET", headers["Location"])[2]
        self.assertIn("badge uncertain", result)
        self.assertIn("Message-ID:", result)
        status, _, settled = self.request("GET", "/settle?id=" + token)
        self.assertEqual(status, 200)
        self.assertIn("did not serve this Message-ID in this lookup", settled)
        self.assertIn("original POST outcome has not changed", settled)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.assertEqual(self.request("POST", "/post", {
            "submission_id": token})[0], 303)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.assertEqual(self.request("POST", "/post", {
            "submission_id": "forgotten"})[0], 410)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.server.submissions = fn_web.SubmissionBook(self.server.backend)
        self.assertEqual(self.request("POST", "/post", {
            "submission_id": token})[0], 410)
        self.assertEqual(self.node.seen.count("POST"), 1)

    def test_bounded_form_memory_evicts_without_reposting(self):
        first = self.form_id()
        for _ in range(fn_web.MAX_SUBMISSIONS):
            self.server.submissions.new("fn.agents")
        self.assertEqual(len(self.server.submissions.entries), fn_web.MAX_SUBMISSIONS)
        self.assertEqual(self.request("POST", "/post", {
            "submission_id": first})[0], 410)
        self.assertNotIn("POST", self.node.seen)

    def test_durable_outbox_restart_duplicate_and_single_instance(self):
        self.enable_outbox()
        token = self.form_id()
        with self.assertRaisesRegex(fn_web.OutboxError, "another client"):
            fn_web.DurableSubmissionBook(self.server.backend, self.outbox_path)
        sent = self.request("POST", "/post", {"submission_id": token})
        self.assertEqual(sent[0], 303)
        record = self.outbox_path / (token + ".json")
        saved = json.loads(record.read_text())
        self.assertEqual(saved["result"]["word"], "accepted")
        self.assertEqual(saved["target"]["port"], self.node.port)
        self.assertEqual(record.stat().st_mode & 0o777, 0o600)
        self.assertEqual(self.outbox_path.stat().st_mode & 0o777, 0o700)
        self.assertIn("A real post", saved["lines"])
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.restart_outbox()
        self.assertIn(html.escape(saved["message_id"]),
                      self.request("GET", "/outbox")[2])
        self.assertIn("badge accepted", self.request("GET", sent[1]["Location"])[2])
        duplicate = self.request("POST", "/post", {"submission_id": token,
                                                      "body": "different source"})
        self.assertEqual(duplicate[0], 303)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.assertEqual(json.loads(record.read_text())["lines"], saved["lines"])

        other_args = SimpleNamespace(host="127.0.0.1", port=self.node.port + 1,
                                     timeout=5.0, plain=True, cafile=None)
        self.server.shutdown()
        self.server.server_close()
        self.thread.join(5)
        with self.assertRaisesRegex(fn_web.OutboxError, "another version or target"):
            fn_web.DurableSubmissionBook(
                fn_web.Backend(other_args, "", ""), self.outbox_path)
        self.server = fn_web.WebServer(0, self.server.backend, self.outbox_path)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()

    def test_durable_refusal_remains_refusal_after_restart(self):
        self.enable_outbox()
        self.node.refuse_post = True
        token = self.form_id()
        sent = self.request("POST", "/post", {"submission_id": token})
        self.assertEqual(sent[0], 303)
        self.restart_outbox()
        page = self.request("GET", "/result?id=" + token)[2]
        self.assertIn("badge refused", page)
        self.assertEqual(self.request("POST", "/post", {"submission_id": token})[0], 303)
        self.assertEqual(self.node.seen.count("POST"), 1)

    def test_durable_inflight_restart_and_lost_reply_never_repost(self):
        self.enable_outbox()
        token = self.form_id()
        entry = self.server.submissions.entries[token]
        lines, msgid = self.server.backend.prepare("fn.agents", "hello",
            "human <h@local.invalid>", "", "in-flight source")
        entry["lines"], entry["message_id"] = tuple(lines), msgid
        self.server.submissions._write(token, entry, None, None)
        self.restart_outbox()
        self.assertIn("badge uncertain", self.request("GET", "/result?id=" + token)[2])
        self.assertEqual(self.request("POST", "/post", {"submission_id": token})[0], 303)
        self.assertNotIn("POST", self.node.seen)

        lost = self.form_id()
        self.node.drop_after_article = True
        sent = self.request("POST", "/post", {"submission_id": lost})
        self.assertEqual(sent[0], 303)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.restart_outbox()
        self.assertIn("badge uncertain", self.request("GET", sent[1]["Location"])[2])
        self.assertEqual(self.request("POST", "/post", {"submission_id": lost})[0], 303)
        self.assertEqual(self.node.seen.count("POST"), 1)
        saved = json.loads((self.outbox_path / (lost + ".json")).read_text())
        self.node.drop_after_article = False
        self.node.inject("fn.agents", saved["lines"])
        observed = self.request("GET", "/settle?id=" + lost)[2]
        self.assertIn("now serves this Message-ID", observed)
        self.assertIn("badge uncertain", observed)
        self.restart_outbox()
        again = self.request("GET", "/result?id=" + lost)[2]
        self.assertIn("now serves this Message-ID", again)
        self.assertIn("badge uncertain", again)
        self.assertEqual(self.node.seen.count("POST"), 1)

    def test_durable_restart_discards_only_incomplete_temp_write(self):
        self.enable_outbox()
        first = self.form_id()
        self.assertEqual(self.request("POST", "/post", {"submission_id": first})[0], 303)
        temp = self.outbox_path / ".record-abcdefgh"
        temp.write_text("half a JSON record")
        temp.chmod(0o600)
        self.restart_outbox()
        self.assertFalse(temp.exists())
        self.assertIn("badge accepted", self.request("GET", "/result?id=" + first)[2])
        self.assertEqual(self.node.seen.count("POST"), 1)

    def test_durable_draft_survives_restart_and_post_freezes_edited_source(self):
        self.enable_outbox()
        token = self.form_id()
        saved = self.request("POST", "/post", {"submission_id": token,
            "action": "save", "subject": "", "body": "rough <draft>"})
        self.assertEqual(saved[0], 303)
        self.assertEqual(saved[1]["Location"], "/draft?id=" + token)
        self.assertNotIn("POST", self.node.seen)
        record = self.outbox_path / (token + ".json")
        self.assertIsNone(json.loads(record.read_text())["lines"])
        self.restart_outbox()
        listing = self.request("GET", "/outbox")[2]
        self.assertIn("Draft: (untitled)", listing)
        restored = self.request("GET", "/draft?id=" + token)[2]
        self.assertIn("rough &lt;draft&gt;", restored)
        self.assertNotIn("POST", self.node.seen)
        edited = self.request("POST", "/post", {"submission_id": token,
            "action": "save", "subject": "Ready", "body": "edited exact source"})
        self.assertEqual(edited[0], 303)
        self.restart_outbox()
        self.assertIn("edited exact source", self.request("GET", edited[1]["Location"])[2])
        sent = self.request("POST", "/post", {"submission_id": token,
            "action": "post", "subject": "Ready", "body": "edited exact source"})
        self.assertEqual(sent[0], 303)
        self.assertEqual(self.node.seen.count("POST"), 1)
        source = next(iter(self.node.articles.values()))
        self.assertIn("edited exact source", source)
        self.assertNotIn("rough <draft>", source)
        self.assertEqual(self.request("GET", "/draft?id=" + token)[0], 410)
        self.restart_outbox()
        self.assertIn("badge accepted", self.request("GET", sent[1]["Location"])[2])
        self.assertEqual(self.request("POST", "/post", {"submission_id": token,
                                                       "body": "another"})[0], 303)
        self.assertEqual(self.node.seen.count("POST"), 1)

    def test_durable_draft_write_failure_fences_before_network(self):
        self.enable_outbox()
        token = self.form_id()
        with mock.patch.object(fn_web.os, "fsync", side_effect=OSError("draft EIO")):
            failed = self.request("POST", "/post", {"submission_id": token,
                "action": "save", "body": "local draft"})
        self.assertEqual(failed[0], 503)
        self.assertNotIn("POST", self.node.seen)
        self.assertIn("latest local save is uncertain",
                      self.request("GET", "/draft?id=" + token)[2])
        self.assertEqual(self.request("POST", "/post", {"submission_id": token,
                                                       "body": "attempt"})[0], 503)
        self.assertNotIn("POST", self.node.seen)

    def test_saved_draft_counts_toward_bound_without_eviction(self):
        self.enable_outbox()
        with mock.patch.object(fn_web, "MAX_SUBMISSIONS", 1):
            token = self.form_id()
            self.assertEqual(self.request("POST", "/post", {
                "submission_id": token, "action": "save", "body": "keep me"})[0], 303)
            self.restart_outbox()
            self.assertEqual(self.request("GET", "/compose?group=fn.agents")[0], 507)
            self.assertIn("keep me", self.request("GET", "/draft?id=" + token)[2])
            self.assertEqual(len(list(self.outbox_path.glob("*.json"))), 1)
        self.assertNotIn("POST", self.node.seen)

    def test_outbox_parent_barrier_failure_prevents_startup_and_post(self):
        with tempfile.TemporaryDirectory() as parent:
            path = Path(parent) / "new-outbox"
            with mock.patch.object(fn_web.os, "fsync", side_effect=OSError("parent EIO")):
                with self.assertRaisesRegex(OSError, "parent EIO"):
                    fn_web.WebServer(0, self.server.backend, path)
            self.assertNotIn("POST", self.node.seen)
            with fn_web.WebServer(0, self.server.backend, path) as recovered:
                self.assertIsInstance(recovered.submissions,
                                      fn_web.DurableSubmissionBook)
            self.assertNotIn("POST", self.node.seen)

    def test_durable_concurrent_submit_and_full_spool_preserve_records(self):
        self.enable_outbox()
        token = self.form_id()
        with ThreadPoolExecutor(max_workers=2) as pool:
            first, second = list(pool.map(lambda body: self.request(
                "POST", "/post", {"submission_id": token, "body": body}),
                ("first", "second")))
        self.assertEqual((first[0], second[0]), (303, 303))
        self.assertEqual(self.node.seen.count("POST"), 1)
        for index in range(fn_web.MAX_SUBMISSIONS - 1):
            token2 = self.server.submissions.new("fn.agents")
            entry = self.server.submissions.entries[token2]
            entry["lines"] = ("Message-ID: <local-%d@example.invalid>" % index, "")
            entry["message_id"] = "<local-%d@example.invalid>" % index
            entry["result"] = fn_web.fn_client.Result(
                fn_web.fn_client.UNCERTAIN, "local fixture", {}, "")
            self.server.submissions._write(token2, entry,
                {"word": "uncertain", "detail": "local fixture"}, None)
        self.assertEqual(self.request("GET", "/compose?group=fn.agents")[0], 507)
        self.assertEqual(len(list(self.outbox_path.glob("*.json"))), fn_web.MAX_SUBMISSIONS)
        self.assertEqual(self.node.seen.count("POST"), 1)

    def test_durable_fsync_failures_before_and_after_network(self):
        self.enable_outbox()
        token = self.form_id()
        actual_fsync = os.fsync
        with mock.patch.object(fn_web.os, "fsync", side_effect=OSError("intent EIO")):
            denied = self.request("POST", "/post", {"submission_id": token})
        self.assertEqual(denied[0], 503)
        self.assertNotIn("POST", self.node.seen)
        self.assertEqual(self.request("GET", "/result?id=" + token)[0], 503)
        self.assertEqual(self.request("GET", "/compose?group=fn.agents")[0], 503)

        self.restart_outbox()
        token = self.form_id()
        calls = [0]
        def fail_result_barrier(fd):
            calls[0] += 1
            if calls[0] == 4:
                raise OSError("result directory EIO")
            return actual_fsync(fd)
        with mock.patch.object(fn_web.os, "fsync", side_effect=fail_result_barrier):
            sent = self.request("POST", "/post", {"submission_id": token})
        self.assertEqual(sent[0], 303)
        page = self.request("GET", sent[1]["Location"])[2]
        self.assertIn("badge accepted", page)
        self.assertIn("outbox persistence failed", page)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.assertEqual(self.request("GET", "/compose?group=fn.agents")[0], 503)


if __name__ == "__main__":
    unittest.main()

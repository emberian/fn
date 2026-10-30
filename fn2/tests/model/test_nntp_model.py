"""Independent fixtures, properties, and deliberately wrong wire responders."""
import os
# Keep property caches out of the shared working tree.
os.environ.setdefault("HYPOTHESIS_STORAGE_DIRECTORY", "/tmp/h2a-hypothesis")
import base64
from pathlib import Path
import re
import unittest

from hypothesis import given, settings, strategies as st
from hypothesis.stateful import Bundle, RuleBasedStateMachine, invariant, rule

from .framing import (FramingError, command_line, decode_block, encode_block,
                      lines, split_commands, stuff, unstuff)
from .nntp_model import (Expect, KEYWORDS, NntpModel, SPECS, body_lines,
                         headers, packed, scrub, wildmat)

FIXTURES = Path(__file__).parent / "fixtures"


def article(ident="<one@example.test>", group="test", body=b"one\r\n.two\r\n", extra=b""):
    return (f"From: Example <a@example.test>\r\nNewsgroups: {group}\r\n"
            f"Subject: test\r\nDate: Tue, 27 Oct 2026 12:00:00 +0000\r\n"
            f"Message-ID: {ident}\r\n".encode() + extra + b"\r\n" + body)


def model(groups=None, articles=None, accounts=None, **policy):
    return NntpModel(groups or {"test": {}}, articles or [], accounts or {}, policy)


def connect(m, tls=False):
    return m.connect(tls=tls, implicit_tls=False)


def accept(expect, status, body=None):
    status = status.encode() + b"\r\n" if isinstance(status, str) else status
    verdict = expect.check(status, body)
    if not verdict.ok:
        raise AssertionError(f"{verdict.rule} {verdict.spec}: {verdict.detail}; {status!r}")
    expect.update(status, body)
    return verdict


def send(c, command, status, body=None):
    return accept(c.send(command.encode() + b"\r\n"), status,
                  encode_block(body) if body is not None else None)


def selected(m=None, *, empty=False):
    m = m or model(articles=[] if empty else [("<one@example.test>", article(), ["test"])])
    c = connect(m)
    count, lo, hi = c._summary("test")
    send(c, "GROUP test", f"211 {count} {lo} {hi} test")
    return c


class FramingTests(unittest.TestCase):
    @settings(max_examples=200, deadline=None, database=None)
    @given(st.binary())
    def test_dot_stuff_roundtrip_arbitrary_binary(self, data):
        self.assertEqual(unstuff(stuff(data)), data)

    @settings(max_examples=200, deadline=None, database=None)
    @given(st.lists(st.binary().filter(lambda b: not any(c in b for c in (b"\0", b"\r", b"\n"))), max_size=20))
    def test_block_roundtrip(self, rows):
        data = packed(rows)
        wire = encode_block(data)
        self.assertTrue(wire.endswith(b".\r\n"))
        self.assertEqual(decode_block(wire), data)

    def test_terminator_and_dot_stuffing(self):
        self.assertEqual(encode_block(b""), b".\r\n")
        self.assertEqual(encode_block(b".\r\n..x\r\n"), b"..\r\n...x\r\n.\r\n")
        for bad in (b"", b"hello\r\n", b".\r\nx\r\n.\r\n", b".x\r\n.\r\n", b"x\n.\r\n"):
            with self.subTest(bad=bad), self.assertRaises(FramingError):
                decode_block(bad)

    def test_512_octet_limit_510_511_512_513(self):
        for length in (510, 511, 512, 513):
            line = b"X" * (length - 2) + b"\r\n"
            if length <= 512:
                self.assertEqual(command_line(line), line[:-2])
                accept(connect(model()).send(line), "500 unrecognized")
            else:
                with self.assertRaises(FramingError):
                    command_line(line)
                accept(connect(model()).send(line), "501 line too long")

    def test_bare_cr_bare_lf_nul_and_multiple_commands(self):
        for line in (b"HELP\n", b"HELP\r", b"HE\rLP\r\n", b"HE\nLP\r\n",
                     b"HELP\0\r\n", b"HELP\r\nQUIT\r\n", b"\r\n"):
            with self.subTest(line=line):
                with self.assertRaises(FramingError):
                    command_line(line)
                accept(connect(model()).send(line), "501 invalid line")

    @settings(max_examples=200, deadline=None, database=None)
    @given(st.binary(), st.integers(min_value=0, max_value=500))
    def test_fragmentation(self, data, cut):
        cut = min(len(data), cut)
        first, tail = split_commands(data[:cut])
        rest, remaining = split_commands(tail + data[cut:])
        whole, whole_tail = split_commands(data)
        self.assertEqual((first + rest, remaining), (whole, whole_tail))


class ReaderTests(unittest.TestCase):
    def test_help_and_optional_capabilities_keyword(self):
        c = connect(model())
        from .nntp_model import HELP
        send(c, "HELP", "100 help", HELP)
        send(c, "CAPABILITIES 2", "501 invalid keyword")
        e = c.send(b"CAPABILITIES VERSION\r\n")
        self.assertEqual(e._get().codes, {101})

    def test_leading_zeroes_and_message_id_command_grammar(self):
        c = selected()
        send(c, "STAT 0000000000000001", "223 0001 <one@example.test>")
        send(c, "LISTGROUP test 0001-0009", "211 01 01 01 test", b"0001\r\n")
        send(c, "ARTICLE <syntactic-but-not-a-stored-id>", "430 absent")
        send(c, "ARTICLE 00000000000000001", "501 too many digits")

    def test_selection_snapshot_does_not_change_during_check_update(self):
        c = connect(model())
        e = c.send(b"LISTGROUP test\r\n")
        self.assertTrue(e.check(b"211 0 1 0 test\r\n", b".\r\n").ok)
        c.model.add_article("<one@example.test>", article(), ["test"])
        accept(e, "211 0 1 0 test", b".\r\n")
        send(c, "STAT <one@example.test>", "430 absent")
        send(c, "GROUP test", "211 1 1 1 test")

    def test_all_keywords_have_rules_and_spec_references(self):
        c = connect(model())
        for keyword in KEYWORDS:
            self.assertTrue(hasattr(c, "_cmd_" + keyword.lower().replace("-", "_")))
            self.assertIn(keyword, SPECS)
        self.assertFalse(c.send(b"XYZZY\r\n").check(b"501 syntax\r\n", None).ok)

    @settings(max_examples=200, deadline=None, database=None)
    @given(st.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1, max_size=40)
           .filter(lambda s: s.upper() not in KEYWORDS))
    def test_non_keyword_is_500(self, word):
        accept(connect(model()).send(word.encode() + b"\r\n"), "500 unknown")

    def test_group_resets_cursor_failed_selection_preserves_it(self):
        m = model(articles=[("<one@example.test>", article(), ["test"]),
                            ("<two@example.test>", article("<two@example.test>"), ["test"])])
        c = selected(m)
        send(c, "STAT 2", "223 2 <two@example.test>")
        send(c, "GROUP missing", "411 missing")
        self.assertEqual(c.current_article_number, 2)
        send(c, "GROUP test", "211 2 1 2 test")
        self.assertEqual(c.current_article_number, 1)
        send(c, "ARTICLE <two@example.test>", "220 2 <two@example.test>",
             b"Xref: .invalid test:2\r\n" + article("<two@example.test>"))
        self.assertEqual(c.current_article_number, 1)
        send(c, "STAT <two@example.test>", "223 0 <two@example.test>")
        self.assertEqual(c.current_article_number, 1)

    def test_holes_watermark_empty_group_and_no_reuse(self):
        m = model()
        for i in range(1, 35):
            m.add_article(f"<{i}@t>", article(f"<{i}@t>"), ["test"])
        for i in range(2, 34):
            m.withdraw(f"<{i}@t>")
        c = connect(m)
        send(c, "GROUP test", "211 2 1 34 test")
        send(c, "NEXT", "223 34 <34@t>")
        send(c, "NEXT", "421 no next")
        send(c, "LAST", "223 1 <1@t>")
        send(c, "LAST", "422 no previous")
        m.withdraw("<1@t>"); m.withdraw("<34@t>")
        send(c, "GROUP test", "211 0 35 34 test")
        for cmd in ("NEXT", "LAST", "STAT", "OVER", "HDR subject"):
            send(c, cmd, "420 no current")
        m.add_article("<35@t>", article("<35@t>"), ["test"])
        send(c, "LISTGROUP test", "211 1 35 35 test", b"35\r\n")
        self.assertEqual(m.issued["test"], list(range(1, 36)))

    def test_listgroup_range_selection_is_first_of_group(self):
        m = model(articles=[(f"<{i}@t>", article(f"<{i}@t>"), ["test"]) for i in range(1, 4)])
        c = connect(m)
        send(c, "LISTGROUP test 2-", "211 3 1 3 test", b"2\r\n3\r\n")
        self.assertEqual(c.current_article_number, 1)
        send(c, "LISTGROUP test 9-2", "211 3 1 3 test", b"")
        self.assertEqual(c.current_article_number, 1)

    def test_empty_range_codes_and_error_precedence(self):
        c = connect(model())
        for cmd in ("NEXT", "LAST", "ARTICLE", "OVER", "XOVER", "HDR subject", "LISTGROUP"):
            send(c, cmd, "412 no group")
        send(c, "ARTICLE <none@t>", "430 absent")
        send(c, "GROUP test", "211 0 1 0 test")
        for cmd in ("ARTICLE 1", "OVER 1-9", "HDR subject 1-9"):
            send(c, cmd, "423 empty")
        for cmd in ("XOVER 1-9", "XHDR subject 1-9", "OVER", "ARTICLE"):
            send(c, cmd, "420 empty")
        send(c, "XOVER <none@t>", "501 syntax")
        send(c, "XPAT subject 1-9 *", "221 matches", b"")

    def test_withdrawal_pins_and_text(self):
        c = selected()
        c.model.withdraw("<one@example.test>")
        send(c, "STAT <one@example.test>", "223 1 <one@example.test>")
        send(c, "GROUP test", "211 0 2 1 test")
        e = c.send(b"ARTICLE <one@example.test>\r\n")
        self.assertFalse(e.check(b"430 absent\r\n", None).ok)
        accept(e, "430 withdrawn")
        send(c, "ARTICLE 1", "423 withdrawn")
        send(c, "STAT <missing@t>", "430 absent")

    def test_older_reader_sees_new_article_only_after_group(self):
        c = selected()
        c.model.add_article("<two@t>", article("<two@t>"), ["test"])
        send(c, "ARTICLE <two@t>", "430 absent")
        send(c, "GROUP absent", "411 absent")
        send(c, "ARTICLE <two@t>", "430 absent")
        send(c, "GROUP test", "211 2 1 2 test")
        send(c, "STAT <two@t>", "223 2 <two@t>")

    def test_nov_fields_and_xref_are_independently_computed(self):
        ident = "<one@example.test>"
        raw = article(extra=b"References: <parent@t>\r\nX-Test: folded\r\n\tvalue\r\n")
        c = selected(model(articles=[(ident, raw, ["test"])], server="news.test"))
        expected = (b"1\ttest\tExample <a@example.test>\tTue, 27 Oct 2026 12:00:00 +0000\t"
                    b"<one@example.test>\t<parent@t>\t" + str(len(raw)).encode() +
                    b"\t2\tXref: news.test test:1\r\n")
        send(c, "OVER 1", "224 overview", expected)
        send(c, "XOVER", "224 overview", expected)
        send(c, f"OVER {ident}", "224 overview", expected.replace(b"1\t", b"0\t", 1))
        e = c.send(b"OVER 1\r\n")
        bad = expected.replace(b"\t2\tXref", b"\t3\tXref")
        self.assertFalse(e.check(b"224 overview\r\n", encode_block(bad)).ok)
        accept(e, "224 overview", encode_block(expected))
        send(c, "HDR x-test 1", "225 headers", b"1 folded value\r\n")
        send(c, "HDR Xref 1", "225 headers", b"1 news.test test:1\r\n")
        send(c, f"XHDR subject {ident}", "221 headers", ident.encode() + b" test\r\n")
        send(c, "XPAT Xref 1 news*", "221 headers", b"")
        send(c, "XPAT subject 1 t*", "221 headers", b"1 test\r\n")
        send(c, "HDR absent 1", "225 headers", b"1\r\n")
        send(c, "HDR :bytes 1", "225 headers", b"1 " + str(len(raw)).encode() + b"\r\n")
        send(c, "HDR :unknown 1", "503 unsupported")

    def test_article_head_body_exact_octets_and_framing(self):
        c = selected()
        raw = article()
        for cmd, code, data in (("ARTICLE", 220, b"Xref: .invalid test:1\r\n" + raw),
                                ("HEAD", 221, b"Xref: .invalid test:1\r\n" + raw.split(b"\r\n\r\n")[0] + b"\r\n"),
                                ("BODY", 222, b"one\r\n.two\r\n")):
            e = c.send(cmd.encode() + b"\r\n")
            status = f"{code} 1 <one@example.test>\r\n".encode()
            self.assertFalse(e.check(status, encode_block(data + b"bad\r\n")).ok)
            self.assertFalse(e.check(status, encode_block(data)[:-3]).ok)
            accept(e, status, encode_block(data))

    def test_scrub_and_first_header(self):
        self.assertEqual(scrub(b"a\r\n\t\0\rb\n"), b"a   b ")
        self.assertEqual(headers(b"Subject: one\r\n two\r\nSubject: other\r\n\r\n")["subject"], b"one\r\n two")
        self.assertEqual(body_lines(b"A: b\r\n\r\nx\0\r\n"), 0)

    def test_wildmat_rightmost_and_utf8(self):
        for text, expected in (("aaa", True), ("abb", False), ("ccb", True), ("xxx", False)):
            self.assertEqual(wildmat("a*,!*b,*c*", text), expected)
        self.assertTrue(wildmat("?", "é"))
        self.assertFalse(wildmat("T*", "test"))
        for pattern in ("", "!foo", "a,,b", "[ab]", "a\\*"):
            with self.assertRaises(ValueError):
                wildmat(pattern, "a")

    def test_lists_flags_descriptions_counts_and_filters(self):
        c = connect(model(groups={"test": {}, "closed": {"read_only": True, "watermark": 9},
                                  "moderated": {"moderated": True, "description": "Discuss"}},
                          subscriptions=["moderated", "test"], motd=[".welcome", "hello"]))
        send(c, "LIST ACTIVE *", "215 list", b"test 0 1 y\r\nclosed 9 10 n\r\nmoderated 0 1 m\r\n")
        send(c, "LIST COUNTS closed", "215 list", b"closed 0009 0010 0 n\r\n")
        send(c, "LIST NEWSGROUPS moderated", "215 list", b"moderated\tDiscuss\r\n")
        send(c, "LIST NEWSGROUPS test", "215 list", b"test (no description)\r\n")
        send(c, "LIST MOTD", "215 list", b".welcome\r\nhello\r\n")
        send(c, "LIST SUBSCRIPTIONS", "215 list", b"moderated\r\ntest\r\n")
        send(c, "LIST OVERVIEW.FMT", "215 list", packed(["Subject:", "From:", "Date:", "Message-ID:", "References:", "Bytes:", "Lines:", "Xref:full"]))
        send(c, "LIST HEADERS MSGID", "215 list", b":\r\n:bytes\r\n:lines\r\n")
        for cmd, code in (("LIST DISTRIB.PATS", 503), ("LIST DISTRIBUTIONS", 503), ("LIST unknown", 501), ("LIST MOTD extra", 501)):
            send(c, cmd, f"{code} unavailable")

    def test_access_hides_existence_and_xref(self):
        ident = "<one@example.test>"
        m = model(groups={"test": {}, "private": {}}, articles=[(ident, article(), ["test", "private"])],
                  accounts={"reader": {"password": "pw", "read": "test", "post": "private"}})
        c = connect(m)
        send(c, "GROUP private", "211 1 1 1 private")
        send(c, "AUTHINFO USER reader", "381 password")
        send(c, "AUTHINFO PASS pw", "281 accepted")
        self.assertIsNone(c.current_group)
        send(c, "GROUP private", "411 absent")
        send(c, "LIST", "215 list", b"test 1 1 n\r\n")
        send(c, "HEAD <one@example.test>", "221 0 <one@example.test>", b"Xref: .invalid test:1\r\n" + article().split(b"\r\n\r\n")[0] + b"\r\n")

    def test_clock_creation_and_acceptance_times(self):
        m = model(groups={"test": {"created_at": 946684800}}, clock="20261028120000",
                  articles=[("<one@example.test>", article(), ["test"])], stamps={"<one@example.test>": 946684800})
        c = connect(m)
        send(c, "DATE", "111 20261028120000")
        send(c, "LIST ACTIVE.TIMES", "215 list", b"test 946684800 unattributed\r\n")
        send(c, "NEWGROUPS 000101 000000 GMT", "231 groups", b"test 1 1 y\r\n")
        send(c, "NEWNEWS * 20000101 000000 GMT", "230 ids", b"<one@example.test>\r\n")
        send(c, "NEWNEWS * 20000101 000001", "230 ids", b"")
        send(c, "NEWGROUPS 20000230 000000", "501 syntax")
        m.policy["clock"] = None
        send(c, "DATE", "503 clock unavailable")
        c2 = connect(m)
        send(c2, "NEWNEWS * 000101 000000", "503 clock unavailable")

    def test_pipelined_commands_resolve_and_commit_in_order(self):
        c = connect(model())
        es = [c.send(x + b"\r\n") for x in (b"GROUP test", b"NEXT", b"QUIT", b"AUTHINFO USER somebody", b"HELP")]
        with self.assertRaises(RuntimeError):
            es[1].check(b"420 empty\r\n", None)
        accept(es[0], "211 0 1 0 test")
        accept(es[1], "420 empty")
        accept(es[2], "205 closing")
        for e in es[3:]:
            accept(e, b"")
            self.assertFalse(e.check(b"500 unexpected\r\n", None).ok)
        self.assertTrue(c.quit)

    def test_update_is_checked_idempotent_and_does_not_accept_another_choice(self):
        c = connect(model())
        e = c.send(b"QUIT\r\n")
        self.assertFalse(c.quit)
        with self.assertRaises(ValueError):
            e.update(b"200 wrong\r\n", None)
        self.assertFalse(c.quit)
        accept(e, "205 bye")
        e.update(b"205 bye\r\n", None)
        with self.assertRaises(ValueError):
            e.update(b"205 other\r\n", None)


class AuthenticationTests(unittest.TestCase):
    def test_sasl_check_is_pure_and_bad_final_is_rejected(self):
        c = connect(model(accounts={"alice": "pw"}), tls=True)
        token = base64.b64encode(b"\0alice\0pw")
        e = c.send(b"AUTHINFO SASL PLAIN " + token + b"\r\n")
        self.assertTrue(e.check(b"281 accepted\r\n", None).ok)
        self.assertIsNone(c.sasl_identity)
        self.assertIsNone(c.authenticated_as)
        accept(e, "281 accepted")
        self.assertEqual(c.authenticated_as, "alice")

    def test_required_and_posting_permission(self):
        c = connect(model(required=True, accounts={"a": {"password": "pw", "posting": False}}))
        accept(c.greeting(), "201 ready")
        send(c, "GROUP test", "480 authenticate")
        send(c, "POST", "480 authenticate")
        send(c, "AUTHINFO PASS pw", "482 sequence")
        send(c, "AUTHINFO USER a", "381 password")
        send(c, "AUTHINFO PASS pw", "281 accepted")
        send(c, "POST", "440 not permitted")
        send(c, "AUTHINFO USER a", "502 already authenticated")
        send(c, "STARTTLS", "502 already authenticated")

    def test_third_failure_481_then_400_and_quit(self):
        c = connect(model(accounts={"a": "good"}))
        for i in range(3):
            send(c, "AUTHINFO USER a", "381 password")
            e = c.send(b"AUTHINFO PASS wrong\r\n")
            status = b"481 failed\r\n" + (b"400 too many authentication failures; closing connection\r\n" if i == 2 else b"")
            if i == 2:
                self.assertFalse(e.check(b"481 failed\r\n", None).ok)
            accept(e, status)
            self.assertEqual(c.failed_auth_count, i + 1)
        accept(c.send(b"AUTHINFO USER a\r\n"), b"")
        self.assertTrue(c.quit)

    def test_starttls_handshake_resets_selection_preserves_mode_and_failures(self):
        c = selected(model(accounts={"a": "pw"}))
        send(c, "MODE READER", "200 ready")
        send(c, "AUTHINFO USER missing", "381 password")
        send(c, "AUTHINFO PASS bad", "481 failed")
        send(c, "STARTTLS", "382 negotiate")
        self.assertFalse(c.tls)
        accept(c.send(b"HELP\r\n"), b"")
        c.tls_established()
        self.assertTrue(c.tls)
        self.assertTrue(c.mode_reader_seen)
        self.assertEqual(c.failed_auth_count, 1)
        self.assertIsNone(c.current_group)
        send(c, "STARTTLS", "502 unavailable")
        send(c, "COMPRESS DEFLATE", "480 authenticate")
        send(c, "AUTHINFO USER a", "381 password")
        send(c, "AUTHINFO PASS pw", "281 accepted")
        send(c, "COMPRESS DEFLATE", "206 compression active")
        send(c, "STARTTLS", "502 unavailable")
        send(c, "COMPRESS DEFLATE", "502 unavailable")
        send(c, "AUTHINFO USER a", "502 unavailable")

    def test_compression_preserves_cursor_and_implicit_tls(self):
        m = model(accounts={"a": "pw"})
        c = m.connect(tls=False, implicit_tls=True)
        self.assertTrue(c.tls)
        send(c, "STARTTLS", "502 unavailable")
        send(c, "AUTHINFO USER a", "381 password")
        send(c, "AUTHINFO PASS pw", "281 accepted")
        send(c, "GROUP test", "211 0 1 0 test")
        send(c, "COMPRESS GZIP", "503 unsupported")
        send(c, "COMPRESS", "501 syntax")
        send(c, "COMPRESS DEFLATE", "206 active")
        self.assertEqual(c.current_group, "test")

    def test_compression_requires_authentication_even_when_reading_is_public(self):
        for required in (False, True):
            for tls in (False, True):
                with self.subTest(required=required, tls=tls):
                    c = connect(model(required=required), tls=tls)
                    for command in ("COMPRESS DEFLATE", "COMPRESS GZIP", "COMPRESS"):
                        e = c.send(command.encode() + b"\r\n")
                        self.assertFalse(e.check(b"206 active\r\n", None).ok)
                        accept(e, "480 authenticate")
                        self.assertFalse(c.compressed)
                    # Active-layer refusal takes precedence even without a login.
                    c.compressed = True
                    send(c, "COMPRESS DEFLATE", "502 unavailable")

    def test_sasl_states_cancellation_shapes_and_third_failure(self):
        c = connect(model(accounts={"alice": "pw"}), tls=True)
        for _ in range(2):
            send(c, "AUTHINFO SASL PLAIN", "383 =")
            send(c, "*", "481 cancelled")
        self.assertEqual(c.failed_auth_count, 0)
        send(c, "AUTHINFO SASL UNKNOWN", "503 unsupported")
        send(c, "AUTHINFO SASL PLAIN broken===", "504 base64")
        for i in range(3):
            send(c, "AUTHINFO SASL PLAIN", "383 =")
            e = c.send(base64.b64encode(b"\0alice\0wrong") + b"\r\n")
            accept(e, b"481 failed\r\n" + (b"400 closing\r\n" if i == 2 else b""))
        self.assertTrue(c.quit)
        c = connect(model(accounts={"alice": "pw"}), tls=True)
        token = base64.b64encode(b"n,,n=alice,r=nonce").decode()
        send(c, "AUTHINFO SASL SCRAM-SHA-256 " + token, "383 cj1ub25jZQ==")
        send(c, "Yz1iaXdzLHA9cHJvb2Y=", "283 dj1zaWduYXR1cmU=")
        self.assertEqual(c.authenticated_as, "alice")

    def test_xredeem_does_not_authenticate_or_refresh_credentials(self):
        m = model(protected_only=True)
        c = connect(m)
        code = "1" * 32
        send(c, f"XREDEEM {code} new", "483 TLS required")
        c = connect(m, tls=True)
        send(c, "XREDEEM PASS pw", "482 sequence")
        send(c, f"XREDEEM {code} new", "381 password")
        send(c, "XREDEEM PASS pw", "281 bound")
        self.assertIsNone(c.authenticated_as)
        send(c, "AUTHINFO USER new", "381 password")
        send(c, "AUTHINFO PASS pw", "481 failed")
        new = connect(m, tls=True)
        send(new, "AUTHINFO USER new", "381 password")
        send(new, "AUTHINFO PASS pw", "281 accepted")

    def test_capacity_and_trusted_addresses(self):
        m = model(connections=2, per_address=1, trusted=["10.0.0.0/8"])
        a = m.connect(tls=False, implicit_tls=False, address="10.0.0.1")
        b = m.connect(tls=False, implicit_tls=False, address="10.0.0.1")
        accept(a.greeting(), "201 ready")
        accept(b.greeting(), "201 ready")
        c = connect(m)
        accept(c.greeting(), "400 too many connections; try again later")
        accept(c.send(b"HELP\r\n"), b"")

    def test_capabilities_conditional_labels(self):
        c = connect(model())
        rows = ["VERSION 2", "READER", "OVER MSGID", "HDR", "XPAT", "NEWNEWS", "POST",
                "STARTTLS", "COMPRESS DEFLATE", "AUTHINFO USER SASL", "SASL SCRAM-SHA-256",
                "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn test"]
        send(c, "CAPABILITIES", "101 capabilities", packed(rows))
        send(c, "STARTTLS", "382 negotiate")
        c.tls_established()
        e = c.send(b"CAPABILITIES\r\n")
        self.assertFalse(e.check(b"101 capabilities\r\n", encode_block(packed(rows))).ok)
        rows.remove("STARTTLS")
        rows[rows.index("SASL SCRAM-SHA-256")] = "SASL SCRAM-SHA-256 PLAIN"
        accept(e, "101 capabilities", encode_block(packed(rows)))

    def test_compress_capability_before_after_authentication_and_activation(self):
        rows = ["VERSION 2", "READER", "OVER MSGID", "HDR", "XPAT", "NEWNEWS", "POST",
                "AUTHINFO USER SASL", "SASL SCRAM-SHA-256 PLAIN",
                "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT",
                "IMPLEMENTATION fn test"]
        c = connect(model(accounts={"a": "pw"}), tls=True)
        for advertised in (False, True):
            send(c, "CAPABILITIES", "101 capabilities",
                 packed(rows + (["COMPRESS DEFLATE"] if advertised else [])))
        send(c, "AUTHINFO USER a", "381 password")
        send(c, "AUTHINFO PASS pw", "281 accepted")
        rows.remove("AUTHINFO USER SASL")
        e = c.send(b"CAPABILITIES\r\n")
        self.assertFalse(e.check(b"101 capabilities\r\n", encode_block(packed(rows))).ok)
        accept(e, "101 capabilities", encode_block(packed(rows + ["COMPRESS DEFLATE"])))
        send(c, "COMPRESS DEFLATE", "206 active")
        e = c.send(b"CAPABILITIES\r\n")
        self.assertFalse(e.check(b"101 capabilities\r\n",
                                 encode_block(packed(rows + ["COMPRESS DEFLATE"]))).ok)
        accept(e, "101 capabilities", encode_block(packed(rows)))


class H2cRecordedReplyTests(unittest.TestCase):
    def test_reader_stream_is_unimplemented_mode_variant(self):
        # shard-1/repro-200-reader-whole-00000.json; specs/nntp.md:78-80,
        # 2416-2418 and RFC 3977 section 3.2.1 (local lines 552-555).
        c = connect(model())
        e = c.send(b"MODE STREAM\r\n")
        self.assertFalse(e.check(b"502 transit is not permitted\r\n", None).ok)
        accept(e, b"501 syntax error\r\n")

    def test_missing_required_post_field_accepts_syntax_reason(self):
        # Recorded POST refusal in shard-0/repro-4-node-whole-00036.json and the
        # eighteen POST rows: RFC free prose; spec860 requires these fields.
        c = connect(model())
        send(c, "POST", "340 send article")
        e = c.send_block(b"From: \r\nNewsgroups: \r\nSubject: x\r\n\r\n.\r\n")
        self.assertFalse(e.check(b"240 article received OK\r\n", None).ok)
        accept(e, b"441 posting failed; the article is not valid syntax\r\n")
        self.assertEqual(c.model.post_outcomes[-1][2], "refused")

    def test_recorded_peer_capabilities_with_unknown_exporter(self):
        # Exact reply bytes from shard-0/repro-5-peer-whole-00048.json.
        reply = (b"VERSION 2\r\nREADER\r\nPOST\r\nOVER MSGID\r\nHDR\r\nXPAT\r\nNEWNEWS\r\n"
                 b"LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT\r\n"
                 b"IMPLEMENTATION fn-nntp-lab\r\nIHAVE\r\nSTREAMING\r\nAUTHINFO USER SASL\r\n"
                 b"SASL SCRAM-SHA-256-PLUS SCRAM-SHA-256 PLAIN\r\nCOMPRESS DEFLATE\r\n"
                 b"XFN-DICT 845aa5e18680ef219a9b0f0d0b959cd8886d5eabc12236aae19f301aed9de75e\r\n.\r\n")
        c = connect(model(peer=True, tls_exporter=None), tls=True)
        e = c.send(b"CAPABILITIES\r\n")
        self.assertTrue(e.check(b"101 capability list follows\r\n", reply.replace(b"COMPRESS DEFLATE\r\n", b"")).ok)
        self.assertFalse(e.check(b"101 capability list follows\r\n", reply.replace(b"PLAIN", b"PLAIN DIGEST-MD5")).ok)
        accept(e, b"101 capability list follows\r\n", reply)
        c = connect(model(peer=True, tls_exporter=False), tls=True)
        self.assertFalse(c.send(b"CAPABILITIES\r\n").check(b"101 capability list follows\r\n", reply).ok)
        for policy in ({"tls_exporter": None, "tls_version": "TLSv1.2"},
                       {"tls_exporter": None, "sasl_mechanisms": ["SCRAM-SHA-256", "PLAIN"]}):
            c = connect(model(peer=True, **policy), tls=True)
            self.assertFalse(c.send(b"CAPABILITIES\r\n").check(b"101 capability list follows\r\n", reply).ok)

    def test_sasl_plus_uses_same_known_exporter_as_capabilities(self):
        c = connect(model(tls_exporter=True, tls_version="TLSv1.3"), tls=True)
        send(c, "AUTHINFO SASL SCRAM-SHA-256-PLUS", "383 =")
        c = connect(model(tls_exporter=False, tls_version="TLSv1.3"), tls=True)
        send(c, "AUTHINFO SASL SCRAM-SHA-256-PLUS", "503 not offered")
        c = connect(model(tls_exporter=None, tls_version="TLSv1.3"), tls=True)
        with self.assertRaisesRegex(RuntimeError, "observed exporter"):
            c.send(b"AUTHINFO SASL SCRAM-SHA-256-PLUS\r\n").check(b"383 =\r\n", None)

    def test_newgroups_creation_interval_required_optional_and_absent(self):
        groups = {"test": {}, "exact": {"created_at": 946684799}}
        policy = {"group_creation_window": (946684800, 946684810)}
        for instant, required, allowed in (("19991231 235959", {b"test 0 1 y", b"exact 0 1 y"}, {b"test 0 1 y", b"exact 0 1 y"}),
                                          ("20000101 000000", {b"test 0 1 y"}, {b"test 0 1 y"}),
                                          ("20000101 000005", set(), {b"test 0 1 y"}),
                                          ("20000101 000011", set(), set())):
            c = connect(model(groups=groups, **policy))
            e = c.send(("NEWGROUPS " + instant + " GMT\r\n").encode())
            for candidate in (set(), {b"test 0 1 y"}, {b"exact 0 1 y"}, {b"test 0 1 y", b"exact 0 1 y"}):
                self.assertEqual(e.check(b"231 list\r\n", encode_block(packed(sorted(candidate)))).ok,
                                 required <= candidate <= allowed, (instant, candidate))
            self.assertFalse(e.check(b"231 list\r\n", encode_block(b"test 0 1 y\r\ntest 0 1 y\r\n")).ok)

    def test_active_times_uses_external_setup_window(self):
        # Exact reply block from shard-3/repro-602-reader-whole-00009.json.
        reply = b"fn.test 1793214256 unattributed\r\nfn.letters 1793214256 unattributed\r\n.\r\n"
        c = connect(model(groups={"fn.test": {}, "fn.letters": {}},
                          group_creation_window=(1793214250, 1793214260)))
        e = c.send(b"LIST ACTIVE.TIMES\r\n")
        for bad in (reply.replace(b"1793214256", b"1793214261"),
                    reply.replace(b"fn.test", b"wrong"),
                    reply.replace(b"unattributed", b"someone"),
                    reply.replace(b"fn.letters", b"fn.test")):
            self.assertFalse(e.check(b"215 information follows\r\n", bad).ok)
        accept(e, b"215 information follows\r\n", reply)
        c = connect(model(groups={"fn.test": {}, "fn.letters": {}}))
        self.assertFalse(c.send(b"LIST ACTIVE.TIMES\r\n").check(b"215 information follows\r\n", reply).ok)
        c = connect(model(groups={"fn.test": {"created_at": 10}}, group_creation_window=(20, 30)))
        send(c, "LIST ACTIVE.TIMES", "215 information follows", b"fn.test 10 unattributed\r\n")


class H2dRecordedReplyTests(unittest.TestCase):
    def test_required_close_statuses_accept_eof_but_not_silence(self):
        c = connect(model())
        e = c.send(b"QUIT\r\n")
        self.assertFalse(e.check(b"", None, eof=True).ok)
        e.update(b"205 closing\r\n", None, eof=True)
        after = c.send(b"AUTHINFO USER after-quit\r\n")
        self.assertFalse(after.check(b"381 password\r\n", None, eof=True).ok)
        after.update(b"", None, eof=True)
        c = connect(model())
        c.refused = "too many connections"
        e = c.greeting()
        self.assertFalse(e.check(b"", None, eof=True).ok)
        e.update(b"400 too many connections\r\n", None, eof=True)
        for sasl in (False, True):
            c = connect(model(accounts={"a": "good"}), tls=True)
            for i in range(3):
                if sasl:
                    command = b"AUTHINFO SASL PLAIN " + base64.b64encode(b"\0a\0wrong") + b"\r\n"
                else:
                    send(c, "AUTHINFO USER a", "381 password")
                    command = b"AUTHINFO PASS wrong\r\n"
                e = c.send(command)
                status = b"481 failed\r\n" + (b"400 closing\r\n" if i == 2 else b"")
                self.assertFalse(e.check(b"", None, eof=True).ok)
                e.update(status, None, eof=i == 2)
            self.assertTrue(c.quit)

    def test_recorded_malformed_command_reply_then_eof(self):
        # H2d shard-1/repro-207-reader-whole-00063: 501 belongs to MO\nDE,
        # not the subsequent LIST whose read discovers EOF.
        c = connect(model())
        e = c.send(b"MO\nDE \r\n")
        self.assertTrue(e.close_after_reply)
        self.assertIn("513-518", e.close_spec)
        accept(e, b"501 syntax error\r\n")
        self.assertFalse(c.quit)
        e.update(b"501 syntax error\r\n", None, eof=True)
        e.update(b"501 syntax error\r\n", None, eof=True)
        self.assertTrue(c.quit)
        accept(c.send(b"LIST OVERVIEW.FMT\r\n"), b"")

    def test_transit_bound_requires_refusal_before_eof(self):
        c = connect(model(peer=True, inbound_max_octets=100))
        send(c, "TAKETHIS <one@example.test>", b"")
        e = c.send_block(encode_block(article()))
        self.assertTrue(e.close_after_reply)
        self.assertFalse(e.check(b"", None, eof=True).ok)
        self.assertFalse(e.check(b"439 rejected\r\n", None, eof=True).ok)
        e.update(b"439 <one@example.test> rejected\r\n", None, eof=True)
        self.assertTrue(c.quit)

    def test_sasl_response_is_a_line_before_it_is_base64(self):
        # P-SASL-LINE (H7): overlong or bare-CR/LF responses are 501 malformed; a line that is not base64 is 504.
        for line, code in ((b'x' * 600 + b'\r\n', 501), (b'STAT x\n\rSTARTTLS\r\n', 501), (b'!!\r\n', 504),
                           (b'\r\n', 504), (b'\x16\x03\x01\x00\x05hello\r\n', 504)):
            with self.subTest(line=line[:16]):
                c = connect(model(), tls=True)
                e = c.send(b'AUTHINFO SASL SCRAM-SHA-256\r\n')
                accept(e, b'383 =\r\n')
                reply = c.send(line)
                self.assertEqual(set(reply._get().codes), {code})
                self.assertEqual(reply.close_after_reply, code == 501)

    def test_invalid_utf8_is_malformed_before_whitespace(self):
        # H6 pin with layer D (specs/nntp.md:513-518): decode first, so a bad-UTF-8 line with
        # surrounding whitespace is malformed (501, the connection may close), never a kept 501.
        for command in (b"GROUP fn.\xff \r\n", b" GROUP fn.\xff\r\n", b"GROUP fn.\xff\t\r\n"):
            with self.subTest(command=command):
                e = connect(model()).send(command)
                self.assertTrue(e.close_after_reply)
                self.assertIn("513-518", e.close_spec)
                accept(e, b"501 syntax error\r\n")
        e = connect(model()).send(b"GROUP fn.test \r\n")  # valid UTF-8: plain 501, connection kept
        self.assertFalse(e.close_after_reply)
        accept(e, b"501 syntax error\r\n")

    def test_malformed_eof_is_optional_and_requires_observed_eof(self):
        for command in (b"HEAD <a@b\r>\r\n", b"GROUP fn.\xff\r\n"):
            with self.subTest(command=command):
                c = connect(model())
                e = c.send(command)
                self.assertFalse(e.check(b"", None).ok)
                self.assertTrue(e.check(b"", None, eof=True).ok)
                e.update(b"", None, eof=True)
                self.assertTrue(c.quit)
                c = connect(model())
                accept(c.send(command), b"501 syntax error\r\n")
                self.assertFalse(c.quit)
                send(c, "LAST", "412 no newsgroup selected")

    def test_unterminated_body_refusal_does_not_invent_safe_boundary(self):
        c = connect(model())
        send(c, "POST", "340 send article")
        accept(c.send_block(b"Subject: partial\r\n"), b"441 article was not received\r\n")
        self.assertTrue(c.quit)

    def test_overlength_requires_501_even_when_closing(self):
        c = connect(model())
        e = c.send(b"LAST " + b"x" * 506 + b"\r\n")
        self.assertTrue(e.close_after_reply)
        self.assertFalse(e.close_without_reply)
        self.assertFalse(e.check(b"", None, eof=True).ok)
        self.assertTrue(e.check(b"501 syntax error\r\n", None, eof=True).ok)
        e.update(b"501 syntax error\r\n", None, eof=True)
        self.assertTrue(c.quit)

    def test_ordinary_errors_do_not_license_silent_close(self):
        for command in (b"BODY -1\r\n", b"XYZZY\r\n", b"TAKETHIS <a@b\r\n"):
            e = connect(model(peer=True)).send(command)
            self.assertFalse(e.close_without_reply)
            self.assertFalse(e.check(b"", None, eof=True).ok)
        e = connect(model(peer=True)).send(b"TAKETHIS <valid@example.test>\r\n")
        self.assertTrue(e.check(b"", None).ok)
        self.assertFalse(e.check(b"", None, eof=True).ok)

    def test_malformed_takethis_consumes_body_before_refusal(self):
        commands = (b"TAKETHIS <a@b@c\r\n", b"TAKETHIS <a@b\r\n",
                    b"TAKETHIS <a@b>junk\r\n", b"TAKETHIS\r\n",
                    b"TAKETHIS <bad\xca@test>Path: a\r\n")
        for command in commands:
            for echo in (command.split()[1] if len(command.split()) > 1 else b"-", b"-"):
                with self.subTest(command=command, echo=echo):
                    c = connect(model(peer=True))
                    initial = c.send(command)
                    self.assertFalse(initial.check(b"439 - refused\r\n", None).ok)
                    accept(initial, b"")
                    self.assertIsNotNone(c.pending)
                    with self.assertRaisesRegex(ValueError, "article body owed"):
                        c._dispatch(b"DATE\r\n")
                    block = c.send_block(encode_block(article()))
                    self.assertFalse(block.check(b"239 - accepted\r\n", None).ok)
                    self.assertFalse(block.check(b"439 unrelated refused\r\n", None).ok)
                    accept(block, b"439 " + echo + b" rejected\r\n")
                    self.assertIsNone(c.pending)
                    self.assertFalse(c.model.articles)
                    send(c, "DATE", "111 20261029120000")

    def test_rejected_dot_terminated_body_can_continue(self):
        # Reduced NUL-body witnesses for all fourteen H2d closed rows; literal
        # responses match seed8 TAKETHIS, seed601 IHAVE, seed602 POST.
        for command, preliminary, refusal in (
                ("TAKETHIS <fz8.1.860518676@fuzz.invalid>", b"",
                 b"439 <fz8.1.860518676@fuzz.invalid>\r\n"),
                ("IHAVE <fz601.2.117886944@fuzz.invalid>", b"335 send article\r\n",
                 b"437 transfer rejected; not a valid article\r\n"),
                ("POST", b"340 send article\r\n",
                 b"441 posting failed; the article is not valid syntax\r\n")):
            with self.subTest(command=command):
                c = connect(model(peer=True))
                send(c, command, preliminary)
                e = c.send_block(b"Subject: \r\n\r\nx.\r\n\x00\r\n.\r\n")
                accept(e, refusal)
                self.assertIsNone(c.pending)
                self.assertFalse(c.quit)
                send(c, "LAST", "412 no newsgroup selected")

    def test_invalid_post_path_keeps_named_reason(self):
        # H2d shard-1/repro-206-peer-whole-00060 has ALSO ': empty name'.
        # A16 leaves compound-defect precedence open; specs905-909,930-935
        # do determine the Path-only named refusal. Do not weaken it.
        for extra in (b"Path: \r\n", b"Path: \r\n: empty name\r\n"):
            c = connect(model())
            send(c, "POST", "340 send article")
            e = c.send_block(encode_block(article(extra=extra)))
            self.assertFalse(e.check(b"240 article received OK\r\n", None).ok)
            self.assertFalse(e.check(b"441 posting failed; the article is not valid syntax\r\n", None).ok)
            accept(e, b"441 Path is not a valid path\r\n")


class PostingTransitTests(unittest.TestCase):
    def test_each_238_counts_even_for_repeated_message_id(self):
        c = connect(model(peer=True, max_inflight=2))
        for _ in range(2):
            send(c, "CHECK <repeat@t>", "238 <repeat@t> wanted")
        send(c, "CHECK <repeat@t>", "431 <repeat@t> window full")
        accept(c.send(b"TAKETHIS <repeat@t>\r\n"), b"")
        raw = article("<repeat@t>", extra=b"Path: peer.test!not-for-mail\r\n")
        accept(c.send_block(encode_block(raw)), "436 <repeat@t> deferred")
        self.assertEqual(c.inflight, ["<repeat@t>"])
        send(c, "CHECK <other@t>", "238 <other@t> wanted")

    def test_unknown_crosspost_policy_accepts_either_permitted_outcome(self):
        for status in ("240 accepted", "441 posting failed; unknown group"):
            c = connect(model())
            raw = article(group="test,unknown")
            send(c, "POST", "340 send")
            accept(c.send_block(encode_block(raw)), status)
            if status.startswith("240"):
                self.assertEqual(c.model.groups["test"], [(1, "<one@example.test>")])
                self.assertIn(b"Newsgroups: test,unknown\r\n", c.model.articles["<one@example.test>"])
            else:
                self.assertFalse(c.model.articles)

    def test_missing_projection_input_does_not_partially_commit(self):
        c = connect(model(accounts={"a": "pw"}))
        send(c, "AUTHINFO USER a", "381 password")
        send(c, "AUTHINFO PASS pw", "281 accepted")
        send(c, "POST", "340 send")
        e = c.send_block(encode_block(article()))
        with self.assertRaisesRegex(ValueError, "stored_articles"):
            e.update(b"240 accepted\r\n", None)
        self.assertIsNotNone(c.pending)
        self.assertFalse(c.model.articles)
        self.assertEqual(c.model.watermarks["test"], 0)
        c.policy["stored_articles"] = {"<one@example.test>": article()}
        accept(e, "240 accepted")

    def test_generated_projection_environment_and_refusal_do_not_fabricate_bytes(self):
        ident = "<generated@t>"
        source = b"From: a@t\r\nSubject: test\r\nNewsgroups: test\r\n\r\nbody\r\n"
        stored = article(ident, body=b"body\r\n")
        c = connect(model(generated_id=ident, stored_articles={ident: stored}))
        send(c, "POST", "340 send")
        accept(c.send_block(encode_block(source)), "240 accepted")
        self.assertEqual(c.model.articles[ident], stored)
        self.assertEqual(c.model.sources[ident], source)

    def test_post_acceptance_updates_only_on_240_and_repin_only_poster(self):
        m = model(server="news.test")
        c, other = connect(m), connect(m)
        raw = article()
        send(c, "POST", "340 send article")
        outcome = c.send_block(encode_block(raw))
        self.assertFalse(m.articles)
        accept(outcome, "240 article received OK")
        self.assertEqual(m.groups["test"], [(1, "<one@example.test>")])
        stored = b"Path: news.test!not-for-mail\r\nInjection-Info: news.test\r\n" + raw
        send(c, "ARTICLE <one@example.test>", "220 0 <one@example.test>", b"Xref: news.test test:1\r\n" + stored)
        send(other, "STAT <one@example.test>", "430 absent")
        for source, reply in ((raw, "441 posting failed; this article is already stored here"),
                              (raw + b"changed\r\n", "441 posting failed; a different article with this Message-ID is stored here")):
            send(c, "POST", "340 send")
            accept(c.send_block(encode_block(source)), reply)
        self.assertEqual(m.watermarks["test"], 1)

    def test_post_refusal_uncertainty_and_all_named_words(self):
        # Duplicate/conflict require held identity and are checked in the prior test.
        words = ["malformed", "unaffordable", "history-exhausted",
                 "storage-failed", "control-not-filed", "control-malformed", "refused",
                 "read-only group", "moderation", "login-unsigned", "login-not-bound", "uncertain"]
        for word in words:
            c = connect(model())
            send(c, "POST", "340 send")
            text = {"duplicate": "this article is already stored here",
                    "conflict": "a different article with this Message-ID is stored here"}.get(word, word)
            accept(c.send_block(encode_block(article())), "441 posting failed; " + text)
            self.assertFalse(c.model.articles)
            self.assertEqual(c.model.watermarks["test"], 0)
            self.assertEqual(c.model.post_outcomes[-1][2], "uncertain" if word == "uncertain" else "refused")

    def test_post_required_fields_closed_group_and_moderation(self):
        cases = [(model(), b"Subject: missing From\r\n\r\nbody\r\n", "malformed"),
                 (model(groups={"test": {"read_only": True}}), article(), "read-only"),
                 (model(groups={"test": {"moderated": True}}), article(extra=b"Approved: forged\r\n"), "moderator")]
        for m, raw, text in cases:
            c = connect(m)
            send(c, "POST", "340 send")
            e = c.send_block(encode_block(raw))
            self.assertFalse(e.check(b"240 accepted\r\n", None).ok)
            accept(e, "441 posting failed; " + text)
            self.assertFalse(m.articles)

    def test_pipelined_post_outcome_precedes_following_command(self):
        c = connect(model())
        send(c, "POST", "340 send")
        post = c.send_block(encode_block(article()))
        group = c.send(b"GROUP test\r\n")
        with self.assertRaises(RuntimeError):
            group.check(b"211 0 1 0 test\r\n", None)
        accept(post, "240 accepted")
        accept(group, "211 1 1 1 test")

    def test_reader_transit_refusal_peer_offers_and_window(self):
        c = connect(model())
        for command in ("IHAVE <a@t>", "CHECK <a@t>", "TAKETHIS <a@t>"):
            send(c, command, "502 reader connection")
        c = connect(model(peer=True, max_inflight=1))
        send(c, "MODE STREAM", "203 streaming")
        send(c, "CHECK <one@example.test>", "238 <one@example.test> wanted")
        send(c, "CHECK <two@t>", "431 <two@t> retry later")
        accept(c.send(b"TAKETHIS <one@example.test>\r\n"), b"")
        accept(c.send_block(encode_block(article(extra=b"Path: peer.test!not-for-mail\r\n"))), "239 <one@example.test> accepted")
        self.assertFalse(c.inflight)
        send(c, "CHECK <one@example.test>", "438 <one@example.test> held")
        send(c, "IHAVE <one@example.test>", "435 already held")
        send(c, "IHAVE <two@t>", "335 send")
        accept(c.send_block(encode_block(article("<two@t>", extra=b"Path: peer.test!not-for-mail\r\n"))), "436 deferred")
        self.assertNotIn("<two@t>", c.model.articles)

    def test_transit_body_limit_closes_with_message_id(self):
        c = connect(model(peer=True, article_limit=20))
        accept(c.send(b"TAKETHIS <one@example.test>\r\n"), b"")
        e = c.send_block(encode_block(article()))
        self.assertFalse(e.check(b"439 rejected\r\n", None).ok)
        accept(e, "439 <one@example.test> size limit")
        self.assertTrue(c.quit)
        accept(c.send(b"HELP\r\n"), b"")

    def test_fn_extension_shapes(self):
        c = selected(model(peer=True, articles=[("<one@example.test>", article(), ["test"])]))
        send(c, "XFNCATCHUP test 0 chain 16", "423 unavailable")
        digest = "a" * 64
        send(c, f"XFN-ZARTICLE <one@example.test> {digest}", f"229 {digest} 100 60", b"encoded\r\n")
        send(c, f"XFN-ZARTICLE <one@example.test> {digest}", "220 1 <one@example.test>", b"Xref: .invalid test:1\r\n" + article())


class RfcTranscriptTests(unittest.TestCase):
    def test_every_fixture_is_verbatim_rfc_excerpt_and_replays(self):
        fixtures = sorted(FIXTURES.glob("*/*.txt"))
        self.assertEqual(len(fixtures), 27)
        for path in fixtures:
            with self.subTest(fixture=str(path.relative_to(FIXTURES))):
                text = path.read_text().splitlines()
                match = re.search(r"RFC (\d+) §([^;]+);.*lines (\d+)-(\d+)", text[0])
                self.assertIsNotNone(match)
                rfc, section, start, end = match.groups()
                source = (Path(__file__).resolve().parents[3] / f"rfc{rfc}.txt").read_text().split("\n")
                literal = [s.strip() for s in source[int(start)-1:int(end)] if re.match(r"\s*\[[CS]\]", s)]
                self.assertEqual(text[1:], literal)
                c = self.fixture_connection(path.stem)
                rows = [(s[1], s[3:].removeprefix(" ").encode() + b"\r\n") for s in text[1:]]
                i = 0
                while i < len(rows):
                    if rows[i][0] == "C":
                        expectation = c.send(rows[i][1]); i += 1
                    else:
                        expectation = c.greeting()
                    self.assertLess(i, len(rows), "fixture must include its server answer")
                    self.assertEqual(rows[i][0], "S")
                    status = rows[i][1]; i += 1
                    body = None
                    if expectation.multiline:
                        pieces = []
                        while i < len(rows) and rows[i][0] == "S":
                            pieces.append(rows[i][1]); i += 1
                            if pieces[-1] == b".\r\n":
                                break
                        body = b"".join(pieces)
                    accept(expectation, status, body)

    @staticmethod
    def fixture_connection(name):
        raw = (b"Path: pathost!demo!whitehouse!not-for-mail\r\n"
               b'From: "Demo User" <nobody@example.net>\r\nNewsgroups: misc.test\r\n'
               b"Subject: I am just a test article\r\nDate: 6 Oct 1998 04:38:40 -0500\r\n"
               b"Organization: An Example Net, Uncertain, Texas\r\nMessage-ID: <45223423@example.com>\r\n"
               b"\r\nThis is just a test article.\r\n")
        groups = {"misc.test": {}, "example.currently.empty.newsgroup": {"watermark": 3999},
                  "news.test": {}, "sci.test": {}}
        articles = [("<45223423@example.com>", raw, ["misc.test"])]
        if name == "newnews":
            articles += [("<i.am.a.new.article@example.com>", article("<i.am.a.new.article@example.com>"), ["news.test"]),
                         ("<i.am.another.new.article@example.com>", article("<i.am.another.new.article@example.com>"), ["sci.test"])]
        policy = {"server": None, "posting": name != "greeting-read", "clock": "19990623135624",
                  "protected_only": name == "protected"}
        if name == "newnews":
            policy["clock"] = None  # legacy unknown horizon must over-report
        if name.startswith("subscriptions"):
            names = ["local.welcome", "local.test", "news.newusers.questions", "news.announce.newusers"]
            groups = dict.fromkeys(names, {})
            articles = []
            policy["subscriptions"] = names
        if name == "counts-wildmat":
            nums = list(range(3000234, 3000234 + 1233)) + [3002322]
            entries = [(n, f"<count{n}@t>") for n in nums]
            groups = {"misc.test": {"entries": entries}, "rec.food.drink.tea": {"entries": [(51,"<tea51@t>"),(70,"<tea70@t>"),(100,"<tea100@t>")]}, "local.tea": {}}
            articles = [(ident, article(ident), [g]) for g, f in groups.items() for _, ident in f.get("entries", [])]
        if name == "motd":
            policy["motd"] = ["Attention all users,", "", "This server will be down for scheduled upgrades on February 1st.",
                              "It should be back up by 8:00 a.m. February 2nd.", "Any questions should be e-mailed to <newsmaster@example.com>.",
                              "", "Apologies for the disturbance."]
        m = NntpModel(groups, articles, {"fred": "flintstone", "barney": "rubble"}, policy)
        return connect(m)


class ModelMachine(RuleBasedStateMachine):
    identities = Bundle("identities")

    def __init__(self):
        super().__init__()
        self.m = model(groups={"test": {}, "other": {}})
        self.c = connect(self.m)
        self.serial = 0
        self.previous_watermarks = {"test": 0, "other": 0}
        self.issue_log = {"test": [], "other": []}

    @rule(target=identities, group=st.sampled_from(["test", "other"]))
    def publish(self, group):
        self.serial += 1
        ident = f"<generated{self.serial}@test>"
        self.m.add_article(ident, article(ident, group), [group])
        self.issue_log[group].append(len(self.issue_log[group]) + 1)
        return ident

    @rule(ident=identities)
    def withdraw(self, ident):
        self.m.withdraw(ident)

    @rule(group=st.sampled_from(["test", "other"]))
    def select(self, group):
        if self.c.quit:
            accept(self.c.send(f"GROUP {group}\r\n".encode()), b"")
        else:
            rows = self.c._available(group, live=True)
            wm = len(self.issue_log[group])
            low, high = (rows[0][0], rows[-1][0]) if rows else (wm + 1, wm)
            send(self.c, f"GROUP {group}", f"211 {len(rows)} {low} {high} {group}")

    @rule(forward=st.booleans())
    def move(self, forward):
        command = "NEXT" if forward else "LAST"
        if self.c.quit:
            accept(self.c.send(command.encode() + b"\r\n"), b"")
            return
        if self.c.current_group is None:
            send(self.c, command, "412 no group")
        elif self.c.current_article_number is None:
            send(self.c, command, "420 no article")
        else:
            rows = self.c._available(self.c.current_group)
            indexes = [n for n, _ in rows]
            i = indexes.index(self.c.current_article_number) + (1 if forward else -1)
            if 0 <= i < len(rows):
                n, ident = rows[i]
                send(self.c, command, f"223 {n} {ident}")
            else:
                send(self.c, command, "421 no next" if forward else "422 no previous")

    @rule()
    def quit(self):
        if self.c.quit:
            accept(self.c.send(b"QUIT\r\n"), b"")
        else:
            send(self.c, "QUIT", "205 closing")

    @rule()
    def reconnect(self):
        if not self.c.quit:
            send(self.c, "QUIT", "205 closing")
        self.c = connect(self.m)

    @invariant()
    def numbers_never_reused_and_watermarks_monotone(self):
        for group, issued in self.m.issued.items():
            assert issued == self.issue_log[group]
            assert all(a < b for a, b in zip(issued, issued[1:]))
            assert len(issued) == len(set(issued))
            assert self.m.watermarks[group] >= self.previous_watermarks[group]
            self.previous_watermarks[group] = self.m.watermarks[group]

    @invariant()
    def current_article_available_in_its_pinned_view_or_none(self):
        n = self.c.current_article_number
        assert n is None or n in dict(self.c._available(self.c.current_group))

    @invariant()
    def after_quit_nothing_is_expected(self):
        if self.c.quit:
            e = self.c.send(b"AUTHINFO USER after-quit\r\n")
            assert not e.multiline
            assert e.check(b"", None).ok
            assert not e.check(b"381 password\r\n", None).ok
            e.update(b"", None)


TestModelStateMachine = ModelMachine.TestCase
TestModelStateMachine.settings = settings(max_examples=200, stateful_step_count=50,
                                          deadline=None, database=None, derandomize=True)


def fake_server(backend, command, *, bug=None, state=None):
    """Small wire responder with one explicit fault switch, plus a clean control.

    The fake has its own state; it never asks Expect to manufacture an answer.
    @publish is its controlled external durable-acceptance event.
    """
    state = state if state is not None else {}
    if command == b"@publish":
        ident = "<two@t>"
        backend.add_article(ident, article(ident), ["test"])
        if bug == "reuse":
            backend.groups["test"][-1] = (1, ident)
            backend.watermarks["test"] = 1
        return b"", None
    if state.get("quit"):
        return (b"500 framed after QUIT\r\n", None) if bug == "after-quit" else (b"", None)
    if command == b"QUIT\r\n":
        state["quit"] = True
        return b"205 closing\r\n", None
    if command == b"GROUP test\r\n":
        rows = [(n, m) for n, m in backend.groups["test"] if m not in backend.withdrawn]
        lo, hi = (min(n for n, _ in rows), max(n for n, _ in rows)) if rows else (backend.watermarks["test"] + 1, backend.watermarks["test"])
        return f"211 {len(rows)} {lo} {hi} test\r\n".encode(), None
    if command == b"XOVER 999-1000\r\n":
        return (b"423 empty\r\n" if bug == "423-for-420" else b"420 empty\r\n"), None
    raise AssertionError(command)


class MutationControls(unittest.TestCase):
    def test_mutation_reused_number_is_caught_by_group_after_withdrawal(self):
        oracle = model(articles=[("<one@t>", article("<one@t>"), ["test"])])
        bad = model(articles=[("<one@t>", article("<one@t>"), ["test"])])
        good = model(articles=[("<one@t>", article("<one@t>"), ["test"])])
        c = connect(oracle)
        for m in (oracle, bad, good):
            m.withdraw("<one@t>")
        oracle.add_article("<two@t>", article("<two@t>"), ["test"])
        fake_server(bad, b"@publish", bug="reuse")
        fake_server(good, b"@publish")
        e = c.send(b"GROUP test\r\n")
        self.assertFalse(e.check(*fake_server(bad, b"GROUP test\r\n")).ok)
        accept(e, *fake_server(good, b"GROUP test\r\n"))

    def test_mutation_423_instead_of_420_is_caught_by_xover_empty_range(self):
        c = selected()
        e = c.send(b"XOVER 999-1000\r\n")
        self.assertFalse(e.check(*fake_server(c.model, b"XOVER 999-1000\r\n", bug="423-for-420")).ok)
        accept(e, *fake_server(c.model, b"XOVER 999-1000\r\n"))

    def test_mutation_reply_after_quit_is_caught_by_none_predicate(self):
        c = connect(model())
        state = {}
        accept(c.send(b"QUIT\r\n"), *fake_server(c.model, b"QUIT\r\n", state=state))
        e = c.send(b"AUTHINFO USER after-quit\r\n")
        self.assertFalse(e.check(*fake_server(c.model, b"AUTHINFO USER after-quit\r\n", bug="after-quit", state=state)).ok)
        accept(e, *fake_server(c.model, b"AUTHINFO USER after-quit\r\n", state=state))


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""The fuzzer's table-driven grammar is the hand-written one it replaced.

tests/fuzz_nntp.py's Gen.step reads every command word and argument grammar
from the protocol table (books/protocol-table.lisp through
tools/protocol_emit.py).  This differential keeps the hand-written step of
2026-09-27 (LegacyGen.step, verbatim) and asserts that the two generate
byte-identical transcripts, seed for seed and mode for mode: the same RNG
draws in the same order.  A later change to the grammar edits the table and
this file's expectation together, and names the difference here.

Named differences (the table has them, the grammar does not send them):
fuzz_nntp.UNFUZZED_ROWS -- XFNCATCHUP; QUIT and COMPRESS are
sent in the fuzzer's own spellings (fuzz_nntp.RAW_ROWS), not through their
rows.  The AUTHINFO SASL mechanism choice follows the table (sasl-4's SCRAM
additions).  XFN-ZARTICLE (NNT-055) takes the last hundredth of the
ARTICLE family's share (compress-10), through its row's grammar.

    python3 -m unittest tests.test_protocol_fuzz_grammar
"""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tests"))
import fuzz_nntp  # noqa: E402
from fuzz_nntp import (CRLF, DATES, GROUPS, HEADER_NAMES, MALFORMED_IDS,  # noqa: E402,F401
                       RANGES, WILDMATS)


class LegacyGen(fuzz_nntp.Gen):
    """Gen with the hand-written step it had before the table."""

    def step(self):  # verbatim, tests/fuzz_nntp.py before lane defprotocol
        """One or more items for one protocol step."""
        rng = self.rng
        r = rng.random()
        c = self.command
        if r < 0.04:
            return [c([b"CAPABILITIES"] + ([self.choice([b"x", b"AUTOUPDATE"])] if self.chance(0.2) else []))]
        if r < 0.08:
            return [c([b"MODE", self.choice([b"READER", b"STREAM", b"", b"reader", b"POSTER", b"X"])])]
        if r < 0.16:
            return [c([b"GROUP", self.choice(GROUPS)] + ([b"x"] if self.chance(0.05) else []))]
        if r < 0.20:
            words = [b"LISTGROUP"]
            if self.chance(0.8):
                words.append(self.choice(GROUPS))
                if self.chance(0.5):
                    words.append(self.choice(RANGES))
            return [c(words)]
        if r < 0.24:
            return [c([self.choice([b"LAST", b"NEXT"])])]
        if r < 0.35:
            verb = self.choice([b"ARTICLE", b"HEAD", b"BODY", b"STAT"])
            arg = self.rng.random()
            words = [verb]
            if arg < 0.4:
                words.append(self.msgid())
            elif arg < 0.8:
                words.append(self.choice(RANGES))
            return [c(words)]
        if r < 0.36:
            # compress-10: XFN-ZARTICLE (NNT-055, named difference).
            return [c([b"XFN-ZARTICLE", self.msgid(),
                       self.choice([b"845aa5e18680ef219a9b0f0d0b959cd8886d5eabc12236aae19f301aed9de75e",
                                    b"00", b"x"])])]
        if r < 0.44:
            kw = self.choice([b"", b"ACTIVE", b"NEWSGROUPS", b"OVERVIEW.FMT", b"HEADERS",
                              b"ACTIVE.TIMES", b"DISTRIB.PATS", b"MOTD", b"COUNTS", b"SUBSCRIPTIONS",
                              b"HEADERS MSGID", b"HEADERS RANGE", b"X"])
            words = [b"LIST"] + ([kw] if kw else [])
            if kw and self.chance(0.5):
                words.append(self.choice(WILDMATS))
            return [c(words)]
        if r < 0.50:
            verb = self.choice([b"OVER", b"XOVER"])
            return [c([verb] + ([self.choice(RANGES + [self.msgid()])] if self.chance(0.8) else []))]
        if r < 0.55:
            verb = self.choice([b"HDR", b"XHDR"])
            words = [verb, self.choice(HEADER_NAMES + [b":bytes", b":lines", b"", b"x" * 600])]
            if self.chance(0.7):
                words.append(self.choice(RANGES + [self.msgid()]))
            return [c(words)]
        if r < 0.57:
            words = [b"XPAT", self.choice(HEADER_NAMES), self.choice(RANGES + [self.msgid()]),
                     self.choice(WILDMATS)]
            return [c(words)]
        if r < 0.61:
            d, t = self.choice(DATES)
            if self.chance(0.5):
                words = [b"NEWGROUPS", d, t]
            else:
                words = [b"NEWNEWS", self.choice(WILDMATS), d, t]
            if self.chance(0.4):
                words.append(self.choice([b"GMT", b"UTC", b"gmt", b"X"]))
            return [c(words)]
        if r < 0.63:
            return [c([self.choice([b"HELP", b"DATE"]) if self.mode != "reader" else b"HELP"])]
        if r < 0.70:
            post = c([b"POST"] + ([b"x"] if self.chance(0.05) else []))
            items = [post]
            if self.chance(0.85):
                items.append(self.article())
            return items
        if r < 0.76:
            mid = self.msgid()
            items = [c([b"IHAVE", mid])]
            if self.chance(0.8):
                items.append(self.article(mid if self.chance(0.9) else None, transit=True))
            return items
        if r < 0.80:
            return [c([b"CHECK", self.msgid()])]
        if r < 0.85:
            mid = self.msgid()
            return [c([b"TAKETHIS", mid]), self.article(mid if self.chance(0.9) else None, transit=True)]
        if r < 0.91:
            kind = self.rng.randrange(6)
            if kind == 0:
                return [c([b"AUTHINFO", b"USER", self.choice([b"fuzz", b"nobody", b"", b"u" * 600])]),
                        c([b"AUTHINFO", b"PASS", self.choice([b"fuzz-password", b"wrong", b"", b"p" * 600])])]
            if kind == 1:
                return [c([b"AUTHINFO", b"PASS", b"fuzz-password"])]
            if kind == 2:
                # lane sasl-4 (NNT-056): the table's SASL mechanisms grew
                # SCRAM-SHA-256 (with and without an initial response), the
                # -PLUS mechanism fn does not offer, and two malformed PLAIN
                # responses (named difference, compress-9).
                return [c([b"AUTHINFO", b"SASL", self.choice([b"PLAIN", b"PLAIN AGZ1enoAZnV6ei1wYXNzd29yZA==", b"X",
                                                              b"SCRAM-SHA-256", b"SCRAM-SHA-256 biwsbj1mdXp6LHI9ZnV6eg==",
                                                              b"SCRAM-SHA-256-PLUS", b"PLAIN =", b"PLAIN !!!!"])])]
            if kind == 3:
                return [c([b"AUTHINFO", self.choice([b"GENERIC", b"SIMPLE", b"", b"user"])])]
            if kind == 4:
                return [c([b"AUTHINFO", b"USER", b"fuzz"])]
            return [c([b"XREDEEM"] + [self.choice([b"code", b"", b"x" * 600])] * self.rng.randrange(3))]
        if r < 0.93:
            return [c([b"STARTTLS"])] if self.mode != "tls" else [c([b"HELP"])]
        if r < 0.96:
            return [c([self.choice([b"FOO", b"XYZZY", b"SLAVE", b"COMPRESS DEFLATE", b"XFEATURE COMPRESS GZIP",
                                    b"XROVER", b"XGTITLE", b"CHECK", b"IHAVE", b"TAKETHIS", b"ARTICLE <"])])]
        if r < 0.98:
            return [self.choice([CRLF, b"\n", b" \r\n", b"\x00\r\n", b"\r", b"\xff\xfe\r\n",
                                 b"\x16\x03\x01\x00\x05hello\r\n"])]
        return [self.choice([b"QUIT", b"quit", b"QUIT x"]) + self.terminator()]



SEEDS = range(3000)
MODES = ("reader", "node", "peer", "tls")


class ProtocolFuzzGrammarTests(unittest.TestCase):
    def test_transcripts_are_byte_identical(self):
        for mode in MODES:
            for seed in SEEDS:
                old = LegacyGen(seed, mode).transcript()
                new = fuzz_nntp.Gen(seed, mode).transcript()
                self.assertEqual(old, new, "seed %d mode %s" % (seed, mode))

    def test_every_fuzzed_row_is_a_table_row_and_the_rest_are_named(self):
        table = fuzz_nntp.PROTOCOL
        sent = {"CAPABILITIES", "MODE", "GROUP", "LISTGROUP", "LAST", "NEXT",
                "ARTICLE", "HEAD", "BODY", "STAT", "LIST", "OVER", "XOVER", "HDR",
                "XHDR", "XPAT", "NEWGROUPS", "NEWNEWS", "HELP", "DATE", "POST",
                "IHAVE", "CHECK", "TAKETHIS", "AUTHINFO", "XREDEEM", "STARTTLS",
                "XFN-ZARTICLE"}
        with_fuzz = {n for n, r in table.items() if r["fuzz"] is not None}
        self.assertEqual(with_fuzz - sent,
                         set(fuzz_nntp.UNFUZZED_ROWS) | set(fuzz_nntp.RAW_ROWS))
        self.assertTrue(sent <= with_fuzz)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""The served differential's transcripts as chunk files.

Imports the chunk lists tests/test_native_served_differential.py sends (its
seven cases, by the same constants), plus longer sessions for timing, and
writes each in the length-prefixed chunk format `--fn model' reads.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tests.test_native_served_differential import (  # noqa: E402
    MULTI_COMMAND, UTF8_WILDMAT, QUIT_WITH_TRAILER, BARE_LF)

CASES = {
    "whole": [MULTI_COMMAND],
    "cut-inside": [MULTI_COMMAND[:12], MULTI_COMMAND[12:]],
    "cut-after-reply": [MULTI_COMMAND[:20], MULTI_COMMAND[20:]],
    "bytewise": [MULTI_COMMAND[i:i + 1] for i in range(len(MULTI_COMMAND))],
    "split-utf8": [UTF8_WILDMAT[:16], UTF8_WILDMAT[16:]],
    "after-quit": [QUIT_WITH_TRAILER],
    "bare-lf": [BARE_LF],
}
# Longer read sessions over the seeded archive (not in the test module):
# every reader command the seed can answer, and a 200-command session.
READER = (b"CAPABILITIES\r\nMODE READER\r\nDATE\r\nHELP\r\nLIST\r\nLIST ACTIVE fn.*\r\n"
          b"LIST NEWSGROUPS\r\nGROUP fn.letters\r\nSTAT\r\nHEAD\r\nBODY\r\nARTICLE\r\n"
          b"ARTICLE <reader@example.invalid>\r\nLISTGROUP fn.letters\r\nOVER 1\r\nHDR Subject 1\r\n"
          b"NEXT\r\nLAST\r\nNEWGROUPS 20000101 000000\r\nNEWNEWS * 20000101 000000\r\nPOST\r\n"
          b"XYZZY\r\nQUIT\r\n")
CASES["reader-commands"] = [READER]
CASES["session-200"] = [(b"GROUP fn.letters\r\nSTAT\r\nARTICLE 1\r\nHEAD 1\r\n" * 50) + b"QUIT\r\n"]

# POST sessions: served only with posting allowed and a clock observation,
# which the image's `--fn model' never sets (it serves read-only), so these
# are compared with ACL2 evaluating the same functions (tools/extract/post-ref.lisp).
ARTICLE = (b"From: poster@example.invalid\r\nNewsgroups: fn.letters\r\nSubject: extracted\r\n"
           b"\r\nA body line.\r\n..dot-stuffed\r\n.\r\n")
POSTS = {
    "post-one": [b"MODE READER\r\nPOST\r\n", ARTICLE, b"QUIT\r\n"],
    "post-bad": [b"POST\r\n", b"Subject: no newsgroups\r\n\r\nx\r\n.\r\nQUIT\r\n"],
    "post-bytewise": [bytes([b]) for b in b"POST\r\n" + ARTICLE + b"DATE\r\nQUIT\r\n"],
}


def write(path, chunks):
    with open(path, "wb") as h:
        for c in chunks:
            h.write(b"%d\n" % len(c))
            h.write(bytes(c))


if __name__ == "__main__":
    out = Path(sys.argv[1])
    out.mkdir(parents=True, exist_ok=True)
    for name, chunks in CASES.items():
        write(out / (name + ".chunks"), chunks)
        print(name, len(chunks), sum(len(c) for c in chunks))
    (out / "post").mkdir(exist_ok=True)
    for name, chunks in POSTS.items():
        write(out / "post" / (name + ".chunks"), chunks)
        print(name, len(chunks), sum(len(c) for c in chunks))
    if len(sys.argv) > 2:
        # the chunk lists as ACL2 constants for the reference evaluation
        with open(sys.argv[2], "w") as h:
            for name, chunks in POSTS.items():
                h.write("(defconst *xt-%s* '(%s))\n" % (name, " ".join(
                    "(" + " ".join(str(b) for b in c) + ")" for c in chunks)))

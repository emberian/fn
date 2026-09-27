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

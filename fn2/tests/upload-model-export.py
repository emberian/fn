#!/usr/bin/env python3
"""H's article judgement over the upload contract's fixtures, as ACL2 data.

Usage: python3 fn2/tests/upload-model-export.py > fn2/tests/evidence/upload-model.lisp

fn2-upload's independent contract (fn2/tests/q1-contracts.lisp) compares the
served upload against layer H's spec-derived model (fn2/tests/model/
nntp_model.py), which never sees the server. For each fixture article block
this script asks the model, on a fresh loopback connection that sent POST and
got 340, what the block's reply must be, and writes:

  (NAME BLOCK DATA JUDGEMENT)

BLOCK is the wire block (dot-stuffed, with its terminator), DATA the model's
decoded article (framing.decode_block; nil when the model refuses the
framing), and JUDGEMENT one of
  (:accept)            not definite: the model admits 240 or a 441 (the
                       upload's interim answer is the :not-stored 441 until D5)
  (:refuse ALT ...)    definite: a 441 whose text contains one of the ALTs
                       after its code (the model's 441 .*?(?:ALT|...).*)
  (:framing)           the block's framing is refused: any 441, and the
                       server may close after it
The model's environment: the fixtures' groups exist, posting is open to the
anonymous loopback client, and the article bound is the served one, 8159
(two 4 KiB chunks less the 32-octet digest and one). Any other expectation shape stops the script.
"""
import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from model import nntp_model, framing  # noqa: E402

GROUPS = ("g", "local.test")
LIMIT = 8192 - 33  # the upload's bound: two 4 KiB chunks less the digest and one octet
GOOD = [b"From: a@example.invalid", b"Subject: hello", b"Newsgroups: local.test",
        b"Message-ID: <one@example.invalid>", b"", b"body", b"..stuffed"]
FIXTURES = [
    ("valid", GOOD),
    ("valid-two-chunks", [b"From: a", b"Subject: long", b"Newsgroups: g", b""]
     + [b"b" * 99 + bytes([48 + k % 10]) for k in range(60)]),
    ("subject-missing", [b"From: a", b"Newsgroups: g", b"", b"x"]),
    ("newsgroups-missing", [b"From: a", b"Subject: s", b"", b"x"]),
    ("from-duplicate", [b"From: a", b"From: b", b"Subject: s", b"Newsgroups: g", b"", b"x"]),
    ("xref", [b"From: a", b"Subject: s", b"Newsgroups: g", b"Xref: h g:1", b"", b"x"]),
    ("message-id-bad", [b"From: a", b"Subject: s", b"Newsgroups: g", b"Message-ID: <bad>", b"", b"x"]),
    ("unescaped-dot", [b"From: a", b"Subject: s", b"Newsgroups: g", b"", b".bad"]),
    ("too-large", [b"From: a", b"Subject: s", b"Newsgroups: g", b""] + [b"z" * 100] * 100),
]
REFUSE = re.compile(rb"441 \.\*\?\(\?:([A-Za-z |-]+)\)\.\*\Z")

# fn2-txn's fixtures (tests/txn-unit.lisp's): the model's store seeded with
# articles (Message-ID, source) before the POST, in txn-unit's profile
# (local.test carried). Each row adds MID (the octets, nil when absent),
# SEEDS ((mid source) ...) and IDENTITY: t when the model's verdict is its
# identity branch (stored, duplicate, conflict), so the served answer is
# the identity decision.
MID = b"<one@example.invalid>"
GOOD_T = [b"From: a@example.invalid", b"Subject: hello", b"Newsgroups: local.test",
          b"Message-ID: " + MID, b"", b"body", b"..stuffed"]
def _source(lines):
    return framing.decode_block(b"".join(l + b"\r\n" for l in lines) + b".\r\n")
SAME = [(MID, _source(GOOD_T))]
OTHER = [(MID, _source(GOOD_T) + b"x\r\n")]
XREF_T = GOOD_T[:3] + [b"Xref: h g:1"] + GOOD_T[3:]
TXN_FIXTURES = [
    ("valid", GOOD_T, []),
    ("duplicate", GOOD_T, SAME),
    ("conflict", GOOD_T, OTHER),
    ("subject-missing-seeded", [l for l in GOOD_T if l != b"Subject: hello"], SAME),
    ("xref-seeded", XREF_T, SAME),
    ("xref", XREF_T, []),
    ("no-carried-group", [GOOD_T[0], GOOD_T[1], b"Newsgroups: no.such.group, other.group"] + GOOD_T[3:], []),
    ("groups-mixed", [GOOD_T[0], GOOD_T[1], b"Newsgroups: x.y,local.test , z"] + GOOD_T[3:], []),
    ("no-message-id-seeded", [l for l in GOOD_T if not l.startswith(b"Message-ID")], SAME),
]
IDENTITY_REASONS = ({"this article is already stored here"}, {"a different article with this Message-ID is stored here"})


def judge(block, groups=GROUPS, seeds=()):
    articles = [(mid.decode(), src, ["local.test"]) for mid, src in seeds]
    m = nntp_model.NntpModel({g: {} for g in groups}, articles, {}, {"article_limit": LIMIT})
    c = m.connect(tls=False, implicit_tls=False)
    for expect, status in ((c.greeting(), b"200 ready\r\n"), (c.send(b"POST\r\n"), b"340 send\r\n")):
        expect.update(status, None)
    e = c.send_block(block)._get()
    codes, pattern = set(e.codes), e.pattern
    if codes == {240, 441}:
        return ["accept"]
    if codes == {441} and pattern is None and e.close_after_reply:
        return ["framing"]
    found = codes == {441} and pattern is not None and REFUSE.match(pattern)
    if not found:
        raise SystemExit(f"unexpected model expectation: codes {sorted(codes)} pattern {pattern!r}")
    return ["refuse"] + found.group(1).decode().split("|")


def octets(bs):
    return "(" + " ".join(str(b) for b in bs) + ")"


def main():
    print("; Generated by fn2/tests/upload-model-export.py from fn2/tests/model/nntp_model.py. Do not edit.")
    print('(in-package "ACL2")')
    digest = hashlib.sha256()
    for name in ("model/nntp_model.py", "model/framing.py", "upload-model-export.py"):
        with open(os.path.join(HERE, name), "rb") as f:
            digest.update(f.read())
    print(f'(defconst *fn2-upload-model-revision* "model-sha256={digest.hexdigest()}")')
    print(f"(defconst *fn2-upload-model-limit* {LIMIT})")
    print("(defconst *fn2-upload-model-cases*\n '(", end="")
    rows = []
    for name, lines in FIXTURES:
        block = b"".join(l + b"\r\n" for l in lines) + b".\r\n"
        try:
            data = framing.decode_block(block)
        except framing.FramingError:
            data = None
        j = judge(block)
        if (data is None) != (j == ["framing"]):
            raise SystemExit(f"{name}: decode and judgement disagree")
        jtext = "(" + " ".join([":" + j[0]] + ['"' + a + '"' for a in j[1:]]) + ")"
        rows.append(f'("{name}" {octets(block)}\n    {octets(data) if data is not None else "nil"}\n    {jtext})')
    print("\n   ".join(rows) + "))")
    print("(defconst *fn2-txn-model-cases*\n '(", end="")
    rows = []
    for name, lines, seeds in TXN_FIXTURES:
        block = b"".join(l + b"\r\n" for l in lines) + b".\r\n"
        data = framing.decode_block(block)
        j = judge(block, ("local.test",), seeds)
        mid = MID if any(l.startswith(b"Message-ID: ") for l in lines) else None
        identity = mid is not None and (j == ["accept"] or (j[0] == "refuse" and set(j[1:]) in IDENTITY_REASONS))
        jtext = "(" + " ".join([":" + j[0]] + ['"' + a + '"' for a in j[1:]]) + ")"
        stext = "(" + " ".join("(" + octets(m) + " " + octets(src) + ")" for m, src in seeds) + ")"
        rows.append(f'("{name}" {octets(block)}\n    {octets(data)}\n    {jtext} {octets(mid) if mid else "nil"}\n    {stext} {"t" if identity else "nil"})')
    print("\n   ".join(rows) + "))")


if __name__ == "__main__":
    main()

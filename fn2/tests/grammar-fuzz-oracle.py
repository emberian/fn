#!/usr/bin/env python3
"""Check the grammar fuzzer's verdicts against layer H's spec-derived model.

Usage: python3 fn2/tests/grammar-fuzz-oracle.py [--cases build/nntp-fuzz-cases.txt]

The cases are written by `tools/acl2 < fn2/tests/grammar-fuzz-export.lsp >
build/nntp-fuzz-cases.txt` (from the certified tests/grammar-fuzz): the
generated, mutated and randomly mutated transcripts, and for every command
line the transcript runner framed, the grammar's code and the line's span.
Each line is sent alone to a fresh model connection in the case's state
(reader, peer, reader+authenticated), and the model's answer is compared on
the syntax layer only:

  grammar :malformed   model answers 501 and closes
  grammar :syntax      model answers 501 and keeps the connection
  grammar :unknown     model answers 500
  grammar :state       model answers 480 or 502
  grammar :ok          model answers neither 500 nor 501 alone

A line the grammar passes and the model refuses with 501 is a disagreement
unless its keyword is in DEFERRED: a sub-form check the layer doc leaves to
D3's decision code, named with its reason. Every disagreement is printed; the
exit status is 1 when there is one. A disagreement is resolved by reading the
spec, never by bending either side to the other.
"""
import os, re, sys

# Sub-form checks the layer doc (section 6) leaves to D3's decision code: the
# grammar declares one entry per keyword, so what depends on a sub-form or
# on the connection kind is decided after parsing, with the command's own
# declared 501. Each is (keyword, predicate over the line's words, reason).
DEFERRED = [
    ("AUTHINFO", lambda w: True, "sub-form arity: USER and PASS take one argument, SASL a mechanism (RFC 4643 sections 2.3, 2.4)"),
    ("XREDEEM", lambda w: True, "sub-form arity and the redemption code (specs/nntp.md:1784-1914)"),
    ("XFN-ZARTICLE", lambda w: True, "digests are 64 lower-case hex octets (specs/nntp.md:2484-2499); the grammar spans them as :rest"),
    ("XFNCATCHUP", lambda w: True, "field values (specs/nntp.md:676)"),
    ("MODE", lambda w: len(w) > 1 and w[1].upper() == b"STREAM", "MODE STREAM on a reader connection is 501 (RFC 4644 section 2.3): decided by the connection kind"),
    ("LIST", lambda w: len(w) > 2,
     "LIST variant arguments: MOTD, DISTRIB.PATS, DISTRIBUTIONS, OVERVIEW.FMT take none, HEADERS only MSGID or RANGE, the others a wildmat (RFC 3977 section 7.6, RFC 6048; specs/nntp.md:195)"),
    ("XPAT", lambda w: True, "the patterns are wildmats (RFC 2980 section 2.9); the grammar spans them as :rest"),
    ("XHDR", lambda w: True, "the field name's syntax (RFC 5322 section 3.6.8)"),
    ("HDR", lambda w: True, "the field name's syntax (RFC 3977 section 8.5; RFC 5322 section 3.6.8)"),
]

def parse_sexpr(text, i=0):
    def skip(i):
        while i < len(text) and text[i] in " \t\r\n":
            i += 1
        return i
    i = skip(i)
    if text[i] == "(":
        out, i = [], i + 1
        while True:
            i = skip(i)
            if text[i] == ")":
                return out, i + 1
            v, i = parse_sexpr(text, i)
            out.append(v)
    j = i
    while j < len(text) and text[j] not in " \t\r\n()":
        j += 1
    tok = text[i:j]
    return (int(tok) if re.fullmatch(r"-?\d+", tok) else tok.lower()), j

def main(argv):
    path = "build/nntp-fuzz-cases.txt"
    if "--cases" in argv:
        path = argv[argv.index("--cases") + 1]
    sys.path.insert(0, os.path.abspath("fn2/tests"))
    from model import nntp_model as m
    reader = peer = auth = None
    cases = []
    for line in open(path, encoding="latin-1"):
        k = line.find("FUZZ-MASKS ")
        if k >= 0:
            reader, peer, auth = parse_sexpr(line, k + len("FUZZ-MASKS "))[0]
        k = line.find("FUZZ-CASE ")
        if k >= 0:
            cases.append(parse_sexpr(line, k + len("FUZZ-CASE "))[0])
    def conn(mask):
        model = m.NntpModel({"misc.test": {}}, [], {"alice": "secret"},
                            {"peer": bool(mask & peer), "anonymous": "open"})
        c = model.connect(tls=False, implicit_tls=False)
        if mask & auth:
            c.authenticated_as = "alice"
        return c
    bad, lines, deferred, order = [], 0, {}, [0]
    for mask, cls, seed, octets, events in cases:
        octets = [] if octets == "nil" else octets
        events = [] if events == "nil" else events
        data = bytes(octets)
        for code, s, e in events:
            text = data[s:e]
            try:
                r = conn(mask).send(text)._get()
                codes, close = set(r.codes), r.close_after_reply
            except Exception as exc:  # a model failure is reported, never absorbed
                bad.append(f"{cls} seed {seed} mask {mask} {text!r}: model raised {exc!r}"); continue
            lines += 1
            words = re.split(rb"[ \t]+", text.rstrip(b"\r\n"))
            kw = words[0].upper().decode("latin-1")
            if code == ":discard":
                # RFC 4644 section 2.5.2: no reply to the line; the article is read, then 439.
                ok = codes == set() and getattr(r, "malformed_takethis", False)
            elif code == ":malformed":
                ok = codes == {501} and close
                if not ok and codes == {501} and re.search(rb"[ \t]\r?\n?$|^[ \t]", text):
                    # H's model checks surrounding whitespace before UTF-8 and keeps the
                    # connection; specs/nntp.md:513-518 permits either. A note for H.
                    order[0] += 1
                    ok = True
            elif code == ":syntax":
                ok = 501 in codes and not close
            elif code == ":unknown":
                ok = codes == {500}
            elif code == ":state":
                ok = bool(codes & {480, 502})
            else:
                ok = 500 not in codes and codes != {501}
                if not ok and codes == {501}:
                    for k, pred, _ in DEFERRED:
                        if kw == k and pred(words):
                            deferred[kw] = deferred.get(kw, 0) + 1
                            ok = True
                            break
            if not ok:
                bad.append(f"{cls} seed {seed} mask {mask} {text!r}: grammar {code}, model {sorted(codes)}{' close' if close else ''}")
    for b in bad:
        print("DISAGREE", b)
    print(f"FUZZ-ORACLE {len(cases)} cases, {lines} lines, {len(bad)} disagreements; deferred to D3: {deferred}; model whitespace-before-UTF-8 order: {order[0]}")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))

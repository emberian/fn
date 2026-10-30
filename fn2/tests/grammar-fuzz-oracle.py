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
  grammar :ok          model answers no 500, and answers 501 alone exactly
                       when the connection's decision table (D3,
                       books/conn-answer.lisp) answers the line 501

The sub-form checks the grammar leaves to D3 (arity, field names, LIST
arguments, digests, MODE STREAM's connection kind) are therefore compared,
not deferred. Every disagreement is printed; the exit status is 1 when
there is one. A disagreement is resolved by reading the spec, never by
bending either side to the other.
"""
import os, re, sys

# The sub-form checks the grammar leaves to D3 are no longer deferred: each
# line's ANSWER is the status code the connection's decision table
# (books/conn-answer.lisp) gives it, and the model's 501 and D3's 501 must
# agree both ways on every parsed line.

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
    bad, lines = [], 0
    for mask, cls, seed, octets, events in cases:
        octets = [] if octets == "nil" else octets
        events = [] if events == "nil" else events
        data = bytes(octets)
        for code, s, e, answer in events:
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
                # H pin P-UTF8-WS: malformed whatever else is wrong, 501 and close.
                ok = codes == {501} and close
            elif code == ":syntax":
                ok = 501 in codes and not close
            elif code == ":unknown":
                ok = codes == {500}
            elif code == ":state":
                ok = bool(codes & {480, 502})
            else:
                # A parsed line: never 500; and the model refuses it by syntax (501
                # alone) exactly when the decision table answers 501.
                ok = 500 not in codes and ((codes == {501}) == (answer == 501))
            if not ok:
                bad.append(f"{cls} seed {seed} mask {mask} {text!r}: grammar {code}, model {sorted(codes)}{' close' if close else ''}")
    for b in bad:
        print("DISAGREE", b)
    print(f"FUZZ-ORACLE {len(cases)} cases, {lines} lines, {len(bad)} disagreements")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))

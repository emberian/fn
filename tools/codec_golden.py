#!/usr/bin/env python3
"""The golden-vector control of the codec seam (plan §4.1, step T1).

A codec seam changes which function a book above reasons about, never the
octets the image writes.  This tool records the second fact.  It reads the
codec test books, collects every ground term their `assert-event`s evaluate
(both sides of an `equal`, or the whole assertion otherwise), loads each test
book into one ACL2 with `ld`, evaluates every term, and writes the printed
value of each.  Run it once before a seam change and once after, then
`compare`: the control holds when every term of the first file has the same
printed value in the second.

    python3 tools/codec_golden.py record --out build/codec-golden/before.json
    python3 tools/codec_golden.py record --out build/codec-golden/after.json
    python3 tools/codec_golden.py compare build/codec-golden/before.json \\
        build/codec-golden/after.json

WHAT IT DECIDES.  That each recorded ground term prints the same value in both
worlds.  The terms are the test books' own vectors, so the set is what those
books pin: the encoder's octets for their values, the decoder's results for
their octet strings, rejections included.  It does not decide anything about
an input no test book names, and a term the second world cannot evaluate is a
difference, not a pass.

The certificates of each test book's include closure come from the local
cache (`tools/certs.py install`); an uncached dependency is loaded
uncertified by `include-book`, which changes nothing about evaluation.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import theory_check  # noqa: E402

TEST_BOOKS = ("cbor-tests", "records-tests", "frame-tests",
              "frame-trailer-tests", "statement-tests")
MARK = "FNGOLD"


def nested_spans(text: str, start: int, end: int) -> list[tuple[int, int]]:
    """The (start, end) of each immediate element of the list at text[start:end]."""
    depth = 0
    begin = None
    pending_quote = None
    found = []
    for match in theory_check.TOKEN.finditer(text, start + 1, end - 1):
        kind = match.lastgroup
        if kind in ("comment", "block"):
            continue
        if depth == 0:
            if kind == "quote":
                pending_quote = match.start() if pending_quote is None else pending_quote
                continue
            if kind == "open":
                begin = pending_quote if pending_quote is not None else match.start()
                depth = 1
            elif kind in ("atom", "string"):
                first = pending_quote if pending_quote is not None else match.start()
                found.append((first, match.end()))
            pending_quote = None
            continue
        if kind == "open":
            depth += 1
        elif kind == "close":
            depth -= 1
            if depth == 0:
                found.append((begin, match.end()))
    return found


def top_spans(text: str) -> list[tuple[int, int]]:
    return nested_spans("(" + text + ")", 0, len(text) + 2)


def assertion_terms(text: str) -> list[str]:
    """The ground terms each top-level `assert-event' of a test book evaluates."""
    wrapped = "(" + text + ")"
    terms = []
    for a, b in nested_spans(wrapped, 0, len(wrapped)):
        form = wrapped[a:b]
        if not form.startswith("("):
            continue
        parts = nested_spans(wrapped, a, b)
        if not parts or wrapped[parts[0][0]:parts[0][1]].lower() != "assert-event":
            continue
        if len(parts) < 2:
            continue
        asserted = parts[1]
        body = wrapped[asserted[0]:asserted[1]]
        inner = nested_spans(wrapped, *asserted) if body.startswith("(") else []
        if inner and wrapped[inner[0][0]:inner[0][1]].lower() == "equal" and len(inner) == 3:
            terms.extend(wrapped[x:y] for x, y in inner[1:])
        else:
            terms.append(body)
    return terms


def driver(book: str, terms: list[str]) -> str:
    lines = [
        '(set-cbd "' + str(ROOT / "tests" / "acl2") + '/")',
        '(ld "' + book + '.lisp")',
        "(set-fmt-hard-right-margin 1000000 state)",
        "(set-fmt-soft-right-margin 1000000 state)",
    ]
    for index, term in enumerate(terms):
        lines.append(f'(cw "~%{MARK} {index} ~x0~%" {term})')
    lines.append(f'(cw "~%{MARK} END~%")')
    return "\n".join(lines) + "\n"


def install(book: str) -> None:
    import certs  # noqa: E402
    names = [name for name in certs.closure(ROOT, f"tests/acl2/{book}")
             if name != f"tests/acl2/{book}"]
    subprocess.run([sys.executable, str(ROOT / "tools" / "certs.py"), "install",
                    *names], capture_output=True, text=True, cwd=ROOT)


def evaluate(book: str, timeout: int) -> dict:
    source = (ROOT / "tests" / "acl2" / f"{book}.lisp").read_text(encoding="utf-8")
    terms = assertion_terms(source)
    install(book)
    run = subprocess.run([str(ROOT / "tools" / "acl2"), "--timeout", str(timeout)],
                         input=driver(book, terms), capture_output=True, text=True,
                         cwd=ROOT)
    values: dict[int, str] = {}
    ended = False
    for line in run.stdout.splitlines():
        match = re.match(rf"^{MARK} (\d+) (.*)$", line)
        if match:
            values[int(match.group(1))] = match.group(2).strip()
        elif line.strip() == f"{MARK} END":
            ended = True
    return {
        "book": f"tests/acl2/{book}",
        "complete": ended and len(values) == len(terms),
        "vectors": [{"term": " ".join(term.split()), "value": values.get(i)}
                    for i, term in enumerate(terms)],
    }


def record(args) -> int:
    report = {"schema": "fn-codec-golden-v1",
              "books": [evaluate(book, args.timeout) for book in args.books]}
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
    total = sum(len(b["vectors"]) for b in report["books"])
    missing = sum(1 for b in report["books"] for v in b["vectors"] if v["value"] is None)
    print(f"codec-golden: {total} ground terms over {len(report['books'])} test books, "
          f"{missing} unevaluated; wrote {out}")
    return 0 if missing == 0 else 1


def compare(args) -> int:
    before = json.loads(Path(args.before).read_text(encoding="utf-8"))
    after = json.loads(Path(args.after).read_text(encoding="utf-8"))
    later = {(b["book"], v["term"]): v["value"] for b in after["books"] for v in b["vectors"]}
    same = differ = 0
    for book in before["books"]:
        for vector in book["vectors"]:
            key = (book["book"], vector["term"])
            if vector["value"] is not None and later.get(key) == vector["value"]:
                same += 1
            else:
                differ += 1
                print(f"DIFFERS {book['book']}: {vector['term']}\n  before {vector['value']}"
                      f"\n  after  {later.get(key)}")
    print(f"codec-golden: {same} identical, {differ} different or unevaluated")
    return 0 if differ == 0 else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Golden-vector control of the codec seam.")
    sub = parser.add_subparsers(dest="command", required=True)
    rec = sub.add_parser("record")
    rec.add_argument("--out", required=True)
    rec.add_argument("--timeout", type=int, default=600)
    rec.add_argument("books", nargs="*", default=list(TEST_BOOKS))
    cmp_ = sub.add_parser("compare")
    cmp_.add_argument("before")
    cmp_.add_argument("after")
    args = parser.parse_args(argv)
    return record(args) if args.command == "record" else compare(args)


if __name__ == "__main__":
    raise SystemExit(main())

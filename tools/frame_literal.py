#!/usr/bin/env python3
"""Print a profile/config frame literal for a test book, computed by ACL2.

    python3 tools/frame_literal.py VALUE...                     # the store profile frame
    python3 tools/frame_literal.py --name '*spot-window-octets*' \\
        '*fn-bs-meta-format-8*' '*fn-bs-meta-frontier-format*' 4096 ... 16384
    python3 tools/frame_literal.py --python VALUE...            # a Python bytes literal
    python3 tools/frame_literal.py --form '(fn-frame-seal ...)' # any octet-list form
    python3 tools/frame_literal.py --host persvati VALUE...     # the session on a box

compression-extents-2's ask (2026-09-27): a `defconst` cannot evaluate an
attached function such as `fn-frame-digest` (the SHA-256 trailer runs
through its attachment), so a test book cannot compute a sealed frame and
writes it out octet for octet -- and every profile layout change re-seals
each such literal through a REPL round-trip and a paste.  This is that
round-trip as one command.

HOW.  It drives tools/proof_repl.py as a subprocess (never imported: the
session machinery is proof_repl's and lane-tools-1 owns it).  `start` opens a
session over BOOK (default tests/acl2/store-profile-open-tests) through its
leading `in-package`/`include-book` forms only -- the certified closure from
the cache, seconds -- then `send` evaluates

    (cw "FNLIT[~*0]FNLIT~%" (list "" "~x*" "~x* " "~x* " FORM))

where FORM is `(ENCODER (list VALUE...))` (ENCODER default
`fn-spo-saved-frame`, books/store-profile-open.lisp: the FNSM config frame of
a profile's fields) or `--form`.  The octets are read between the markers,
checked to be octets, and printed in the test books' layout (sixteen a line)
with the length assertion the books carry.  The session is stopped unless
`--session NAME` names one to reuse (then it is neither started nor stopped).

Each VALUE is one Lisp token or one balanced form (a constant such as
`*fn-bs-meta-format-8*`, a number, `(expt 2 32)`); a `#.` read-time
evaluation or an unbalanced form is refused before anything runs.  What it
prints is what ACL2 computed in a session over cached certificates; the
test book's own `(assert-event (equal (ENCODER ...) *LITERAL*))` is still
the check.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PROOF_REPL = ROOT / "tools" / "proof_repl.py"
DEFAULT_BOOK = "tests/acl2/store-profile-open-tests"
DEFAULT_ENCODER = "fn-spo-saved-frame"
MARK = re.compile(r"FNLIT\[(.*?)\]FNLIT", re.S)
PER_LINE = 16


class LiteralError(ValueError):
    pass


def check_value(text: str) -> str:
    """TEXT as one Lisp token or balanced form, or LiteralError."""
    stripped = text.strip()
    if not stripped:
        raise LiteralError("an empty VALUE")
    if "#." in stripped:
        raise LiteralError(f"{text!r}: read-time evaluation (#.) is refused")
    depth, in_string, escaped = 0, False, False
    for char in stripped:
        if in_string:
            escaped = (char == "\\" and not escaped)
            if char == '"' and not escaped:
                in_string = False
            continue
        if char == '"':
            in_string = True
        elif char == ";":
            raise LiteralError(f"{text!r}: a comment inside a VALUE")
        elif char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                raise LiteralError(f"{text!r}: unbalanced parentheses")
    if depth or in_string:
        raise LiteralError(f"{text!r}: unbalanced parentheses or string")
    if not stripped.startswith(("(", "'")) and re.search(r"\s", stripped):
        raise LiteralError(f"{text!r}: more than one token; quote it as one form")
    return stripped


def value_form(values: list[str], encoder: str = DEFAULT_ENCODER) -> str:
    if not re.fullmatch(r"[a-z0-9<>=/*+$-]+", encoder, re.I):
        raise LiteralError(f"{encoder!r}: not a function name")
    return f"({encoder} (list {' '.join(check_value(v) for v in values)}))"


def print_form(form: str) -> str:
    """The form `send' evaluates: FORM's octets between markers, space-separated."""
    return f'(cw "FNLIT[~*0]FNLIT~%" (list "" "~x*" "~x* " "~x* " {check_value(form)}))'


def parse_octets(output: str) -> list[int]:
    """The octets between the markers in ACL2's answer (fmt may wrap lines)."""
    found = MARK.findall(output)
    if not found:
        raise LiteralError("ACL2's answer has no FNLIT[...]FNLIT: the form did not "
                           "evaluate (the answer follows)\n" + output[-3000:])
    words = found[-1].split()
    octets = []
    for word in words:
        if not word.isdigit() or int(word) > 255:
            raise LiteralError(f"the form's value is not an octet list ({word!r} in it)")
        octets.append(int(word))
    return octets


def lisp_literal(octets: list[int], name: str | None = None) -> str:
    rows = [" ".join(str(o) for o in octets[i:i + PER_LINE])
            for i in range(0, len(octets), PER_LINE)]
    body = "  '(\n" + "\n".join("    " + row for row in rows) + ")"
    if name is None:
        return body.strip() if not rows else body
    return (f"(defconst {name}\n{body})\n\n"
            f"(assert-event (equal (len {name}) {len(octets)}))")


def python_literal(octets: list[int]) -> str:
    rows = [", ".join(str(o) for o in octets[i:i + PER_LINE])
            for i in range(0, len(octets), PER_LINE)]
    return "bytes([\n" + ",\n".join("    " + row for row in rows) + ",\n])  # " + \
        f"{len(octets)} octets"


def leading_forms(listing: str) -> str:
    """`#N` of the last of a book's leading in-package/include-book forms,
    from `proof_repl.py forms BOOK`."""
    last = None
    for line in listing.splitlines():
        match = re.match(r"#(\d+)\s+(\S+)", line.strip())
        if not match:
            continue
        if match.group(2) in ("in-package", "include-book"):
            last = match.group(1)
        else:
            break
    if last is None:
        raise LiteralError("the book has no leading include-book forms")
    return "#" + last


def repl(arguments: list[str], remote: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(PROOF_REPL), *arguments, *remote],
                          cwd=ROOT, capture_output=True, text=True)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("values", nargs="*", help="the encoder's field values, in order")
    parser.add_argument("--encoder", default=DEFAULT_ENCODER)
    parser.add_argument("--form", help="evaluate this octet-list form instead of ENCODER over VALUES")
    parser.add_argument("--book", default=DEFAULT_BOOK,
                        help="the book whose leading includes the session loads")
    parser.add_argument("--name", help="print a defconst NAME and its length assertion")
    parser.add_argument("--python", action="store_true", help="print a Python bytes literal")
    parser.add_argument("--session", help="reuse this live proof_repl session")
    parser.add_argument("--host", help="run the session on this box (proof_repl --host)")
    parser.add_argument("--remote-tree", help="proof_repl --remote-tree")
    arguments = parser.parse_args(argv)

    try:
        if arguments.form and arguments.values:
            raise LiteralError("give VALUEs or --form, not both")
        if not arguments.form and not arguments.values:
            raise LiteralError("no VALUEs and no --form")
        form = arguments.form or value_form(arguments.values, arguments.encoder)
        sent = print_form(form)
    except LiteralError as exc:
        print(f"frame_literal: {exc}", file=sys.stderr)
        return 2

    remote = []
    if arguments.host:
        remote += ["--host", arguments.host]
    if arguments.remote_tree:
        remote += ["--remote-tree", arguments.remote_tree]
    session = arguments.session or f"flit-{os.getpid()}"
    started = False
    try:
        if not arguments.session:
            listing = repl(["forms", arguments.book], remote)
            if listing.returncode != 0:
                print(f"frame_literal: proof_repl forms failed:\n{listing.stderr}{listing.stdout}",
                      file=sys.stderr)
                return 2
            through = leading_forms(listing.stdout)
            start = repl(["start", session, arguments.book, "--through", through,
                          "--idle-timeout", "10"], remote)
            if start.returncode != 0:
                print(f"frame_literal: proof_repl start failed:\n{start.stderr}{start.stdout}",
                      file=sys.stderr)
                return 2
            started = True
        answer = repl(["send", session, sent, "--full"], remote)
        octets = parse_octets(answer.stdout + answer.stderr)
    except LiteralError as exc:
        print(f"frame_literal: {exc}", file=sys.stderr)
        return 1
    finally:
        if started:
            repl(["stop", session], remote)
    print(python_literal(octets) if arguments.python else lisp_literal(octets, arguments.name))
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""The host side of the FN-Statement carrier.

Nothing here computes what ACL2 computes.  `books/stx-carrier.lisp` owns the
detached encoding, the base64 layer, the field value, the payload projection
and the bounds; `books/stx-verify.lisp` owns the verdict and its rendering.
This module starts an ACL2 session over those books, marshals octets in and
out of it, and prints what the session decided.  There is no second encoder
in Python, and no path here turns an exception into a verdict.

The crypto seam is constrained (`books/crypto-seam.lisp`): a digest and a
signature scheme with shape constraints and one correctness property, and no
deployed realiser.  So the session attaches the TOY realisers of
`tests/acl2/crypto-seam-tests.lisp` -- a polynomial mix digest and a
sign-by-public-key scheme, neither cryptographic -- and every verdict this
tool prints is a statement about the codec and the composition, never about
unforgeability.  `tools/crypto_host.py` is the host's one Ed25519 entry point
and is used by `sign --ed25519` to produce a real signature over the signing
preimage ACL2 computed, for the deployed profile; wiring that signature back
into an ACL2 verdict needs a digest realiser ACL2 can execute, which is D09's
open question (specs/substrate-transport.md, "What this design does not
decide").  Until it is answered, `verify` under the deployed profile is the
recipient's own business and this tool reports the toy-realiser verdict only,
saying so on every line.

Exit codes keep the three outcomes distinct (D13):
    0  verified
    3  unverified
    4  absent
    2  the tool could not reach a verdict at all (never an outcome)
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from tools.run_store import (  # noqa: E402
    PROMPT, StoreError, acl2_result, decimal_list, read_prompt,
)

EXIT_VERIFIED = 0
EXIT_UNVERIFIED = 3
EXIT_ABSENT = 4
EXIT_NO_VERDICT = 2

_BOOKS = (
    '(include-book "tests/acl2/crypto-seam-tests")',
    '(include-book "books/stx-invariants")',
)


class StxSession:
    """An ACL2 session over the stx books, with the toy realisers attached."""

    def __init__(self):
        env = os.environ.copy()
        env["ACL2_CUSTOMIZATION"] = "NONE"
        env["ACL2_BOOK_HASH_ALISTP"] = "NIL"
        self.proc = subprocess.Popen(
            [env.get("FN_ACL2", "acl2")], cwd=ROOT, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
        read_prompt(self.proc, 300.0)
        for form in _BOOKS:
            self.call(form, timeout=600.0)

    def call(self, form: str, timeout: float = 120.0) -> bytes:
        self.proc.stdin.write((form + "\n").encode("ascii"))
        self.proc.stdin.flush()
        output = read_prompt(self.proc, timeout)
        upper = output.upper()
        if b"ACL2 ERROR" in upper or b"HARD ACL2 ERROR" in upper:
            raise StoreError(output.decode("utf-8", "replace"))
        return output

    def octets(self, form: str) -> bytes:
        body = acl2_result(self.call(form))
        if body == b"NIL":
            return b""
        values = decimal_list(body)
        if values is None or any(value > 255 for value in values):
            raise StoreError("ACL2 returned a non-octet result: {!r}".format(body))
        return bytes(values)

    def keyword(self, form: str) -> str:
        body = acl2_result(self.call(form)).decode("ascii", "replace").strip()
        return body.upper().lstrip(":")

    def close(self):
        if self.proc is not None:
            try:
                self.proc.stdin.close()
            except OSError:
                pass
            self.proc.wait(timeout=30)
            self.proc = None


def octet_form(data: bytes) -> str:
    return "(quote (" + " ".join(str(b) for b in data) + "))"


def seed_form(seed: bytes) -> str:
    if len(seed) != 32:
        raise SystemExit("a seed is 32 octets (books/crypto-seam.lisp)")
    return octet_form(seed)


def sign(args) -> int:
    payload = open(args.payload, "rb").read()
    seed = bytes.fromhex(open(args.seed).read().strip())
    session = StxSession()
    try:
        public = session.octets(
            "(fn-sig-public-key {})".format(seed_form(seed)))
        creator = session.octets(
            "(fn-prin-id {} {})".format(octet_form(public), octet_form(args.token.encode())))
        statement = "(fn-stmt-sign {} {} {} {} nil {} {})".format(
            seed_form(seed), octet_form(creator), args.incarnation, args.sequence,
            ":" + args.kind, octet_form(payload))
        value = session.octets("(fn-stx-header-value {})".format(statement))
        if not value:
            raise SystemExit("ACL2 refused the statement: no field value")
        preimage = session.octets(
            "(fn-stmt-signing-preimage (fn-stmt-header {}))".format(statement))
    finally:
        session.close()
    sys.stdout.write("FN-Statement: " + value.decode("ascii") + "\r\n")
    sys.stderr.write("creator {}\n".format(creator.hex()))
    if args.ed25519:
        from tools import crypto_host
        signature = crypto_host.sign(seed, preimage)
        sys.stderr.write("ed25519 signature over the ACL2 signing preimage: {}\n"
                         .format(signature.hex()))
        sys.stderr.write("not attached: the deployed digest realiser is open (D09)\n")
    return 0


def attach(args) -> int:
    field = open(args.field, "rb").read().rstrip(b"\r\n")
    article = open(args.article, "rb").read()
    sys.stdout.buffer.write(field + b"\r\n" + article)
    return 0


def verify(args) -> int:
    received = open(args.article, "rb").read()
    keyring = "nil"
    if args.keyring:
        entries = []
        for line in open(args.keyring):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            ident, key = line.split()
            entries.append("(cons {} {})".format(
                octet_form(bytes.fromhex(ident)), octet_form(bytes.fromhex(key))))
        keyring = "(list " + " ".join(entries) + ")" if entries else "nil"
    session = StxSession()
    try:
        article = ("(fn-article-result-article (fn-article-parse {}))"
                   .format(octet_form(received)))
        parsed = session.keyword("(if (fn-article-syntax-p {}) :ok :unparsable)"
                                 .format(article))
        if parsed != "OK":
            sys.stderr.write("the article does not parse; no verdict\n")
            return EXIT_NO_VERDICT
        verdict = "(fn-stx-verdict {} {} {})".format(article, keyring, args.generation)
        token = session.keyword("(fn-stx-verdict-token {})".format(verdict))
        item = session.octets("(fn-stx-verified-item {})".format(verdict))
    finally:
        session.close()
    sys.stdout.write(item.decode("ascii") + "\n")
    sys.stdout.write("(toy crypto realiser; not a cryptographic verdict)\n")
    return {"VERIFIED": EXIT_VERIFIED,
            "UNVERIFIED": EXIT_UNVERIFIED,
            "ABSENT": EXIT_ABSENT}.get(token, EXIT_NO_VERDICT)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("sign", help="sign a statement and print its FN-Statement field")
    p.add_argument("--seed", required=True, help="file holding a 32-octet hex seed")
    p.add_argument("--payload", required=True, help="file holding the authored source bytes")
    p.add_argument("--token", default="fn", help="the principal's token")
    p.add_argument("--kind", default="article",
                   choices=("article", "policy", "receipt", "succession"))
    p.add_argument("--incarnation", type=int, default=1)
    p.add_argument("--sequence", type=int, default=1)
    p.add_argument("--ed25519", action="store_true",
                   help="also print a real Ed25519 signature over the signing preimage")
    p.set_defaults(func=sign)

    p = sub.add_parser("attach", help="prepend a field line to an article")
    p.add_argument("--field", required=True)
    p.add_argument("--article", required=True)
    p.set_defaults(func=attach)

    p = sub.add_parser("verify", help="print the node's verdict on an article")
    p.add_argument("--article", required=True)
    p.add_argument("--keyring", help="lines of '<creator-hex> <public-key-hex>'")
    p.add_argument("--generation", type=int, default=0)
    p.set_defaults(func=verify)

    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except StoreError as error:
        sys.stderr.write("ACL2 session failed: {}\n".format(error))
        return EXIT_NO_VERDICT


if __name__ == "__main__":
    raise SystemExit(main())

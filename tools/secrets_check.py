#!/usr/bin/env python3
"""No live credential in the public tree's prose, records or fixtures.

The repository is public.  On 2026-09-27 two lane records nearly committed a
live peering invitation code (caught before the push; batch AY's obstruction
report); `bb439b155` had to redact one after the fact.  Nothing looked.

This refuses, by file:line, a SECRET-SHAPED value within WINDOW lines of a
CONTEXT word, in every tracked file under planning/, docs/ and tests/
(`git ls-files`; without .git, a walk of those directories):

  context   redeem, XREDEEM, invite, invitation, credential(s)
            (case-insensitive, as a word or a word's stem: `invites`,
            `invitation-code`, `REDEEM`)
  secret    a standalone 32-hex-digit token (an invitation code's shape: no
            hex digit or word character on either side, so a 64-hex digest
            or a hex run inside a longer word is not one);
            `password=VALUE` / `password: VALUE` / `passwd` / `secret=VALUE`;
            `Bearer TOKEN` (16+ token characters);
            `Authorization: VALUE`.

WINDOW is 5 lines.  An invitation is quoted on its own command line
(`XREDEEM <code>`), or in a transcript or a record one to three lines from the
word that names it ("the invitation:" then a blank line and a fenced code
line); five covers a fenced block's opening, the blank line and a heading.
Wider windows reach the 32-hex digests of evidence manifests that merely sit
near a sentence about credentials (measured on 699802ba5: 5 lines, 0 hits on
the sanitized tree; 12 lines, dozens of manifest digests).

No waiver list.  A value that is not a secret passes by one RULE, stated
here and applied mechanically:

  synthetic  a 32-hex token with at most four distinct hex digits
             (`00000000...`, `0123...0123`; write new test vectors as
             `11111111...` or `0f0f...`), or the counting vector (at least
             12 of its 16 bytes are the byte before plus one,
             `000102...0e0f`), or a line
             that carries the marker `FAKE-SECRET` (upper case, hyphenated:
             a test that needs a realistic-looking value says so on its line);
  placeholder a password/Bearer/Authorization value that is a placeholder:
             starts with `<`, `$`, `{`, `%`, `*`, `...`/`…`, or is one of
             `x`-runs, `REDACTED`, `redacted`, `changeme`, `example`,
             `secret`, `password` (the word itself), or empty.
  evidence   a 32-hex token inside a path under `planning/evidence/`
             (`planning/evidence/repair/S107-<uuid4 hex>.json`: the repair
             tool's archive names, which sit beside a ledger item's title
             and so beside its words); a credential is a value, never a
             component of a filed evidence path.

A real secret found here is REDACTED in the source and ROTATED (a redacted
invitation must still be revoked: the history keeps the old bytes).  The
report prints only the first four characters and the length of a value.

    python3 tools/secrets_check.py [--window N] [FILE ...]

Exit 0 clean, 1 with each finding named.  Static, no ACL2, about a second.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DIRECTORIES = ("planning", "docs", "tests")
WINDOW = 5

# A context word is prose or a command word, not part of an identifier or a
# path: `books/native-auth-credentials.lisp' and `invitation-for-friend' are
# names, and next to them sit the certificate digests of a manifest.
CONTEXT = re.compile(r"(?i)(?<![A-Za-z0-9_/.-])(?:x?redeem|invit(?:e|es|ed|ing|ation)"
                     r"|credentials?)(?![A-Za-z0-9_]|[-_/.][A-Za-z0-9])")
HEX32 = re.compile(r"(?<![0-9A-Za-z_])([0-9a-fA-F]{32})(?![0-9A-Za-z_])")
# `password=VALUE' and a quoted `"password": "VALUE"'; an unquoted
# `Password: ...' is a prompt in a transcript (`Password: Confirm password:'),
# never a value.
PASSWORD = re.compile(r"(?i)\b(?:password|passwd|secret)\s*=\s*\\?[\"']?([^\s\"',;)\\]*)"
                      r"|\b(?:password|passwd|secret)[\"']?\s*:\s*[\"']([^\"']*)[\"']")
BEARER = re.compile(r"(?i)\bbearer\s+([A-Za-z0-9._~+/-]{16,}=*)")
AUTHORIZATION = re.compile(r"(?i)\bauthorization\s*:\s*([^\s\"',;)]+(?:\s+[^\s\"',;)]+)?)")
# The evidence rule: a path under planning/evidence/, up to the first
# character no path component carries (whitespace, a quote, a bracket).
EVIDENCE_PATH = re.compile(r"planning/evidence/[^\s\"'`()<>\[\]{},;]*")
MARKER = "FAKE-SECRET"
PLACEHOLDER_WORDS = {"redacted", "changeme", "example", "secret", "password", "none",
                     "null", "nil", "true", "false"}


def synthetic_hex(token: str) -> bool:
    """At most four distinct hex digits, or the counting vector: at least 12
    of its 16 bytes are the byte before plus one (`000102...0e0f')."""
    token = token.lower()
    if len(set(token)) <= 4:
        return True
    octets = [int(token[i:i + 2], 16) for i in range(0, 32, 2)]
    return sum(1 for a, b in zip(octets, octets[1:]) if b == a + 1) >= 12


def placeholder(value: str) -> bool:
    value = value.strip()
    if not value:
        return True
    if value[0] in "<${%*[(" or value.startswith(("...", "…")):
        return True
    if "(" in value or "%s" in value or "{}" in value:
        return True  # an expression or a format template, not a literal
    lowered = value.lower().rstrip(".")
    if lowered in PLACEHOLDER_WORDS or set(lowered) <= {"x"}:
        return True
    # `Authorization: Bearer <token>' and `Authorization: Basic $X'
    words = value.split()
    return len(words) == 2 and placeholder(words[1])


def redact(value: str) -> str:
    return f"{value[:4]}... ({len(value)} chars)"


def findings_in(text: str, window: int = WINDOW) -> list[tuple[int, str]]:
    """(line, description) for each secret-shaped value near a context word."""
    lines = text.split("\n")
    near = [False] * len(lines)
    for number, line in enumerate(lines):
        if CONTEXT.search(line):
            for other in range(max(0, number - window), min(len(lines), number + window + 1)):
                near[other] = True
    found: list[tuple[int, str]] = []
    for number, line in enumerate(lines):
        if not near[number] or MARKER in line:
            continue
        evidence = [span.span() for span in EVIDENCE_PATH.finditer(line)]
        for match in HEX32.finditer(line):
            if any(start <= match.start() and match.end() <= end for start, end in evidence):
                continue
            if not synthetic_hex(match.group(1)):
                found.append((number + 1, "a 32-hex token " + redact(match.group(1))))
        for pattern, kind in ((PASSWORD, "a password/secret value"),
                              (BEARER, "a bearer token"),
                              (AUTHORIZATION, "an Authorization header value")):
            for match in pattern.finditer(line):
                value = next((g for g in match.groups() if g is not None), "")
                if not placeholder(value):
                    found.append((number + 1, f"{kind} " + redact(value)))
    return found


def tracked_files(root: Path = ROOT) -> list[Path]:
    if (root / ".git").exists():
        result = subprocess.run(["git", "-C", str(root), "ls-files", "-z", "--", *DIRECTORIES],
                                capture_output=True, check=False)
        if result.returncode == 0:
            return [root / name for name in result.stdout.decode().split("\0") if name]
    found = []
    for directory in DIRECTORIES:
        for base, _, names in os.walk(root / directory):
            found.extend(Path(base) / name for name in names)
    return sorted(found)


def check(files: list[Path], root: Path = ROOT, window: int = WINDOW) -> list[str]:
    refused = []
    for path in files:
        try:
            text = path.read_bytes().decode("utf-8")
        except (OSError, UnicodeDecodeError):
            continue  # binary fixtures carry no prose
        try:
            rel = path.resolve().relative_to(root.resolve()).as_posix()
        except ValueError:
            rel = path.as_posix()
        for line, what in findings_in(text, window):
            refused.append(f"{rel}:{line}: {what} within {window} lines of "
                           "redeem/invite/invitation/credentials")
    return refused


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("files", nargs="*", type=Path)
    parser.add_argument("--window", type=int, default=WINDOW)
    arguments = parser.parse_args(argv)
    files = [p if p.is_absolute() else ROOT / p for p in arguments.files] or tracked_files()
    refused = check(files, ROOT, arguments.window)
    for line in refused:
        print(f"FAIL {line}")
    print(f"secrets_check: {len(files)} file(s), {len(refused)} secret-shaped value(s) "
          "near an invitation or credential word"
          + ("; redact AND rotate each (tools/secrets_check.py header)" if refused else ""))
    return 1 if refused else 0


if __name__ == "__main__":
    sys.exit(main())

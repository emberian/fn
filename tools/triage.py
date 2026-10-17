"""The error blocks of an ACL2 certification log.

``acl2_errors(text)`` is every ``ACL2 Error`` block of a book's log,
``key_checkpoint`` the checkpoint lines a block names, with the patterns
``ERROR_START``, ``CHECKPOINT_START`` and ``NO_CERTIFICATE``;
tools/certify_triage.py reads a certify run's logs through them.  The
provisional-certification triage driver that lived here (waves over a box,
substitution rounds, its report) left on cut/breaking (M1-d, 2026-10-17).
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass, field
import datetime as dt
import hashlib
import json
from pathlib import Path
import re
import secrets
import subprocess
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs  # noqa: E402
import farm  # noqa: E402
import green_check  # noqa: E402
# ACL2 wraps its error text at about 70 columns, so "There is no certificate
# on file" arrives with a newline anywhere inside it and a phrase match has to
# be made on whitespace-collapsed text.
NO_CERTIFICATE = "There is no certificate on file"
# `\b` after the optional `[Failure]` would backtrack past it -- `]` and the
# space that follows are both non-word -- and the report would then print
# every error as a plain `ACL2 Error`.
ERROR_START = re.compile(
    r"^(?:ACL2 Error(?: \[[^\]]*\])?|HARD ACL2 ERROR)(?=[ :]|$)")
CHECKPOINT_START = re.compile(r"^\*\*\* Key checkpoint.*\*\*\*$")
MISSING_FOR = re.compile(NO_CERTIFICATE + r' for "([^"]+)"')
# The Complete wave says it differently: it is not that the book is
# uncertified, it is that the certificate is not there yet.  Found on the
# real run of 2026-09-22; a classifier that knew only the include-book
# sentence read every blocked book as having no reason at all.
NOT_YET_CERTIFIED = "does not have a .cert file that is at least as recent"
BLOCKED_ON = re.compile(NOT_YET_CERTIFIED + r' as that included book: "([^"]+)"')
CHECKPOINT_LINES = 24
def collapse(text: str) -> str:
    """`text` with every run of whitespace as one space, for phrase matching."""
    return " ".join(text.split())


def repository_book(path: str) -> str:
    """The repository-relative book name inside an absolute path ACL2 printed.

    ACL2 names the uncertified dependency by the absolute path it has on the
    box, which is the remote root, not this worktree.  The repository part is
    what a reader here can act on.
    """
    text = path[:-len(".lisp")] if path.endswith(".lisp") else path
    for directory in certs.BOOK_DIRECTORIES:
        marker = f"/{directory}/"
        at = text.rfind(marker)
        if at >= 0:
            return text[at + 1:]
    return Path(text).name


@dataclass
class AclError:
    """One `ACL2 Error` block in a book's log, as the report needs it."""

    line: int
    head: str
    form: str
    message: str
    cascade_of: str | None = None
    wrapper: bool = False
    restatement: bool = False

    @property
    def news(self) -> bool:
        """Is this block the book's own first word about its own failure?"""
        return (self.cascade_of is None and not self.wrapper
                and not self.restatement)

    def text(self) -> str:
        where = f" in ({self.form})" if self.form else ""
        return collapse(f"{self.head}{where}: {self.message}")


def acl2_errors(log: str) -> list[AclError]:
    """Every error block in `log`, in order, each classified by its own text.

    ACL2 prints an error as a run of non-blank lines starting with `ACL2
    Error`, wrapped at the pretty-printer margin, so both the form and the
    message can be split across lines.  Four kinds appear in a failed
    certification and only one of them is news: the certify-book wrapper at
    the end, which restates the failure; an include-book of a book with no
    certificate, which is a cascade; ACL2's own `[Failure] ... See :DOC
    failure` restatement of a form it has already complained about, which
    carries none of the reason and which made every cascade here look like
    an independent red until it was given a name; and the book's own error.
    """
    lines = log.splitlines()
    found: list[AclError] = []
    by_form: dict[str, AclError] = {}
    index = 0
    while index < len(lines):
        if not ERROR_START.match(lines[index]):
            index += 1
            continue
        start = index
        block: list[str] = []
        while index < len(lines) and lines[index].strip():
            block.append(lines[index])
            index += 1
        whole = collapse(" ".join(block))
        form = ""
        parenthesised = re.search(r"\(\s*([^()]*?)\s*\)", whole)
        if parenthesised:
            form = parenthesised.group(1)
        _, separator, rest = whole.partition("): ")
        if not separator:
            _, separator, rest = whole.partition(": ")
        message = rest.strip() if separator else whole
        cascade_of = None
        if NOT_YET_CERTIFIED in whole:
            named = BLOCKED_ON.search(whole)
            cascade_of = (repository_book(named.group(1)) if named
                          else "an unnamed book")
        elif NO_CERTIFICATE in whole:
            named = MISSING_FOR.search(whole)
            cascade_of = (repository_book(named.group(1)) if named
                          else repository_book(form.split('"')[1])
                          if '"' in form else "an unnamed book")
        earlier = by_form.get(form) if form else None
        error = AclError(
            line=start + 1, head=ERROR_START.match(lines[start]).group(0),
            form=form, message=message,
            cascade_of=cascade_of or (earlier.cascade_of if earlier else None),
            wrapper=form.upper().startswith("CERTIFY-BOOK"),
            restatement=earlier is not None)
        if form and earlier is None:
            by_form[form] = error
        found.append(error)
    return found


def key_checkpoint(log: str, limit: int = CHECKPOINT_LINES) -> str | None:
    """ACL2's last key checkpoint, the goal it could not prove, truncated.

    The checkpoint is the one part of a failed proof a reader can act on
    without the log, so the report carries it; it is also unbounded, so it is
    cut at `limit` lines with the cut declared.
    """
    lines = log.splitlines()
    starts = [number for number, line in enumerate(lines)
              if CHECKPOINT_START.match(line.strip())]
    if not starts:
        return None
    start = starts[-1]
    body: list[str] = []
    for line in lines[start + 1:]:
        if ERROR_START.match(line) or line.startswith(("Summary", "********")):
            break
        body.append(line)
    while body and not body[0].strip():
        body.pop(0)
    while body and not body[-1].strip():
        body.pop()
    shown = body[:limit]
    if len(body) > limit:
        shown.append(f"... ({len(body) - limit} more lines, in the run log "
                     f"on the box)")
    return "\n".join([lines[start].strip()] + shown)



#!/usr/bin/env python3
"""fn's guides as Usenet articles: read, check and serialize docs/articles/*.txt.

Each file is one article as it is posted: RFC 5536 header lines, an empty
line, a plain-text body.  The site (site/build_site.py) renders them as a
newsreader, tools/post_docs.py posts them to a node, and tools/docs_check.py
checks their indented command lines.  This module is the one reader of the
format, so the three agree on it.

The rules `check` enforces (make check runs them through site/build_site.py):

  * From, Newsgroups, Subject, Date, Message-ID, Archive-name,
    Posting-Frequency, Last-modified and Summary are present, once each;
    Newsgroups is fn.announce or fn.docs.
  * The Message-ID is `<STEM-YYYYMMDD@fn.fg-goose.online>`, STEM the file's
    name and YYYYMMDD its Last-modified: a revised article is a new
    Message-ID, which a node supersedes the old one with.  Date is that day.
  * References name articles in this set (a follow-up's thread).
  * Header lines are ASCII (fn refuses anything else in a header).  The
    body is ASCII too, except in an article that declares
    `Content-Type: text/plain; charset=UTF-8`.
  * No body line is wider than 72 columns, and none ends in a space.

    python3 tools/docs_articles.py            # list the articles; exit 1 on a problem
"""

from __future__ import annotations

import email.utils
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ARTICLES = ROOT / "docs" / "articles"
DOMAIN = "fn.fg-goose.online"
GROUPS = ("fn.announce", "fn.docs")
REQUIRED = ("From", "Newsgroups", "Subject", "Date", "Message-ID", "Archive-name",
            "Posting-Frequency", "Last-modified", "Summary")
WIDTH = 72


@dataclass
class Article:
    path: Path
    headers: list[tuple[str, str]]
    body: str
    errors: list[str] = field(default_factory=list)

    def get(self, name: str, default: str = "") -> str:
        for key, value in self.headers:
            if key.lower() == name.lower():
                return value
        return default

    @property
    def stem(self) -> str:
        return self.path.stem

    @property
    def message_id(self) -> str:
        return self.get("Message-ID")

    @property
    def group(self) -> str:
        return self.get("Newsgroups")

    @property
    def references(self) -> list[str]:
        return self.get("References").split()

    @property
    def lines(self) -> int:
        return len(self.body.splitlines())

    def date(self):
        return email.utils.parsedate_to_datetime(self.get("Date"))

    def wire(self, extra: list[tuple[str, str]] = ()) -> bytes:
        """The article as POST sends it: CRLF lines, dot-stuffed, without
        the terminating dot line."""
        head = [f"{k}: {v}" for k, v in self.headers] + [f"{k}: {v}" for k, v in extra]
        lines = head + [""] + self.body.rstrip("\n").split("\n")
        return "".join(("." + line if line.startswith(".") else line) + "\r\n"
                       for line in lines).encode("utf-8")


def display(path: Path) -> str:
    path = path.resolve()
    return path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else str(path)


def parse(path: Path) -> Article:
    text = path.read_text(encoding="utf-8")
    head, sep, body = text.partition("\n\n")
    article = Article(path=path, headers=[], body=body)
    rel = display(path)
    if not sep:
        article.errors.append(f"{rel}: no empty line after the header")
    for line in head.split("\n"):
        if line[:1] in (" ", "\t") and article.headers:
            key, value = article.headers[-1]
            article.headers[-1] = (key, value + " " + line.strip())
            continue
        key, colon, value = line.partition(":")
        if not colon or not re.fullmatch(r"[A-Za-z][A-Za-z0-9-]*", key):
            article.errors.append(f"{rel}: not a header line: {line!r}")
            continue
        article.headers.append((key, value.strip()))
    return article


def check_one(article: Article, ids: set[str]) -> list[str]:
    errors = list(article.errors)
    rel = display(article.path)
    names = [k.lower() for k, _ in article.headers]
    for name in REQUIRED:
        count = names.count(name.lower())
        if count != 1:
            errors.append(f"{rel}: {name} appears {count} times (once is required)")
    for key, value in article.headers:
        if not (key + value).isascii():
            errors.append(f"{rel}: header {key} is not ASCII (fn refuses it)")
    if article.group not in GROUPS:
        errors.append(f"{rel}: Newsgroups is {article.group!r}, not one of {', '.join(GROUPS)}")
    modified = article.get("Last-modified")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", modified):
        errors.append(f"{rel}: Last-modified {modified!r} is not YYYY-MM-DD")
    want = f"<{article.stem}-{modified.replace('-', '')}@{DOMAIN}>"
    if article.message_id != want:
        errors.append(f"{rel}: Message-ID {article.message_id!r} should be {want} "
                      "(the file's name and its Last-modified)")
    try:
        if article.date().date().isoformat() != modified:
            errors.append(f"{rel}: Date is not the Last-modified day {modified}")
    except (TypeError, ValueError):
        errors.append(f"{rel}: Date {article.get('Date')!r} does not parse (RFC 5322)")
    for ref in article.references:
        if ref not in ids:
            errors.append(f"{rel}: References names {ref}, which no article here has")
    utf8 = "charset=utf-8" in article.get("Content-Type").lower().replace(" ", "")
    for number, line in enumerate(article.body.split("\n"), 1):
        where = f"{rel}: body line {number}"
        if not line.isascii() and not utf8:
            errors.append(f"{where} is not ASCII and the article declares no charset")
        if len(line) > WIDTH:
            errors.append(f"{where} is {len(line)} columns (at most {WIDTH})")
        if line != line.rstrip():
            errors.append(f"{where} ends in whitespace")
    if not article.body.endswith("\n") or article.body.endswith("\n\n"):
        errors.append(f"{rel}: the body must end with exactly one newline")
    return errors


def natural(text: str) -> list:
    return [int(part) if part.isdigit() else part for part in re.split(r"(\d+)", text)]


def load(directory: Path = ARTICLES) -> list[Article]:
    """Every article, in posting order: by Date, then by Archive-name."""
    articles = [parse(path) for path in directory.glob("*.txt")]

    def key(article):
        try:
            when = article.date().timestamp()
        except (TypeError, ValueError):
            when = 0
        return (when, natural(article.get("Archive-name")))
    return sorted(articles, key=key)


def check(articles: list[Article]) -> list[str]:
    ids = [a.message_id for a in articles]
    errors = [f"Message-ID {mid} is used twice" for mid in set(ids) if ids.count(mid) > 1]
    for article in articles:
        errors += check_one(article, set(ids))
    return errors


def main() -> int:
    articles = load()
    for article in articles:
        print(f"{article.group:12} {article.lines:4d} {article.message_id}  {article.get('Subject')}")
    errors = check(articles)
    for error in errors:
        print("FAIL " + error)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Post fn's guides (docs/articles/*.txt) to a node's fn.announce and fn.docs.

Idempotent, by Message-ID.  For each article, in posting order (Date, then
Archive-name, so a follow-up comes after what it follows):

    present      the node answers STAT with 223: nothing is sent.
    posted       it was absent and the node answered POST with 240.
    superseded   as posted, with `Supersedes: <OLD>`: the group holds an
                 older version of the same article (the same file stem,
                 an earlier Last-modified in its Message-ID), so the new one
                 replaces it.  The node decides whether the supersede
                 withdraws the old one (its poster's Cancel-Lock, RFC 8315);
                 this tool reports the node's answer and never cancels.
    refused      the node's 4xx line, printed as it came.
    uncertain    the POST's text went out and no final answer came back, or
                 the node answered that the outcome is uncertain.  Run the
                 same command again: it re-sends the same article under the
                 same Message-ID, which settles it (D25).

Exit 0 when every article is present or posted, 1 when one was refused, 3
when one is uncertain (AGENTS.md: the three stay distinct).  The login
happens only inside TLS: implicit TLS (--tls, port 563) or STARTTLS.

Credentials come from FN_CLIENT_USER and FN_CLIENT_PASSWORD, or from
--credentials PATH (mode 0600, `user password`), never from argv.

    python3 tools/post_docs.py --node fn.fg-goose.online:563 --tls \\
        --credentials /root/fn-docs.credentials
    python3 tools/post_docs.py --node 127.0.0.1:21119 --cafile cert.pem --dry-run
"""

from __future__ import annotations

import argparse
import re
import socket
import ssl
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import docs_articles                                   # noqa: E402
from fn_client import credentials, split_node          # noqa: E402
from nntp_session import Disconnected, Session         # noqa: E402

EXIT = {"present": 0, "posted": 0, "superseded": 0, "planned": 0, "refused": 1, "uncertain": 3}
ALREADY_STORED = "441 posting failed; this article is already stored here"


class ImplicitSession(Session):
    """A Session whose TLS starts with the first octet (port 563)."""

    def __init__(self, host: str, port: int, timeout: float, context: ssl.SSLContext):
        self.host, self.port = host, port
        raw = socket.create_connection((host, port), timeout=timeout)
        try:
            self.sock = context.wrap_socket(raw, server_hostname=host)
        except BaseException:
            raw.close()
            raise
        self.sock.settimeout(timeout)
        self.buf = b""
        self.broken = False
        self.tls = {"version": self.sock.version(), "cipher": self.sock.cipher()[0]}
        try:
            self.greeting = self.line()
        except BaseException:
            self.sock.close()
            raise


class Uncertain(Exception):
    pass


def connect(args, user: str, password: str) -> Session:
    context = ssl.create_default_context(cafile=args.cafile)
    if args.tls:
        session = ImplicitSession(args.host, args.port, args.timeout, context)
    else:
        session = Session(args.host, args.port, args.timeout)
        status = session.starttls(context)
        if not status.startswith("382"):
            session.close()
            raise SystemExit("post_docs: the node answered %s to STARTTLS; no login sent" % status)
    print("connected %s:%d %s %s" % (args.host, args.port, session.tls["version"],
                                     session.greeting))
    status = session.login(user, password)
    if not status.startswith("281"):
        session.close()
        print("refused login: %s" % status)
        raise SystemExit(1)
    return session


def visible(session: Session, group: str) -> list[str]:
    """The Message-IDs the node shows this login in GROUP (OVER's field 4)."""
    status = session.cmd("GROUP " + group)[0]
    if not status.startswith("211"):
        return []
    fields = status.split()
    if int(fields[1]) == 0:
        return []
    status, lines = session.cmd("OVER %s-%s" % (fields[2], fields[3]), multiline=True)
    if not status.startswith("224"):
        return []
    return [line.split("\t")[4] for line in lines if line.count("\t") >= 4]


def older_version(article: docs_articles.Article, ids: list[str]) -> str | None:
    """The newest visible Message-ID of an earlier version of ARTICLE."""
    mine = re.fullmatch(r"<(.+)-(\d{8})@(.+)>", article.message_id)
    if not mine:
        return None
    stem, date, domain = mine.groups()
    older = []
    for mid in ids:
        m = re.fullmatch(r"<(.+)-(\d{8})@(.+)>", mid)
        if m and m.group(1) == stem and m.group(3) == domain and m.group(2) < date:
            older.append((m.group(2), mid))
    return max(older)[1] if older else None


def post(session: Session, article, extra) -> tuple[str, str]:
    status = session.cmd("POST")[0]
    if not status.startswith("340"):
        return "refused", status
    try:
        session.sock.sendall(article.wire(extra) + b".\r\n")
        status = session.line()
    except (OSError, Disconnected) as exc:
        raise Uncertain("%s: the POST's text went out and no answer came back (%s); "
                        "run again to settle it" % (article.message_id, exc))
    if status.startswith("240"):
        return "posted", status
    if status.startswith(ALREADY_STORED):
        return "present", status
    if status.startswith("441") and "uncertain" in status.lower():
        raise Uncertain("%s: %s" % (article.message_id, status))
    return "refused", status


def run(args, session: Session, articles) -> int:
    worst = 0
    listed: dict[str, list[str]] = {}
    for article in articles:
        mid = article.message_id
        status = session.cmd("STAT " + mid)[0]
        if status.startswith("223"):
            outcome, detail = "present", status
        else:
            group = article.group
            if group not in listed:
                listed[group] = visible(session, group)
            old = older_version(article, listed[group])
            extra = [("Supersedes", old)] if old else []
            if args.dry_run:
                outcome, detail = "planned", "absent (%s)%s" % (
                    status, "; would supersede " + old if old else "")
            else:
                try:
                    outcome, detail = post(session, article, extra)
                except Uncertain as exc:
                    print("uncertain %s %s" % (article.group, exc))
                    return 3
                if outcome == "posted" and old:
                    outcome, detail = "superseded", "%s (Supersedes: %s)" % (detail, old)
        print("%s %s %s %s" % (outcome, article.group, mid, detail))
        worst = max(worst, EXIT[outcome])
    return worst


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--node", required=True, help="HOST:PORT")
    parser.add_argument("--tls", action="store_true",
                        help="TLS from the first octet (port 563); otherwise STARTTLS")
    parser.add_argument("--cafile", help="the node's certificate, or its CA "
                                         "(default: the system's)")
    parser.add_argument("--credentials", help="a mode-0600 file holding `user password`")
    parser.add_argument("--articles", default=str(docs_articles.ARTICLES),
                        help="the articles' directory (default docs/articles)")
    parser.add_argument("--dry-run", action="store_true",
                        help="log in and say what would be posted; post nothing")
    parser.add_argument("--timeout", type=float, default=30.0)
    return parser


def main(argv=None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    host, port = split_node(args.node)
    if host is None or not str(port).isdigit():
        parser.error("--node %s: want HOST:PORT" % args.node)
    args.host, args.port = host, int(port)
    articles = docs_articles.load(Path(args.articles))
    errors = docs_articles.check(articles)
    if errors:
        for error in errors:
            print("FAIL " + error)
        return 2
    user, password = credentials(args, parser)
    if not user or not password:
        parser.error("no login: set FN_CLIENT_USER and FN_CLIENT_PASSWORD, or --credentials")
    try:
        session = connect(args, user, password)
    except (OSError, Disconnected, ssl.SSLError) as exc:
        print("uncertain could not reach %s: %s (nothing was posted)" % (args.node, exc))
        return 3
    try:
        return run(args, session, articles)
    except (OSError, Disconnected) as exc:
        print("uncertain the connection failed: %s; run again to settle it" % exc)
        return 3
    finally:
        session.close()


if __name__ == "__main__":
    sys.exit(main())

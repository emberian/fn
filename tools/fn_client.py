#!/usr/bin/env python3
"""Read and post on a deployed fn node: STARTTLS, AUTHINFO, and a watermark.

This is the client side, and only the client side.  D07 keeps Python out of
the node; nothing here runs inside one.  It is standard-library Python 3.9 or
later on purpose -- `nntplib` left the standard library in 3.13 (PEP 594), so
a client that imports it is a client that stops working on a current
interpreter -- and it drives the socket by hand, which is also what lets it
keep every status line the node sent.

    fn_client.py groups --cafile hbox-cert.pem
    fn_client.py read fn.agents --new --cafile hbox-cert.pem --json
    fn_client.py show '<a@b.invalid>' --cafile hbox-cert.pem
    fn_client.py post fn.agents --subject 'hello' --cafile hbox-cert.pem <<<'body'

The node decides; this reports.  Every refusal printed here is the status line
the node sent, not a rewording of it, and no reply is reinterpreted: a node
that answers `441 posting failed; the outcome is uncertain, do not repost`
(books/nntp-post.lisp) is reported as uncertain and never as refused.

The three outcomes stay distinct out to the exit code (AGENTS.md, D13):

    0   done, or accepted -- the node answered and the action happened
    1   refused -- the node answered 4xx or 5xx to the action; its line is printed.
        Also the node's certificate failing to verify against --cafile: nothing
        was sent after STARTTLS, so what happened is known.
    3   uncertain -- the connection or the TLS handshake failed, or an article's
        text was sent and no final reply came back.  An uncertain post prints
        the Message-ID it used; `post --draft PATH` keeps the exact article so
        `reconcile PATH` can settle it.
    4   unresolved -- `reconcile` re-sent the same article and the node's answer
        does not say whether it was accepted (NNT-019).
    2   usage

Acceptance is settled only by re-submitting the SAME article under the SAME
Message-ID (D25, NNT-019): the node answers `441 ... already stored here`
for a source it holds, even after the article was withdrawn by a cancel or
its content reclaimed.  A `430` to `show` is a visibility observation -- the
article is not served to this reader now -- and never evidence that a post
was not accepted.

Credentials come from FN_CLIENT_USER and FN_CLIENT_PASSWORD, or from
`--credentials PATH`, a mode-0600 file holding `user password` on one line.
Never from argv, where `ps` would show them.  The password is sent only after
the TLS handshake: if a node answers 381 to AUTHINFO USER on an unprotected
connection it is asking for the password in the clear, and this client stops
and says so instead.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import secrets
import ssl
import stat
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from nntp_session import Disconnected, Session      # noqa: E402  one socket half

DONE, ACCEPTED, REFUSED, UNCERTAIN = "done", "accepted", "refused", "uncertain"
UNRESOLVED = "unresolved"
EXIT = {DONE: 0, ACCEPTED: 0, REFUSED: 1, UNCERTAIN: 3, UNRESOLVED: 4}
DEFAULT_NODE = "192.168.50.39:1119"
DEFAULT_PORT = 1119
# books/nntp-post.lisp fn-nntp-post-outcome: :refused and :uncertain are two
# distinct 441 lines, and a client must not repost on the second one.
UNCERTAIN_POST = "uncertain"
# books/nntp-post.lisp fn-post-store-refusal-text: the Store's two answers
# for a Message-ID it already holds (D25).  The node words them; this client
# only recognizes them.
ALREADY_STORED = "441 posting failed; this article is already stored here"
DIFFERENT_STORED = "441 posting failed; a different article with this Message-ID is stored here"
DRAFT_FORMAT = "fn-client-draft-v1"


class Stop(Exception):
    """An outcome decided before the subcommand could produce its own."""

    def __init__(self, word: str, detail: str):
        super().__init__(detail)
        self.word, self.detail = word, detail


class Result:
    """What a subcommand decided, what it wants printed, and what it may then commit.

    `commit` runs only after the output has been written and only on a
    successful outcome, which is how the read watermark comes to advance for
    articles the caller has actually seen.
    """

    def __init__(self, word: str, detail: str, data: dict, text: str, commit=None):
        self.word, self.detail, self.data, self.text = word, detail, data, text
        self.commit = commit
        self.status_lines: list = []


# ---------------------------------------------------------------- the wire


class Client:
    def __init__(self, args, user: str, password: str, session_factory=Session):
        self.args = args
        self.user, self.password = user, password
        self.session_factory = session_factory
        self.lines: list[str] = []
        self.session = None

    @property
    def node(self) -> str:
        return node_name(self.args.host, self.args.port)

    def record(self, status: str) -> str:
        self.lines.append(status)
        return status

    def cmd(self, text: str, multiline: bool = False):
        """Send one command and record its status line.  A lost connection is uncertain."""
        try:
            status, body = self.session.cmd(text, multiline)
        except (OSError, Disconnected) as exc:
            raise Stop(UNCERTAIN, "the connection failed during %s: %s"
                       % (text.split()[0] if text.split() else "the command", exc))
        self.record(status)
        return status, body

    def open(self) -> None:
        try:
            self.session = self.session_factory(self.args.host, self.args.port,
                                                self.args.timeout)
        except (OSError, Disconnected) as exc:
            # `Disconnected` and not only `OSError`: a node whose owner has
            # stopped behind a forwarder -- the `ssh -L` tunnel of
            # docs/operator.md -- accepts the connection and then closes it
            # before the greeting, which is a reachability failure and must
            # land on uncertain like any other, never on a traceback.
            raise Stop(UNCERTAIN, "could not connect to %s: %s" % (self.node, exc))
        self.record(self.session.greeting)
        labels = self.capabilities()
        if self.args.plain:
            return
        if "STARTTLS" not in labels:
            self.no_protected_channel()
        self.start_tls()
        self.capabilities()
        self.log_in()

    def capabilities(self) -> set:
        status, caps = self.cmd("CAPABILITIES", multiline=True)
        if not status.startswith("101"):
            return set()
        return {one.split()[0].upper() for one in caps if one.strip()}

    def no_protected_channel(self) -> None:
        """The node offers no STARTTLS and --plain was not given.  Say which problem it is.

        483 and 381 are different operator problems: the first is a node that
        requires a protected channel and cannot provide one, the second is a
        node that would take the password in the clear.  Asking costs the
        username on an unprotected connection; it never costs the password,
        because no PASS follows either answer.
        """
        status = self.cmd("AUTHINFO USER " + self.user)[0] if self.user else "(no login configured)"
        if status.startswith("381"):
            raise Stop(REFUSED, "the node answered %s to AUTHINFO USER before TLS: it would "
                                "take the password in the clear, and none was sent" % status)
        raise Stop(REFUSED, "the node advertises no STARTTLS and answered %s; a login here "
                            "would cross in the clear. Use --plain only where you trust the "
                            "path." % status)

    def start_tls(self) -> None:
        context = ssl.create_default_context(cafile=self.args.cafile)
        # The 382 is recorded before the handshake, so a handshake that fails
        # still shows the node agreed to one.
        status = self.cmd("STARTTLS")[0]
        if not status.startswith("382"):
            raise Stop(UNCERTAIN, "no TLS layer: the node answered %s to STARTTLS" % status)
        try:
            self.session.upgrade(context)
        except ssl.SSLCertVerificationError as exc:
            # Not uncertain: what happened is known exactly.  The peer did not
            # prove it holds the certificate --cafile names, this side ended
            # the handshake, and no command went to it after the 382.  The
            # action was refused, by this client, before it began.
            raise Stop(REFUSED, "the certificate %s presented did not verify against --cafile "
                                "%s (%s); nothing was sent after STARTTLS"
                       % (self.node, self.args.cafile, exc.verify_message or exc))
        except (ssl.SSLError, OSError, Disconnected) as exc:
            raise Stop(UNCERTAIN, "the TLS handshake with %s failed: %s" % (self.node, exc))

    def log_in(self) -> None:
        # unreachable-in-composition: `open` reaches here only after
        # `start_tls`, which raises unless a layer came up, so no test can
        # witness this branch and it is not evidence of anything.  It stays
        # because a later caller of `log_in` alone would otherwise inherit
        # the one mistake this whole file exists to avoid.
        if self.session.tls is None:
            raise Stop(UNCERTAIN, "refusing to log in: there is no TLS layer")
        status = self.cmd("AUTHINFO USER " + self.user)[0]
        if status.startswith("381"):
            # Sent straight at the session: the command text holds the secret
            # and nothing that records or renders commands ever sees it.
            try:
                status = self.session.cmd("AUTHINFO PASS " + self.password)[0]
            except (OSError, Disconnected) as exc:
                raise Stop(UNCERTAIN, "the connection failed during the login: %s" % exc)
            self.record(status)
        if not status.startswith("281"):
            raise Stop(REFUSED, status)

    def close(self) -> None:
        if self.session is not None:
            try:
                self.session.close()
            except (OSError, Disconnected):
                pass

    # ------------------------------------------------------------ groups

    def groups(self) -> Result:
        status, body = self.cmd("LIST ACTIVE", multiline=True)
        if not status.startswith("215"):
            return Result(REFUSED, status, {}, "")
        rows = []
        for one in body:
            fields = one.split()
            if len(fields) < 3:
                continue
            # books/nntp-responses.lisp fn-nntp-active-line: name, high, low, status.
            high, low = number(fields[1]), number(fields[2])
            rows.append({"group": fields[0], "first": low, "last": high,
                         "articles": span(low, high),
                         "status": fields[3] if len(fields) > 3 else ""})
        width = max([len(r["group"]) for r in rows] + [5])
        # `articles` is the span the node's own high and low water marks
        # imply, not a count it reported: a removed number is still inside it.
        text = "\n".join(["%-*s  %8s  %6s  %6s" % (width, "group", "articles", "first", "last")]
                         + ["%-*s  %8s  %6s  %6s" % (width, r["group"], show(r["articles"]),
                                                     show(r["first"]), show(r["last"]))
                            for r in rows])
        return Result(DONE, "%s served %d group name(s)" % (self.node, len(rows)),
                      {"groups": rows}, text)

    def counts(self) -> Result:
        """RFC 6048 section 2.2 LIST COUNTS: name, high, low, count, status.

        The count is the node's (books/nntp-list-counts.lisp,
        fn-nntp-group-count-is-listgroup-length: the length of LISTGROUP's
        number list), not the span of the water marks.  A node that does not
        answer 215 (a node older than LIST COUNTS) is REFUSED with its status
        line, and the caller decides what to fall back to.
        """
        status, body = self.cmd("LIST COUNTS", multiline=True)
        if not status.startswith("215"):
            return Result(REFUSED, status, {}, "")
        rows = []
        for one in body:
            fields = one.split()
            if len(fields) < 4:
                continue
            high, low, count = number(fields[1]), number(fields[2]), number(fields[3])
            rows.append({"group": fields[0], "first": low, "last": high,
                         "articles": count, "count": count,
                         "status": fields[4] if len(fields) > 4 else ""})
        return Result(DONE, "%s counted %d group(s)" % (self.node, len(rows)),
                      {"groups": rows}, "")

    def listgroup(self, group: str) -> Result:
        status, body = self.cmd("LISTGROUP " + group, multiline=True)
        if not status.startswith("211"):
            return Result(REFUSED, status, {"group": group}, "")
        numbers = [n for n in (number(line.strip()) for line in body) if n is not None]
        return Result(DONE, status, {"group": group, "numbers": numbers}, "")

    # -------------------------------------------------------------- read

    def read(self, group: str, marks: dict, save) -> Result:
        status = self.cmd("GROUP " + group)[0]
        if not status.startswith("211"):
            return Result(REFUSED, status, {"group": group}, "")
        fields = status.split()
        low = number(fields[2]) if len(fields) > 2 else None
        high = number(fields[3]) if len(fields) > 3 else None
        if low is None or high is None:
            raise Stop(UNCERTAIN, "the node's GROUP line has no water marks: %s" % status)
        mark = marks.get(group)
        if self.args.all:
            start = low
        elif self.args.since is not None:
            start = self.args.since + 1
        elif mark is None:
            start = low                       # never read here: everything is new
        else:
            start = max(mark + 1, low)

        articles, gaps, refusal = [], [], None
        for one in self.wanted(start, high):
            got, body = self.cmd("ARTICLE %d" % one, multiline=True)
            if got.startswith("220"):
                articles.append(article(one, body))
            elif got[:3] in ("423", "430"):
                gaps.append({"number": one, "status": got})
            else:
                refusal = got
                break

        data = {"group": group, "first": low, "last": high, "window_from": start,
                "watermark_before": mark, "watermark_after": mark,
                "articles": articles, "gaps": gaps}
        pieces = [render(one) for one in articles]
        pieces += ["-- %d %s" % (one["number"], one["status"]) for one in gaps]
        if refusal is not None:
            # The watermark does not move: the range was not read to its end,
            # and a later run must offer these numbers again.
            return Result(REFUSED, refusal, data, "\n\n".join(pieces))
        if start > high:
            pieces.append("no articles in %s yet" % group if mark is None
                          else "no articles in %s after %d" % (group, mark))
        data["watermark_after"] = high

        def commit():
            marks[group] = high
            save(marks)

        return Result(DONE, "%s %s: read through %d" % (self.node, group, high),
                      data, "\n\n".join(pieces), commit)

    def wanted(self, start: int, high: int) -> list:
        """Which numbers in start..high the node actually holds.

        OVER answers that in one round trip, so the usual case costs one
        command rather than one 423 per removed number.  A node that does not
        answer it is still readable a number at a time; a 423 or 430 on one
        number is a hole in the group, not a refusal of the read.
        """
        if start > high:
            return []
        status, body = self.cmd("OVER %d-%d" % (start, high), multiline=True)
        if status.startswith("224"):
            found = [number(one.split("\t")[0]) for one in body]
            return [one for one in found if one is not None]
        if status[:3] in ("420", "423"):
            return []
        return list(range(start, high + 1))

    # -------------------------------------------------------------- show

    def show(self, token: str, group: str) -> Result:
        if group:
            status = self.cmd("GROUP " + group)[0]
            if not status.startswith("211"):
                return Result(REFUSED, status, {"group": group}, "")
        status, body = self.cmd("ARTICLE " + token, multiline=True)
        if not status.startswith("220"):
            data = {"article": token}
            if status[:3] in ("423", "430"):
                # Not served to this reader now: withdrawn, reclaimed, not
                # held, or not visible under this login.  Never evidence
                # that a post was not accepted (NNT-019).
                data["visibility"] = "not-visible"
                status += (" -- not visible to this reader now; this is not evidence "
                           "about acceptance")
            return Result(REFUSED, status, data, "")
        fields = status.split()
        # RFC 3977 section 6.2.1.2: retrieval by Message-ID answers the
        # article's number in the selected group, or `220 0` with no group
        # selected or when the article is not in it (books/nntp-responses.lisp
        # fn-nntp-msgid-local-number).  0 is not an article number; --json says
        # null, as `render` does.
        found = number(fields[1]) if len(fields) > 1 else None
        one = article(found or None, body)
        return Result(DONE, "%s %s" % (self.node, one["message_id"] or token),
                      {"articles": [one]}, render(one))

    # -------------------------------------------------------------- post

    def post(self, group: str, lines: list, msgid: str) -> Result:
        data = {"group": group, "message_id": msgid}
        status = self.cmd("POST")[0]
        if not status.startswith("340"):
            return Result(REFUSED, status, data, "")
        try:
            for one in lines:
                self.session.send(("." + one) if one.startswith(".") else one)
            self.session.send(".")
        except (OSError, Disconnected) as exc:
            return Result(UNCERTAIN, unsettled(msgid, "the article text was cut off: %s" % exc),
                          data, "")
        try:
            status = self.record(self.session.line())
        except (OSError, Disconnected) as exc:
            return Result(UNCERTAIN, unsettled(msgid, "no reply came back: %s" % exc), data, "")
        if status.startswith("240"):
            # The Message-ID goes to standard output so a shell can keep it.
            return Result(ACCEPTED, "%s %s %s" % (self.node, msgid, status), data, msgid)
        if status.startswith("441") and UNCERTAIN_POST in status.lower():
            return Result(UNCERTAIN, unsettled(msgid, "the node said %s" % status), data, "")
        if status.startswith("441"):
            return Result(REFUSED, status, data, "")
        # Neither 240 nor either 441: the node did not say it refused the
        # article, so whether it is durable is not known.
        return Result(UNCERTAIN, unsettled(msgid, "the node answered %s, which is neither an "
                                                  "acceptance nor a refusal" % status), data, "")


# -------------------------------------------------------------- rendering


def unsettled(msgid: str, why: str) -> str:
    return ("the article may or may not be durable; do not post a new copy. Message-ID %s -- "
            "settle it by re-sending the same article under the same Message-ID "
            "(`fn_client.py reconcile DRAFT` for a `post --draft DRAFT`). %s" % (msgid, why))


def reconciliation(result: Result) -> Result:
    """What a re-POST of the same article under the same Message-ID settles.

    240 is an acceptance now (and so the only one); the duplicate line is an
    acceptance earlier; the conflict line says a different article holds the
    Message-ID, so this source is not stored under it.  Every other answer --
    a refusal for another reason (a login no longer allowed to post, a
    changed policy), the node's own uncertain line, a lost connection --
    leaves the question open: unresolved, never absent.
    """
    lines = result.status_lines or [result.detail]
    status = next((line for line in reversed(lines)
                   if line[:3] in ("240", "441")), "")
    if result.word == ACCEPTED:
        return Result(ACCEPTED, "accepted by this re-submission: " + result.detail,
                      dict(result.data, settled="accepted-now"), result.text)
    if result.word == REFUSED and status.startswith(ALREADY_STORED):
        return Result(ACCEPTED, "already accepted: the node holds this article (%s)" % status,
                      dict(result.data, settled="already-stored"), result.data.get("message_id", ""))
    if result.word == REFUSED and status.startswith(DIFFERENT_STORED):
        return Result(REFUSED, "a different article holds this Message-ID; this one is not "
                      "stored under it (%s)" % status, dict(result.data, settled="conflict"), "")
    return Result(UNRESOLVED, "the re-submission did not settle it; the original outcome "
                  "stands. The node said: %s" % (status or result.detail),
                  dict(result.data, settled="unresolved"), "")


def write_draft(path: Path, draft: dict) -> None:
    """Atomically replace PATH with DRAFT, durable before return."""
    path = Path(path).expanduser()
    data = (json.dumps(draft, indent=1, sort_keys=True) + "\n").encode()
    temporary = path.with_name("." + path.name + ".tmp")
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    try:
        os.write(fd, data)
        os.fsync(fd)
    finally:
        os.close(fd)
    os.replace(temporary, path)
    directory = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def read_draft(path: Path) -> dict:
    draft = json.loads(Path(path).expanduser().read_text())
    if (not isinstance(draft, dict) or draft.get("format") != DRAFT_FORMAT or
            not isinstance(draft.get("lines"), list) or not draft["lines"] or
            not all(isinstance(line, str) and "\r" not in line and "\n" not in line
                    for line in draft["lines"]) or
            not isinstance(draft.get("message_id"), str) or
            not isinstance(draft.get("group"), str) or
            not isinstance(draft.get("node"), str) or
            not isinstance(draft.get("reconciliations"), list)):
        raise ValueError("not an fn-client draft")
    if ("Message-ID: " + draft["message_id"]) not in draft["lines"]:
        raise ValueError("the draft's article does not carry its Message-ID")
    return draft


def number(text: str):
    try:
        return int(text)
    except (TypeError, ValueError):
        return None


def split_node(text: str):
    """(host, port) for HOST, HOST:PORT, [HOST] or [HOST]:PORT, or (None, None).

    RFC 3986 section 3.2.2 puts an IPv6 literal in brackets precisely so a
    colon can still separate a port, and `[listener] host` admits `::1`
    (docs/operator.md).  A bare token holding more than one colon therefore
    has exactly one reading -- the address, with the default port -- and
    `::1` must never be taken apart into the host `::` at port 1.
    """
    if text.startswith("["):
        host, closed, rest = text[1:].partition("]")
        if not closed or rest not in ("",) and not rest.startswith(":"):
            return None, None
        return host, rest[1:] if rest else str(DEFAULT_PORT)
    if text.count(":") > 1:
        return text, str(DEFAULT_PORT)
    host, marked, port = text.rpartition(":")
    return (host, port) if marked else (text, str(DEFAULT_PORT))


def node_name(host: str, port: int) -> str:
    """How this client writes a node down, brackets and all."""
    return "[%s]:%d" % (host, port) if ":" in host else "%s:%d" % (host, port)


def span(low, high):
    if low is None or high is None or high < low:
        return 0
    return high - low + 1


def show(value) -> str:
    return "-" if value is None else str(value)


def article(num, body: list) -> dict:
    cut = body.index("") if "" in body else len(body)
    fields = headers(body[:cut])
    return {"number": num, "message_id": first(fields, "message-id"),
            "subject": first(fields, "subject"), "from": first(fields, "from"),
            "headers": fields, "body": body[cut + 1:]}


def headers(lines: list) -> list:
    """RFC 5536 section 2.2 folded header fields, as [name, value] pairs in order."""
    fields = []
    for one in lines:
        if one[:1] in (" ", "\t") and fields:
            fields[-1][1] += " " + one.strip()
        elif ":" in one:
            name, _, value = one.partition(":")
            fields.append([name.strip(), value.strip()])
    return fields


def first(fields: list, name: str):
    for entry in fields:
        if entry[0].lower() == name:
            return entry[1]
    return None


def render(one: dict) -> str:
    # RFC 3977 section 6.2.1: retrieval by Message-ID answers with the number
    # 0, which is not an article number and is not printed as one.
    head = " ".join(["---"] + [str(part) for part in (one["number"], one["message_id"]) if part])
    body = ["%s: %s" % (name, value) for name, value in one["headers"]]
    return "\n".join([head] + body + [""] + one["body"])


# ------------------------------------------------------------------ state


def state_file(args) -> Path:
    if args.state:
        return Path(args.state).expanduser()
    name = re.sub(r"[^A-Za-z0-9._-]", "-", args.host)
    return Path.home() / ".fn-client" / ("%s_%d.json" % (name, args.port))


def load_state(path: Path) -> dict:
    try:
        data = json.loads(path.read_text())
    except (OSError, ValueError):
        return {}
    marks = data.get("watermarks")
    return {k: v for k, v in marks.items() if isinstance(v, int)} if isinstance(marks, dict) else {}


def save_state(path: Path, node: str, marks: dict) -> None:
    if not path.parent.is_dir():
        path.parent.mkdir(parents=True, exist_ok=True)
        os.chmod(str(path.parent), 0o700)
    temporary = path.with_name(path.name + ".new")
    handle = os.open(str(temporary), os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(handle, "w") as out:
        out.write(json.dumps({"node": node, "watermarks": marks},
                             indent=1, sort_keys=True) + "\n")
    os.replace(str(temporary), str(path))


def credentials(args, parser):
    if not args.credentials:
        return os.environ.get("FN_CLIENT_USER", ""), os.environ.get("FN_CLIENT_PASSWORD", "")
    path = Path(args.credentials).expanduser()
    try:
        mode = stat.S_IMODE(os.stat(str(path)).st_mode)
        text = path.read_text()
    except OSError as exc:
        parser.error("--credentials %s: %s" % (path, exc))
    if mode != 0o600:
        # Anyone who can read the file can log in as this principal.
        parser.error("--credentials %s is mode %04o; it must be 0600" % (path, mode))
    fields = text.split()
    if len(fields) != 2:
        parser.error("--credentials %s must hold one line, `user password`" % path)
    return fields[0], fields[1]


# ------------------------------------------------------------- the command


def connection_options(parser, suppress: bool) -> None:
    """The options every subcommand takes, before or after the subcommand name.

    The copy on the subparsers suppresses its defaults, so a value given
    before the subcommand survives and is not overwritten by one.
    """
    hide = argparse.SUPPRESS if suppress else None
    parser.add_argument("--node", default=hide if suppress else DEFAULT_NODE,
                        help="HOST or HOST:PORT (default %s)" % DEFAULT_NODE)
    parser.add_argument("--cafile", default=hide, help="the node's certificate, or its CA")
    parser.add_argument("--plain", action="store_true", default=hide,
                        help="no TLS and no login; for a loopback development node")
    parser.add_argument("--timeout", type=float, default=hide if suppress else 30.0)
    parser.add_argument("--credentials", default=hide,
                        help="a mode-0600 file holding `user password`")
    parser.add_argument("--state", default=hide, help="where the watermarks live")
    parser.add_argument("--json", action="store_true", default=hide,
                        help="one JSON document, including every status line")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    connection_options(parser, suppress=False)
    common = argparse.ArgumentParser(add_help=False)
    connection_options(common, suppress=True)
    subcommands = parser.add_subparsers(dest="command")

    subcommands.add_parser("groups", parents=[common], help="LIST ACTIVE")

    reader = subcommands.add_parser("read", parents=[common],
                                    help="the articles after the remembered watermark")
    reader.add_argument("group")
    window = reader.add_mutually_exclusive_group()
    window.add_argument("--new", action="store_true", help="after the watermark (the default)")
    window.add_argument("--since", type=int, metavar="N", help="after article number N")
    window.add_argument("--all", action="store_true", help="every article the group holds")

    shower = subcommands.add_parser("show", parents=[common], help="one article")
    shower.add_argument("id", help="a Message-ID in angle brackets, or a number with --group")
    shower.add_argument("--group", default="")

    poster = subcommands.add_parser("post", parents=[common], help="POST one article")
    poster.add_argument("group")
    poster.add_argument("--subject", required=True)
    poster.add_argument("--from", dest="sender", default=os.environ.get("FN_CLIENT_FROM", ""))
    poster.add_argument("--body-file", dest="body_file", default="",
                        help="the body; standard input when absent")
    poster.add_argument("--message-id", dest="message_id", default="")
    poster.add_argument("--references", default="")
    poster.add_argument("--draft", default="",
                        help="durably keep the exact article here before sending, and the "
                             "node's answer after; `reconcile` re-sends it")

    reconciler = subcommands.add_parser(
        "reconcile", parents=[common],
        help="settle an uncertain post: re-send the draft's exact article, same Message-ID")
    reconciler.add_argument("draft")
    return parser


def resolve(args, parser) -> None:
    host, port = split_node(str(args.node))
    if host is None or not host.strip() or number(port) is None or not 0 < int(port) < 65536:
        parser.error("--node %s: expected HOST, HOST:PORT or [IPV6-ADDRESS]:PORT" % args.node)
    args.host, args.port = host, int(port)
    if getattr(args, "since", None) is not None and args.since < 0:
        # RFC 3977 section 6: article numbers start at 1, so a negative
        # window is a command line to fix here and not a range to put on the
        # wire for the node to call a syntax error.
        parser.error("--since %d: an article number is never negative" % args.since)
    if args.plain and args.cafile:
        parser.error("--plain and --cafile are two different nodes; give one")
    if not args.plain and not args.cafile:
        parser.error("--cafile is required unless --plain; it is the node's own certificate")
    if args.plain and args.credentials:
        parser.error("--plain sends no login, so --credentials cannot apply")
    if getattr(args, "draft", "") and args.command == "post" and \
            Path(args.draft).expanduser().exists():
        parser.error("--draft %s exists; settle that post with `reconcile %s`, or name "
                     "a new draft file" % (args.draft, args.draft))


def compose(args, user: str, parser, body_override: str | None = None) -> tuple:
    """The article to post, and the Message-ID it carries."""
    for name, value in (("group", args.group), ("subject", args.subject),
                        ("from", args.sender), ("references", args.references),
                        ("message-id", args.message_id)):
        if "\r" in value or "\n" in value:
            parser.error("--%s must not contain a line break" % name)
    msgid = args.message_id or "<fn-client.%s.%s@%s.invalid>" % (
        dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ"),
        secrets.token_hex(4), re.sub(r"[^A-Za-z0-9.-]", "-", user or "anonymous"))
    if not (msgid.startswith("<") and msgid.endswith(">") and "@" in msgid):
        parser.error("--message-id %s is not <local@domain>" % msgid)
    sender = args.sender or "%s <%s@%s>" % (user or "anonymous", user or "anonymous", args.host)
    if body_override is not None:
        body = body_override
    elif args.body_file:
        try:
            body = Path(args.body_file).expanduser().read_text()
        except OSError as exc:
            parser.error("--body-file %s: %s" % (args.body_file, exc))
    else:
        body = sys.stdin.read()
    # No Path, Injection-Date, Injection-Info or Xref: books/nntp-post.lisp
    # refuses an article that supplies any of them, because they are the
    # injecting and relaying agents' fields and not the poster's.
    lines = ["From: " + sender, "Newsgroups: " + args.group, "Subject: " + args.subject,
             "Message-ID: " + msgid]
    if args.references:
        lines.append("References: " + args.references)
    # A CR inside a line has no framing here: the wire ends a line with CRLF
    # and the node reads it back that way, so one is dropped rather than sent.
    text = body.replace("\r\n", "\n").replace("\r", "").rstrip("\n")
    return lines + [""] + text.split("\n"), msgid


def run(args, user: str, password: str, parser) -> Result:
    if args.command == "reconcile":
        return reconcile(args, user, password, parser)
    lines, msgid = compose(args, user, parser) if args.command == "post" else ([], "")
    if args.command == "show" and not args.id.startswith("<") and not args.group:
        parser.error("show by number needs --group")
    draft_path = getattr(args, "draft", "") if args.command == "post" else ""
    if draft_path:
        # The exact article and its Message-ID are durable before any byte
        # of the POST is sent: an uncertain outcome is then settled by
        # re-sending exactly these lines.
        draft = {"format": DRAFT_FORMAT, "node": node_name(args.host, args.port),
                 "group": args.group, "message_id": msgid, "lines": lines,
                 "original": None, "reconciliations": []}
        try:
            write_draft(Path(draft_path), draft)
        except OSError as exc:
            return Result(REFUSED, "the draft could not be kept (%s); nothing was sent" % exc,
                          {"message_id": msgid}, "")
    result = exchange(args, user, password, lines, msgid)
    if draft_path:
        draft["original"] = {"outcome": result.word, "detail": result.detail,
                             "status_lines": result.status_lines}
        try:
            write_draft(Path(draft_path), draft)
        except OSError as exc:
            sys.stderr.write("the node's answer was not recorded in the draft (%s); the "
                             "draft still holds the exact article\n" % exc)
    return result


def reconcile(args, user: str, password: str, parser) -> Result:
    """Re-send a draft's exact article under its Message-ID; record, never rewrite."""
    path = Path(args.draft).expanduser()
    try:
        draft = read_draft(path)
    except (OSError, ValueError) as exc:
        parser.error("%s: %s" % (args.draft, exc))
    node = node_name(args.host, args.port)
    if draft["node"] != node:
        parser.error("the draft was posted to %s, not %s" % (draft["node"], node))
    msgid = draft["message_id"]
    original = (draft.get("original") or {}).get("outcome")
    data = {"message_id": msgid, "original": original or UNCERTAIN}
    if original in (ACCEPTED, REFUSED):
        # Known already: nothing to settle, and a refused article is not
        # re-sent behind the poster's back.
        return Result(original, "the original post was %s; nothing to reconcile" % original,
                      data, msgid if original == ACCEPTED else "")
    answer = exchange(args, user, password, list(draft["lines"]), msgid)
    settled = reconciliation(answer)
    settled.data.update(data)
    settled.status_lines = answer.status_lines
    draft["reconciliations"].append(
        {"at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
         "outcome": settled.word, "settled": settled.data.get("settled"),
         "status_lines": answer.status_lines})
    try:
        write_draft(path, draft)
    except OSError as exc:
        sys.stderr.write("the reconciliation was not recorded in the draft (%s)\n" % exc)
    return settled


def exchange(args, user: str, password: str, lines: list, msgid: str) -> Result:
    client = Client(args, user, password)
    try:
        client.open()
        if args.command == "groups":
            result = client.groups()
        elif args.command == "read":
            path = state_file(args)
            marks = load_state(path)
            result = client.read(args.group, marks,
                                 lambda saved: save_state(path, client.node, saved))
        elif args.command == "show":
            result = client.show(args.id, args.group)
        else:
            result = client.post(getattr(args, "group", "") or "", lines, msgid)
    except Stop as stop:
        result = Result(stop.word, stop.detail, {"message_id": msgid} if msgid else {}, "")
    finally:
        client.close()
    result.status_lines = client.lines
    return result


def main(argv=None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if not args.command:
        parser.error("name a subcommand: groups, read, show or post")
    resolve(args, parser)
    user, password = ("", "") if args.plain else credentials(args, parser)
    if not args.plain and (not user or not password):
        parser.error("set FN_CLIENT_USER and FN_CLIENT_PASSWORD, or give --credentials")

    result = run(args, user, password, parser)
    # The client's own speech about the session must not carry the secret.
    # Article bodies are the node's content and are not measured against it:
    # a word that happens to be someone's password is still their article.
    if password and password in "\n".join(result.status_lines + [result.detail]):
        sys.stderr.write("refused a status line held the password, so nothing was written\n")
        return EXIT[REFUSED]
    return report(args, result)


def report(args, result: Result) -> int:
    if args.json:
        document = {"node": node_name(args.host, args.port), "command": args.command,
                    "outcome": result.word, "exit": EXIT[result.word],
                    "detail": result.detail, "status_lines": result.status_lines}
        document.update(result.data)
        sys.stdout.write(json.dumps(document, indent=1) + "\n")
    elif result.text:
        sys.stdout.write(result.text + "\n")
    sys.stdout.flush()
    sys.stderr.write("%s %s\n" % (result.word, result.detail))
    if result.commit is not None and result.word in (DONE, ACCEPTED):
        try:
            result.commit()
        except OSError as exc:
            # The node answered and the articles are out; only this side's
            # note of how far it got failed.  That is neither a refusal by
            # the node nor an uncertain outcome -- what happened is known
            # exactly -- so the node's word and exit code stand and the cost
            # is the repeat the watermark exists to avoid, said out loud.
            sys.stderr.write("the watermark was not saved (%s); the next read offers "
                             "these articles again\n" % exc)
    return EXIT[result.word]


if __name__ == "__main__":
    sys.exit(main())

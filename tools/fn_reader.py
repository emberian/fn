#!/usr/bin/env python3
"""fn reader: a web reader for friends of an fn node (WEB-003).

A small web service. A friend signs in with the login an invitation code
created, and reads and writes in the node's groups from any browser, phone
included. It is a client, like tin or Thunderbird:

- Every page is made from what the node answers over NNTP (RFC 3977), on a
  STARTTLS connection whose certificate is verified (--tls-cert), logged in
  with the friend's own AUTHINFO USER/PASS (RFC 4643). The node checks the
  password, decides which groups the login may see or post to, accepts,
  refuses or holds each post, decides who may approve and whose cancel
  withdraws what. This process decides none of it and adds no authority:
  it never opens the Store and holds no account table of its own.
- The password is held in this process's memory for the length of the
  browser session (to open the friend's NNTP connections) and is never
  written to a file, a URL, a page or a log.
- Kept here, per login: which articles the friend has opened (NNTP keeps no
  read state), the display name for From, and a record of each submission
  (the exact article lines and the node's answer), written before the POST
  is sent so a lost answer stays "not sure" and is settled by re-sending the
  same article under the same Message-ID (NNT-019), never by a new post.
- Accepted, refused and not-sure stay three outcomes on every page.

Pages are server-rendered HTML with no JavaScript and nothing loaded from
another site. The browser side is HTTPS (--https-cert/--https-key); plain
HTTP is accepted only when the listener is loopback (a TLS proxy or an ssh
tunnel in front of it).

    python3 tools/fn_reader.py --node news.example.net:1119 --tls-cert node-cert.pem \\
        --state ~/.fn-reader --listen 0.0.0.0:8443 \\
        --https-cert web-cert.pem --https-key web-key.pem --mail-domain example.net
"""
from __future__ import annotations

import argparse
import datetime as dt
import email
import email.header
import email.policy
import email.utils
import html
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import hmac
import json
import os
from pathlib import Path
import quopri
import re
import secrets
import ssl
import sys
import threading
import time
from types import SimpleNamespace
from urllib.parse import parse_qs, urlencode, urlsplit

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fn_client  # noqa: E402
from fn_web import reply_references, reply_subject, thread_rows  # noqa: E402
from nntp_session import Disconnected, Session  # noqa: E402

# Client-side bounds on one request's work and memory, never on what the node
# stores (D27): a longer article is shown as "too long to show here" and a
# group is read one window of numbers at a time.
MAX_LINE = 262144
MAX_BLOCK = 64 * 1024 * 1024
WINDOW = 200            # numbers per group page
THREAD_SPAN = 1000      # numbers a thread page looks through
THREAD_ARTICLES = 80    # articles one thread page fetches
MAX_FORM = 1024 * 1024
SESSION_IDLE = 12 * 3600
CONNECTION_IDLE = 90
KEEP_CONNECTIONS = True  # one cached NNTP connection per signed-in session
FAILED_SIGNINS = 8      # per address per 15 minutes, then a pause
ENVELOPE = "application/news-transmission"
STATE_FORMAT = "fn-reader-account-v1"
RECORD_FORMAT = "fn-reader-submission-v1"
ACCEPTED, REFUSED, UNCERTAIN = fn_client.ACCEPTED, fn_client.REFUSED, fn_client.UNCERTAIN
UNSENT = "unsent"       # the connection or login failed before any of the article was sent


class BoundedSession(Session):
    def line(self) -> str:
        while b"\r\n" not in self.buf:
            if len(self.buf) > MAX_LINE:
                raise Disconnected("a line from the node is longer than this reader keeps")
            chunk = self.sock.recv(65536)
            if not chunk:
                raise Disconnected("the node closed the connection")
            self.buf += chunk
        out, self.buf = self.buf.split(b"\r\n", 1)
        return out.decode("utf-8", "replace")

    def block(self) -> list:
        lines, size = [], 0
        while True:
            one = self.line()
            if one == ".":
                return lines
            size += len(one) + 2
            if size > MAX_BLOCK:
                raise Disconnected("the answer is longer than this reader shows")
            lines.append(one[1:] if one.startswith("..") else one)


# ------------------------------------------------------------------ text


def e(value) -> str:
    return html.escape("" if value is None else str(value), quote=True)


def href(path: str, **params) -> str:
    params = {k: v for k, v in params.items() if v is not None}
    return path + ("?" + urlencode(params) if params else "")


def decoded(value: str) -> str:
    """RFC 2047 words in a header value, for display only."""
    try:
        return str(email.header.make_header(email.header.decode_header(value or "")))
    except Exception:
        return value or ""


def who(value: str) -> str:
    name, address = email.utils.parseaddr(decoded(value))
    return name or (address.split("@")[0] if address else "") or decoded(value) or "someone"


def when(value: str, now=None):
    """(short, full) for a Date field; the node's field, shown in the reader's words."""
    try:
        moment = email.utils.parsedate_to_datetime(value)
        if moment.tzinfo is None:
            moment = moment.replace(tzinfo=dt.timezone.utc)
    except Exception:
        return ("", value or "")
    now = now or dt.datetime.now(dt.timezone.utc)
    seconds = (now - moment).total_seconds()
    full = moment.astimezone(dt.timezone.utc).strftime("%-d %b %Y, %H:%M UTC")
    if seconds < 60:
        short = "just now"
    elif seconds < 3600:
        short = "%d min ago" % (seconds // 60)
    elif seconds < 86400:
        short = "%d h ago" % (seconds // 3600)
    elif seconds < 7 * 86400:
        short = "%d days ago" % (seconds // 86400) if seconds >= 2 * 86400 else "yesterday"
    else:
        short = moment.strftime("%-d %b %Y")
    return short, full


def header_value(name: str, value: str) -> list:
    """One header field as wire lines: ASCII as is, anything else as RFC 2047 words."""
    value = " ".join(value.split())
    if value.isascii():
        return [name + ": " + value]
    encoded = email.header.Header(value, "utf-8", header_name=name).encode(linesep="\n")
    return (name + ": " + encoded).split("\n")


def body_lines(text: str) -> tuple:
    """(extra header lines, body lines) for a text/plain UTF-8 body."""
    text = text.replace("\r\n", "\n").replace("\r", "\n").rstrip("\n")
    lines = text.split("\n")
    mime = ["MIME-Version: 1.0", "Content-Type: text/plain; charset=utf-8"]
    if all(len(one.encode("utf-8")) <= 900 for one in lines):
        return mime + ["Content-Transfer-Encoding: 8bit"], lines
    encoded = quopri.encodestring(text.encode("utf-8")).decode("ascii")
    return (mime + ["Content-Transfer-Encoding: quoted-printable"],
            encoded.replace("\r\n", "\n").rstrip("\n").split("\n"))


def parse_article(lines: list):
    return email.message_from_bytes(("\n".join(lines) + "\n").encode("utf-8", "replace"),
                                    policy=email.policy.default)


def article_text(message) -> str:
    """The readable text of an article: its text/plain part, decoded."""
    try:
        part = message.get_body(preferencelist=("plain",))
        if part is None:
            return "(This post has no plain text part to show.)"
        if part.get_content_charset() is None:
            # No charset declared (most newsreaders' plain posts): UTF-8, else Latin-1.
            raw = part.get_payload(decode=True) or b""
            try:
                return raw.decode("utf-8")
            except UnicodeDecodeError:
                return raw.decode("latin-1")
        return part.get_content()
    except Exception:
        payload = message.get_payload()
        return payload if isinstance(payload, str) else "(This post could not be shown.)"


def is_envelope(message) -> bool:
    return (message.get_content_type() == ENVELOPE and
            "moderate" in (message.get_param("usage") or ""))


URL = re.compile(r"https?://[^\s<>\"]+")


def rendered_body(text: str) -> str:
    out = []
    for line in text.split("\n"):
        safe = e(line)

        def link(match):
            url = match.group(0)
            tail = ""
            while url and url[-1] in ".,;:!?)":
                tail, url = url[-1] + tail, url[:-1]
            return "<a href='%s' rel='nofollow noopener noreferrer'>%s</a>%s" % (url, url, tail)
        safe = URL.sub(link, safe)
        out.append("<span class='q'>%s</span>" % safe if line.startswith(">") else safe)
    return "<div class='body'>" + "\n".join(out) + "</div>"


# ------------------------------------------------------------ read ranges


def add_range(ranges: list, low: int, high: int) -> list:
    out = []
    for a, b in sorted(ranges + [[low, high]]):
        if out and a <= out[-1][1] + 1:
            out[-1][1] = max(out[-1][1], b)
        else:
            out.append([a, b])
    return out


def is_read(ranges: list, number: int) -> bool:
    return any(a <= number <= b for a, b in ranges)


def read_within(ranges: list, low: int, high: int) -> int:
    return sum(max(0, min(b, high) - max(a, low) + 1) for a, b in ranges)


# ------------------------------------------------------------ per login


def write_json(path: Path, value: dict) -> None:
    temporary = path.with_suffix(".tmp")
    descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
        json.dump(value, handle, sort_keys=True)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)
    directory = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


class AccountState:
    """What this reader keeps for one login on one node: read marks, a display
    name and the submission records. None of it is an fn record."""

    def __init__(self, root: Path, node: str, user: str):
        self.node, self.user = node, user
        self.dir = root / user.encode("utf-8").hex()
        self.dir.mkdir(mode=0o700, parents=True, exist_ok=True)
        (self.dir / "sent").mkdir(mode=0o700, exist_ok=True)
        self.path = self.dir / "account.json"
        self.lock = threading.Lock()
        self.data = {"format": STATE_FORMAT, "node": node, "user": user,
                     "name": "", "read": {}}
        if self.path.exists():
            loaded = json.loads(self.path.read_text(encoding="utf-8"))
            if loaded.get("format") != STATE_FORMAT or loaded.get("node") != node \
                    or loaded.get("user") != user:
                raise ValueError("%s belongs to another node or login" % self.path)
            self.data = loaded

    def save(self) -> None:
        write_json(self.path, self.data)

    def read_ranges(self, group: str) -> list:
        return self.data["read"].get(group, [])

    def mark(self, group: str, numbers) -> None:
        with self.lock:
            ranges = self.read_ranges(group)
            for one in numbers:
                if not is_read(ranges, one):
                    ranges = add_range(ranges, one, one)
            self.data["read"][group] = ranges
            self.save()

    def mark_through(self, group: str, low: int, high: int) -> None:
        with self.lock:
            self.data["read"][group] = add_range(self.read_ranges(group), low, high)
            self.save()

    def set_name(self, name: str) -> None:
        with self.lock:
            self.data["name"] = name
            self.save()

    # submissions: written before the POST; an entry without an answer is not sure.
    def record_path(self, sid: str) -> Path:
        return self.dir / "sent" / (sid + ".json")

    def record(self, sid: str):
        path = self.record_path(sid)
        if not path.exists():
            return None
        record = json.loads(path.read_text(encoding="utf-8"))
        if record.get("outcome") is None:
            record = dict(record, outcome=UNCERTAIN,
                          detail="this reader stopped before the node's answer was recorded")
        return record

    def begin(self, sid: str, record: dict) -> None:
        record = dict(record, format=RECORD_FORMAT, sid=sid, outcome=None, checks=[],
                      at=dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"))
        write_json(self.record_path(sid), record)

    def finish(self, sid: str, **fields) -> dict:
        path = self.record_path(sid)
        record = json.loads(path.read_text(encoding="utf-8"))
        record.update(fields)
        write_json(path, record)
        return self.record(sid)

    def records(self) -> list:
        out = []
        for path in (self.dir / "sent").glob("*.json"):
            try:
                out.append(self.record(path.stem))
            except (OSError, ValueError):
                continue
        return sorted(out, key=lambda r: r.get("at", ""), reverse=True)

    def my_post(self, msgid: str):
        for record in self.records():
            if record.get("kind") == "post" and record.get("message_id") == msgid \
                    and record.get("outcome") == ACCEPTED:
                return record
        return None


class Account:
    """One signed-in browser session: the login, its password (memory only),
    a form token, and one cached NNTP connection."""

    def __init__(self, user: str, password: str, state: AccountState):
        self.user, self.password, self.state = user, password, state
        self.csrf = secrets.token_urlsafe(24)
        self.used = time.time()
        self.lock = threading.RLock()
        self.client = None
        self.client_used = 0.0


# ------------------------------------------------------------ the node


class Node:
    def __init__(self, args):
        self.args = SimpleNamespace(host=args.host, port=args.port, timeout=args.timeout,
                                    plain=args.plain_node, cafile=args.tls_cert)
        self.name = fn_client.node_name(args.host, args.port)

    def connect(self, user: str, password: str):
        client = fn_client.Client(self.args, user, password, session_factory=BoundedSession)
        try:
            client.open()
        except BaseException:
            client.close()
            raise
        return client

    def sign_in(self, user: str, password: str):
        """The node's answer to this login: (word, detail). The node decides."""
        try:
            client = self.connect(user, password)
        except fn_client.Stop as stop:
            return stop.word, stop.detail
        client.close()
        return fn_client.DONE, "signed in"

    def reading(self, account: Account, operation):
        """Run a read-only OPERATION(client) on the account's connection.

        A reused connection that fails is replaced once: reads repeat safely.
        """
        with account.lock:
            client = account.client
            fresh = client is None or time.time() - account.client_used > CONNECTION_IDLE
            if fresh and client is not None:
                client.close()
                client = None
            for attempt in (0, 1):
                if client is None:
                    client = self.connect(account.user, account.password)
                    account.client, fresh = client, True
                client.lines = []
                try:
                    result = operation(client)
                    account.client_used = time.time()
                    if not KEEP_CONNECTIONS:
                        client.close()
                        account.client = None
                    return result
                except fn_client.Stop:
                    client.close()
                    account.client = client = None
                    if fresh or attempt:
                        raise

    def posting(self, account: Account, lines: list, msgid: str):
        """POST on a new connection; never repeated here. fn_client keeps the three outcomes."""
        with account.lock:
            if account.client is not None:
                account.client.close()
                account.client = None
            try:
                client = self.connect(account.user, account.password)
            except fn_client.Stop as stop:
                # Nothing of the article was sent: the connection or login failed first.
                result = fn_client.Result(UNSENT, stop.detail, {}, "")
                result.status_lines = []
                return result
            try:
                result = client.post("", lines, msgid)
                result.status_lines = list(client.lines)
                return result
            finally:
                client.close()


def stream_listgroup_unread(client, group: str, ranges: list) -> int:
    """Unread in a group with gaps: stream LISTGROUP, holding no list."""
    status = client.cmd("LISTGROUP " + group)[0]
    if not status.startswith("211"):
        return None
    unread = 0
    try:
        while True:
            one = client.session.line()
            if one == ".":
                return unread
            number = fn_client.number(one.strip())
            if number is not None and not is_read(ranges, number):
                unread += 1
    except (OSError, Disconnected) as exc:
        raise fn_client.Stop(UNCERTAIN, "the connection failed during LISTGROUP: %s" % exc)


def over_rows(client, low: int, high: int) -> list:
    if high < low:
        return []
    status, body = client.cmd("OVER %d-%d" % (low, high), multiline=True)
    if not status.startswith("224"):
        return []
    rows = []
    for line in body:
        parts = line.split("\t")
        number = fn_client.number(parts[0]) if parts else None
        if number is None or len(parts) < 6:
            continue
        rows.append({"number": number, "subject": parts[1], "from": parts[2],
                     "date": parts[3], "message_id": parts[4], "references": parts[5]})
    return rows


def content_types(client, low: int, high: int) -> dict:
    if high < low:
        return {}
    status, body = client.cmd("HDR Content-Type %d-%d" % (low, high), multiline=True)
    if not status.startswith("225"):
        return {}
    out = {}
    for line in body:
        number, _, value = line.partition(" ")
        if fn_client.number(number) is not None:
            out[int(number)] = value.strip().lower()
    return out


def group_line(client, group: str):
    status = client.cmd("GROUP " + group)[0]
    if not status.startswith("211"):
        return None, status
    fields = status.split()
    return (fn_client.number(fields[1]), fn_client.number(fields[2]),
            fn_client.number(fields[3])), status


# ------------------------------------------------------------------ style

STYLE = """
:root{--bg:#f6f4ee;--card:#fffefa;--ink:#1c2523;--soft:#5b6862;--line:#d9dfd8;--accent:#1f6f5c;
--accent-ink:#fff;--hot:#b3432f;--ok-bg:#dcf1e1;--ok:#155233;--no-bg:#fbe3dc;--no:#7c2616;
--maybe-bg:#fff1c2;--maybe:#6a4b00;--quote:#6b7a73;--focus:#e0a100}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]){--bg:#141917;--card:#1d2421;
--ink:#e6ece8;--soft:#a3b1aa;--line:#34403b;--accent:#69c7a9;--accent-ink:#0d1a15;--hot:#ff8d73;
--ok-bg:#1f3b2b;--ok:#bfe8cd;--no-bg:#43241d;--no:#ffc9bb;--maybe-bg:#40361a;--maybe:#ffe39a;
--quote:#94a59d}}
:root[data-theme=dark]{--bg:#141917;--card:#1d2421;--ink:#e6ece8;--soft:#a3b1aa;--line:#34403b;
--accent:#69c7a9;--accent-ink:#0d1a15;--hot:#ff8d73;--ok-bg:#1f3b2b;--ok:#bfe8cd;--no-bg:#43241d;
--no:#ffc9bb;--maybe-bg:#40361a;--maybe:#ffe39a;--quote:#94a59d}
*{box-sizing:border-box}
html{background:var(--bg);color:var(--ink);font:17px/1.55 system-ui,-apple-system,"Segoe UI",sans-serif}
body{margin:0 auto;max-width:46rem;padding:0 16px 4rem}
a{color:var(--accent);text-underline-offset:.18em}
a:focus-visible,button:focus-visible,input:focus-visible,textarea:focus-visible,summary:focus-visible{outline:3px solid var(--focus);outline-offset:2px}
.skip{position:absolute;left:-999px}.skip:focus{left:8px;top:8px;background:var(--card);padding:.4rem}
header.top{display:flex;flex-wrap:wrap;gap:.3rem 1rem;align-items:center;justify-content:space-between;padding:1rem 0 .8rem;border-bottom:1px solid var(--line);margin-bottom:1.2rem}
header.top .site{font-weight:700;font-size:1.15rem;color:var(--ink);text-decoration:none}
header.top nav{display:flex;flex-wrap:wrap;gap:.2rem 1rem;align-items:center;font-size:.95rem}
h1{font-size:1.6rem;line-height:1.25;margin:.2rem 0 .6rem;overflow-wrap:anywhere}
h2{font-size:1.2rem;margin:1.6rem 0 .5rem}
.soft{color:var(--soft)}.small{font-size:.88rem}
ul.list{list-style:none;margin:0;padding:0}
ul.list li{background:var(--card);border:1px solid var(--line);border-radius:12px;margin:.55rem 0;padding:.75rem 1rem}
ul.list li a.title{font-weight:600;text-decoration:none;color:var(--ink);overflow-wrap:anywhere}
ul.list li a.title:hover{text-decoration:underline}
ul.list li.new a.title{font-weight:800}
.pill{display:inline-block;border-radius:99px;padding:.05rem .55rem;font-size:.8rem;font-weight:600;background:var(--line);color:var(--ink);white-space:nowrap}
.pill.new{background:var(--hot);color:#fff}
.row{display:flex;flex-wrap:wrap;gap:.2rem .8rem;align-items:baseline;justify-content:space-between}
article.post{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:.9rem 1rem;margin:.7rem 0}
article.post.d1{margin-left:1.2rem}article.post.d2{margin-left:2.4rem}article.post.d3{margin-left:3.6rem}
article.post.new{border-left:4px solid var(--hot)}
article.post header{display:flex;flex-wrap:wrap;gap:.1rem .7rem;align-items:baseline;margin-bottom:.4rem}
article.post .author{font-weight:700}
.body{white-space:pre-wrap;overflow-wrap:anywhere}
.body .q{color:var(--quote)}
.actions{display:flex;flex-wrap:wrap;gap:.5rem;margin-top:.6rem}
form{margin:0}
label{display:block;font-weight:600;margin:.8rem 0 .2rem}
input[type=text],input[type=password],textarea{width:100%;font:inherit;color:var(--ink);background:var(--card);border:1px solid var(--soft);border-radius:8px;padding:.6rem .7rem}
textarea{min-height:11rem;resize:vertical}
button,.button{display:inline-block;font:inherit;font-weight:600;border:0;border-radius:8px;padding:.55rem 1rem;background:var(--accent);color:var(--accent-ink);cursor:pointer;text-decoration:none}
button.quiet,.button.quiet{background:transparent;color:var(--accent);border:1px solid var(--line)}
button.danger{background:var(--hot);color:#fff}
button[aria-pressed=true]{background:var(--accent);color:var(--accent-ink)}
.note{border-radius:10px;padding:.7rem .9rem;margin:.8rem 0}
.note.ok{background:var(--ok-bg);color:var(--ok)}.note.no{background:var(--no-bg);color:var(--no)}
.note.maybe{background:var(--maybe-bg);color:var(--maybe)}.note.info{background:var(--card);border:1px solid var(--line)}
code,.said{font-family:ui-monospace,Menlo,monospace;font-size:.85rem;overflow-wrap:anywhere}
details{margin:.6rem 0}summary{cursor:pointer;color:var(--soft)}
footer{margin-top:3rem;border-top:1px solid var(--line);padding-top:1rem;font-size:.88rem;color:var(--soft)}
footer form{display:inline}footer button{padding:.2rem .6rem;font-size:.85rem}
.pager{display:flex;justify-content:space-between;margin:1rem 0}
@media (max-width:480px){html{font-size:16px}h1{font-size:1.35rem}article.post.d1{margin-left:.6rem}article.post.d2{margin-left:1.2rem}article.post.d3{margin-left:1.8rem}}
"""


# ------------------------------------------------------------ the server


class Reader(ThreadingHTTPServer):
    daemon_threads = True

    def __init__(self, address, node: Node, state_root: Path, *, site: str,
                 mail_domain: str, secure: bool):
        super().__init__(address, Handler)
        self.node, self.state_root = node, state_root
        self.site, self.mail_domain, self.secure = site, mail_domain, secure
        self.sessions: dict = {}
        self.states: dict = {}
        self.lock = threading.Lock()
        self.failures: dict = {}

    def state_for(self, user: str) -> AccountState:
        with self.lock:
            if user not in self.states:
                self.states[user] = AccountState(self.state_root, self.node.name, user)
            return self.states[user]

    def open_session(self, user: str, password: str) -> str:
        token = secrets.token_urlsafe(32)
        with self.lock:
            self.expire()
            self.sessions[token] = Account(user, password, None)
        self.sessions[token].state = self.state_for(user)
        return token

    def expire(self) -> None:
        now = time.time()
        for token, account in list(self.sessions.items()):
            if now - account.used > SESSION_IDLE:
                self.drop(token)

    def drop(self, token: str) -> None:
        account = self.sessions.pop(token, None)
        if account is not None:
            account.password = ""
            if account.client is not None:
                account.client.close()

    def failed(self, address: str, add: bool = False) -> int:
        now = time.time()
        with self.lock:
            recent = [t for t in self.failures.get(address, []) if now - t < 900]
            if add:
                recent.append(now)
            self.failures[address] = recent
            return len(recent)


class Handler(BaseHTTPRequestHandler):
    server_version = "fn-reader"
    sys_version = ""

    def log_message(self, *args):
        return      # no access log: URLs name groups and people's posts

    # ---------------------------------------------------------- plumbing

    def cookies(self) -> dict:
        out = {}
        for part in (self.headers.get("Cookie") or "").split(";"):
            name, _, value = part.strip().partition("=")
            if name:
                out[name] = value
        return out

    def account(self):
        token = self.cookies().get("fnr_session", "")
        account = self.server.sessions.get(token)
        if account is None:
            return None
        if time.time() - account.used > SESSION_IDLE:
            self.server.drop(token)
            return None
        account.used = time.time()
        return account

    def theme(self) -> str:
        value = self.cookies().get("fnr_theme", "auto")
        return value if value in ("light", "dark", "auto") else "auto"

    def cookie(self, name: str, value: str, max_age=None) -> str:
        parts = ["%s=%s" % (name, value), "Path=/", "HttpOnly", "SameSite=Lax"]
        if self.server.secure:
            parts.append("Secure")
        if max_age is not None:
            parts.append("Max-Age=%d" % max_age)
        return "; ".join(parts)

    def send(self, code: int, body: str, headers=(), content_type="text/html; charset=utf-8"):
        data = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Security-Policy",
                         "default-src 'none'; style-src 'self'; img-src 'self'; "
                         "form-action 'self'; frame-ancestors 'none'; base-uri 'none'")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "same-origin")
        if self.server.secure:
            self.send_header("Strict-Transport-Security", "max-age=31536000")
        for name, value in headers:
            self.send_header(name, value)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(data)

    def redirect(self, location: str, headers=()):
        self.send_response(303)
        self.send_header("Location", location)
        self.send_header("Content-Length", "0")
        self.send_header("Cache-Control", "no-store")
        for name, value in headers:
            self.send_header(name, value)
        self.end_headers()

    def page(self, title: str, content: str, account=None, code=200, headers=()):
        theme = self.theme()
        nav = ""
        if account is not None:
            nav = ("<nav aria-label='Main'><a href='/'>Groups</a>"
                   "<a href='/me'>%s</a>"
                   "<form method='post' action='/signout'>%s"
                   "<button class='quiet' type='submit'>Sign out</button></form></nav>"
                   % (e(account.state.data.get("name") or account.user), self.token(account)))
        switch = "".join(
            "<button type='submit' name='theme' value='%s' class='quiet'%s>%s</button> "
            % (value, " aria-pressed='true'" if theme == value else "", label)
            for value, label in (("light", "Light"), ("dark", "Dark"), ("auto", "Automatic")))
        body = ("<!doctype html><html lang='en'%s><head><meta charset='utf-8'>"
                "<meta name='viewport' content='width=device-width, initial-scale=1'>"
                "<meta name='color-scheme' content='light dark'>"
                "<title>%s · %s</title><link rel='stylesheet' href='/style.css'></head><body>"
                "<a class='skip' href='#main'>Skip to the page</a>"
                "<header class='top'><a class='site' href='/'>%s</a>%s</header>"
                "<main id='main'>%s</main>"
                "<footer><form method='post' action='/theme'>Colours: %s</form></footer>"
                "</body></html>"
                % ("" if theme == "auto" else " data-theme='%s'" % theme,
                   e(title), e(self.server.site), e(self.server.site), nav, content, switch))
        self.send(code, body, headers)

    def token(self, account) -> str:
        return "<input type='hidden' name='csrf' value='%s'>" % e(account.csrf)

    def form(self) -> dict:
        length = int(self.headers.get("Content-Length") or 0)
        if length > MAX_FORM:
            raise ValueError("That was too much to send at once.")
        raw = self.rfile.read(length).decode("utf-8", "replace")
        return {k: v[0] for k, v in parse_qs(raw, keep_blank_values=True).items()}

    def same_site(self) -> bool:
        """A POST must come from this site's own pages."""
        fetch = self.headers.get("Sec-Fetch-Site")
        if fetch and fetch not in ("same-origin", "none"):
            return False
        origin = self.headers.get("Origin")
        if origin and origin != "null":
            return urlsplit(origin).netloc == (self.headers.get("Host") or "")
        return True

    def query(self) -> dict:
        return {k: v[0] for k, v in parse_qs(urlsplit(self.path).query).items()}

    def trouble(self, account, stop) -> None:
        """A connection problem or a refused login on a page."""
        if stop.word == REFUSED and stop.detail.startswith("481"):
            token = self.cookies().get("fnr_session", "")
            self.server.drop(token)
            self.page("Signed out", "<h1>Please sign in again</h1><p>The server no longer "
                      "accepts your password for this session.</p><p><a class='button' "
                      "href='/signin'>Sign in</a></p>", code=401)
            return
        self.page("Can't reach the server",
                  "<h1>We can't reach the server right now</h1><p>Please try again in a "
                  "minute.</p><details><summary>Details</summary><p class='said'>%s</p>"
                  "</details>" % e(stop.detail), account, code=503)

    # ---------------------------------------------------------- dispatch

    def do_HEAD(self):
        self.do_GET()

    def do_GET(self):
        path = urlsplit(self.path).path
        if path == "/style.css":
            self.send(200, STYLE, [("Cache-Control", "max-age=3600")],
                      content_type="text/css; charset=utf-8")
            return
        if path == "/signin":
            self.signin_page()
            return
        account = self.account()
        if account is None:
            self.redirect(href("/signin", next=self.path if path != "/" else None))
            return
        routes = {"/": self.groups_page, "/g": self.group_page, "/t": self.thread_page,
                  "/new": self.compose_page, "/sent": self.sent_page, "/me": self.me_page,
                  "/remove": self.remove_page, "/find": self.find_page}
        handler = routes.get(path)
        if handler is None:
            self.page("Not found", "<h1>There's nothing here</h1><p><a href='/'>Back to the "
                      "groups</a></p>", account, code=404)
            return
        try:
            handler(account)
        except fn_client.Stop as stop:
            self.trouble(account, stop)

    def do_POST(self):
        path = urlsplit(self.path).path
        if not self.same_site():
            self.page("Not allowed", "<h1>That didn't come from this site</h1>", code=403)
            return
        try:
            fields = self.form()
        except ValueError as exc:
            self.page("Too much", "<h1>%s</h1>" % e(exc), code=413)
            return
        if path == "/theme":
            value = fields.get("theme", "auto")
            value = value if value in ("light", "dark", "auto") else "auto"
            back = urlsplit(self.headers.get("Referer") or "/")
            target = (back.path or "/") + ("?" + back.query if back.query else "")
            if back.netloc and back.netloc != self.headers.get("Host"):
                target = "/"
            self.redirect(target, [("Set-Cookie", self.cookie("fnr_theme", value, 400 * 86400))])
            return
        if path == "/signin":
            self.signin(fields)
            return
        account = self.account()
        if account is None or not hmac.compare_digest(fields.get("csrf", ""), account.csrf):
            self.redirect("/signin")
            return
        routes = {"/signout": self.signout, "/post": self.post, "/check": self.check,
                  "/remove": self.remove, "/approve": self.approve, "/read-all": self.read_all,
                  "/me": self.save_me, "/edit": self.edit_again}
        handler = routes.get(path)
        if handler is None:
            self.page("Not found", "<h1>There's nothing here</h1>", account, code=404)
            return
        try:
            handler(account, fields)
        except fn_client.Stop as stop:
            self.trouble(account, stop)

    # ---------------------------------------------------------- sign in

    def signin_page(self, message: str = "", user: str = "", code: int = 200, nxt: str = ""):
        pre = self.cookies().get("fnr_pre") or secrets.token_urlsafe(18)
        nxt = nxt or self.query().get("next", "")
        warn = ("<p class='note no' role='alert'>%s</p>" % e(message)) if message else ""
        self.page("Sign in",
                  "<h1>Sign in</h1><p class='soft'>Use the name and password you chose when "
                  "you accepted your invitation.</p>%s"
                  "<form method='post' action='/signin'>"
                  "<input type='hidden' name='pre' value='%s'>"
                  "<input type='hidden' name='next' value='%s'>"
                  "<label for='user'>Name</label><input type='text' id='user' name='user' "
                  "value='%s' autocomplete='username' autocapitalize='none' spellcheck='false' "
                  "required>"
                  "<label for='password'>Password</label><input type='password' id='password' "
                  "name='password' autocomplete='current-password' required>"
                  "<p><button type='submit'>Sign in</button></p></form>"
                  % (warn, e(pre), e(nxt), e(user)),
                  code=code, headers=[("Set-Cookie", self.cookie("fnr_pre", pre, 3600))])

    def signin(self, fields: dict):
        user, password = fields.get("user", "").strip(), fields.get("password", "")
        nxt = fields.get("next", "")
        if not nxt.startswith("/") or nxt.startswith("//") or "\\" in nxt:
            nxt = "/"
        pre = self.cookies().get("fnr_pre", "")
        if not pre or not hmac.compare_digest(pre, fields.get("pre", "")):
            self.signin_page("Something went wrong. Please try again.", user, 400, nxt)
            return
        address = self.client_address[0]
        if self.server.failed(address) >= FAILED_SIGNINS:
            self.signin_page("Too many tries. Please wait a few minutes and try again.",
                             user, 429, nxt)
            return
        if not user or not re.fullmatch(r"[\x21-\x7e]{1,64}", user) or \
                not password or any(c in password for c in "\r\n\0"):
            self.server.failed(address, add=True)
            self.signin_page("That name and password don't match.", user, 401, nxt)
            return
        word, detail = self.server.node.sign_in(user, password)
        if word == fn_client.DONE:
            token = self.server.open_session(user, password)
            self.redirect(nxt, [("Set-Cookie", self.cookie("fnr_session", token)),
                                ("Set-Cookie", self.cookie("fnr_pre", "", 0))])
            return
        if word == REFUSED and detail.startswith("481"):
            self.server.failed(address, add=True)
            self.signin_page("That name and password don't match.", user, 401, nxt)
        elif word == REFUSED and detail.startswith("the certificate"):
            self.signin_page("We couldn't confirm the server is the real one, so your "
                             "password was not sent. Please tell the person who invited you.",
                             user, 502, nxt)
        elif word == REFUSED:
            self.signin_page("The server said no: %s" % detail, user, 403, nxt)
        else:
            self.signin_page("We can't reach the server right now. Please try again in a "
                             "minute.", user, 503, nxt)

    def signout(self, account, fields):
        self.server.drop(self.cookies().get("fnr_session", ""))
        self.redirect("/signin", [("Set-Cookie", self.cookie("fnr_session", "", 0))])

    # ---------------------------------------------------------- groups

    def groups_page(self, account):
        state = account.state

        def query(client):
            counted = client.counts()
            rows = counted.data["groups"] if counted.word == fn_client.DONE else \
                client.groups().data.get("groups", [])
            # The posting status is LIST ACTIVE's (RFC 3977 section 7.6.3); the node's
            # LIST COUNTS reports `y` for a moderated group (PKT-703).
            status, body = client.cmd("LIST ACTIVE", multiline=True)
            if status.startswith("215"):
                flags = {f[0]: f[3] for f in (line.split() for line in body) if len(f) > 3}
                for row in rows:
                    row["status"] = flags.get(row["group"], row.get("status", ""))
            status, body = client.cmd("LIST NEWSGROUPS", multiline=True)
            about = {}
            if status.startswith("215"):
                for line in body:
                    name, _, text = line.partition("\t")
                    text = text.strip()
                    if text and text != "(no description)":
                        about[name.strip()] = text
            for row in rows:
                ranges = state.read_ranges(row["group"])
                low, high, count = row["first"], row["last"], row.get("count")
                if low is None or high is None or high < low or count == 0:
                    row["unread"] = 0
                elif count is None:       # a node without LIST COUNTS
                    unread = stream_listgroup_unread(client, row["group"], ranges)
                    row["unread"] = (unread if unread is not None else
                                     high - low + 1 - read_within(ranges, low, high))
                    row["count"] = row["unread"] + read_within(ranges, low, high)
                elif count == high - low + 1:
                    row["unread"] = count - read_within(ranges, low, high)
                else:
                    row["unread"] = stream_listgroup_unread(client, row["group"], ranges)
                    if row["unread"] is None:
                        row["unread"] = count - read_within(ranges, low, high)
                row["about"] = decoded(about.get(row["group"], ""))
            return rows
        rows = self.server.node.reading(account, query)
        items, others = [], []
        moderated = {r["group"] for r in rows if r.get("status") == "m"}
        for row in sorted(rows, key=lambda r: r["group"]):
            unread = row.get("unread")
            pill = ("<span class='pill new'>%d new</span>" % unread if unread else
                    "<span class='pill'>all read</span>" if unread == 0 and row.get("count")
                    else "")
            status = {"m": "A moderator checks new posts before they appear.",
                      "n": "Read only."}.get(row.get("status", ""), "")
            name, _, last = row["group"].rpartition(".")
            if last == "moderation" and name in moderated and not row["about"]:
                # a label only: the node decides who is served this group
                row["about"] = "Posts waiting for your approval in %s." % name
            (others if row["group"].startswith("control.") else items).append(
                "<li%s><div class='row'><a class='title' href='%s'>%s</a>%s</div>%s%s</li>"
                % (" class='new'" if unread else "", e(href("/g", name=row["group"])),
                   e(row["group"]), pill,
                   "<div class='soft small'>%s</div>" % e(row["about"]) if row["about"] else "",
                   "<div class='soft small'>%s</div>" % status if status else ""))
        self.page("Groups", "<h1>Groups</h1>" + (
            "<ul class='list'>%s</ul>" % "".join(items) if items else
            "<p>There are no groups for you here yet.</p>") + (
            "<details><summary>Technical groups</summary><ul class='list'>%s</ul></details>"
            % "".join(others) if others else ""), account)

    def group_page(self, account):
        group = self.query().get("name", "")
        before = fn_client.number(self.query().get("before", ""))
        state = account.state

        def query(client):
            summary, status = group_line(client, group)
            if summary is None:
                return None
            count, low, high = summary
            end = min(high, before - 1) if before else high
            start = max(low, end - WINDOW + 1)
            rows = over_rows(client, start, end) if count else []
            types = content_types(client, start, end) if rows else {}
            # A held post's envelope (RFC 5537 section 3.5.1) is listed by the post inside.
            held = [r for r in rows if ENVELOPE in types.get(r["number"], "")]
            for row in held[-THREAD_ARTICLES:]:
                got, body = client.cmd("BODY %d" % row["number"], multiline=True)
                if got.startswith("222"):
                    inner = parse_article(body)
                    row["subject"] = str(inner.get("Subject", "")) or row["subject"]
                    row["from"] = str(inner.get("From", "")) or row["from"]
            return {"low": low, "high": high, "start": start, "end": end, "rows": rows,
                    "types": types}
        found = self.server.node.reading(account, query)
        if found is None:
            self.missing(account)
            return
        ranges = state.read_ranges(group)
        threads = {}
        order = []
        root_of = None
        for row, depth, _ in thread_rows(found["rows"]):
            if depth == 0:
                root_of = row
                threads[row["number"]] = {"root": row, "rows": []}
                order.append(row["number"])
            threads[root_of["number"]]["rows"].append(row)
        order.sort(key=lambda n: max(r["number"] for r in threads[n]["rows"]), reverse=True)
        items = []
        for number in order:
            thread = threads[number]
            root = thread["root"]
            unread = sum(1 for r in thread["rows"] if not is_read(ranges, r["number"]))
            latest = max(thread["rows"], key=lambda r: r["number"])
            short, full = when(latest["date"])
            waiting = ENVELOPE in found["types"].get(root["number"], "")
            replies = len(thread["rows"]) - 1
            items.append(
                "<li%s><div class='row'><a class='title' href='%s'>%s</a>%s</div>"
                "<div class='soft small'>%s%s · <span title='%s'>%s</span></div></li>"
                % (" class='new'" if unread else "",
                   e(href("/t", g=group, n=root["number"])),
                   e(("Waiting for approval: " if waiting else "") +
                     (decoded(root["subject"]) or "(no subject)")),
                   "<span class='pill new'>%d new</span>" % unread if unread else "",
                   e(who(root["from"])),
                   " · %d repl%s" % (replies, "y" if replies == 1 else "ies") if replies else "",
                   e(full), e(short)))
        older = ("<a href='%s'>Older posts</a>" % e(href("/g", name=group, before=found["start"]))
                 if found["start"] > found["low"] and found["rows"] else "<span></span>")
        newer = ("<a href='%s'>Newest posts</a>" % e(href("/g", name=group))
                 if before else "<span></span>")
        mark = ("<form method='post' action='/read-all'>%s<input type='hidden' name='g' "
                "value='%s'><input type='hidden' name='through' value='%d'>"
                "<button class='quiet' type='submit'>Mark all as read</button></form>"
                % (self.token(account), e(group), found["high"]) if items else "")
        self.page(group,
                  "<h1>%s</h1><div class='actions'><a class='button' href='%s'>Write a new "
                  "post</a>%s</div>%s<nav class='pager' aria-label='More posts'>%s%s</nav>"
                  % (e(group), e(href("/new", g=group)), mark,
                     "<ul class='list'>%s</ul>" % "".join(items) if items else
                     "<p>No posts here yet. Be the first!</p>", newer, older), account)

    def missing(self, account):
        self.page("Not found", "<h1>We couldn't find that group</h1><p>It may not exist, or "
                  "it may not be open to you.</p><p><a href='/'>Back to the groups</a></p>",
                  account, code=404)

    def read_all(self, account, fields):
        group = fields.get("g", "")
        through = fn_client.number(fields.get("through", ""))
        if through:
            account.state.mark_through(group, 1, through)
        self.redirect(href("/g", name=group))

    # ---------------------------------------------------------- a thread

    def thread_page(self, account, notice: str = ""):
        q = self.query()
        group, number = q.get("g", ""), fn_client.number(q.get("n", ""))
        if not number:
            self.missing(account)
            return
        state = account.state

        def query(client):
            summary, status = group_line(client, group)
            if summary is None:
                return None
            count, low, high = summary
            start = max(low, number - 100)
            end = min(high, number + THREAD_SPAN)
            rows = over_rows(client, start, end)
            ordered = thread_rows(rows)
            # the thread holding NUMBER: from its root to the next root
            index = next((i for i, (r, _, _) in enumerate(ordered) if r["number"] == number),
                         None)
            if index is None:
                return {"posts": [], "earlier": None}
            top = index
            while ordered[top][1] > 0:
                top -= 1
            chosen = [ordered[top]]
            for item in ordered[top + 1:]:
                if item[1] == 0:
                    break
                chosen.append(item)
            posts = []
            for row, depth, _ in chosen[:THREAD_ARTICLES]:
                got, body = client.cmd("ARTICLE %d" % row["number"], multiline=True)
                if got.startswith("220"):
                    posts.append((row, depth, body))
            refs = ordered[top][0]["references"].split()
            return {"posts": posts, "earlier": refs[0] if refs else None,
                    "more": len(chosen) > THREAD_ARTICLES}
        try:
            found = self.server.node.reading(account, query)
        except fn_client.Stop as stop:
            if "longer than this reader" in stop.detail:
                self.page("Too long", "<h1>This post is too long to show here</h1>", account)
                return
            raise
        if found is None:
            self.missing(account)
            return
        if not found["posts"]:
            self.page("Not found", "<h1>That post isn't here</h1><p>It may have been "
                      "removed.</p><p><a href='%s'>Back to %s</a></p>"
                      % (e(href("/g", name=group)), e(group)), account, code=404)
            return
        ranges = state.read_ranges(group)
        cards, title = [], None
        for row, depth, lines in found["posts"]:
            message = parse_article(lines)
            fresh = not is_read(ranges, row["number"])
            subject = decoded(str(message.get("Subject", "")) or row["subject"])
            if is_envelope(message):
                inner = parse_article(str(message.get_payload()).replace("\r\n", "\n")
                                      .split("\n"))
                subject = "Waiting for approval: " + (
                    decoded(str(inner.get("Subject", ""))) or "(no subject)")
            title = title or subject
            cards.append(self.card(account, group, row, depth, message, fresh))
        state.mark(group, [row["number"] for row, _, _ in found["posts"]])
        earlier = ("<p class='soft small'>This continues an earlier conversation. "
                   "<a href='%s'>See the earlier post</a></p>"
                   % e(href("/find", id=found["earlier"], g=group)) if found["earlier"] else "")
        more = ("<p class='soft small'>This conversation is long; only the first %d posts "
                "are shown.</p>" % THREAD_ARTICLES if found.get("more") else "")
        self.page(title or group,
                  "<p class='small'><a href='%s'>&larr; %s</a></p>%s<h1>%s</h1>%s%s%s"
                  % (e(href("/g", name=group)), e(group), notice, e(title or "(no subject)"),
                     earlier, "".join(cards), more), account)

    def card(self, account, group, row, depth, message, fresh) -> str:
        short, full = when(str(message.get("Date", "")) or row["date"])
        author = who(str(message.get("From", "")) or row["from"])
        msgid = row["message_id"]
        actions = []
        if is_envelope(message):
            inner = message.get_payload()
            inner = inner if isinstance(inner, str) else ""
            proto = parse_article(inner.replace("\r\n", "\n").split("\n"))
            text = article_text(proto)
            groups = str(proto.get("Newsgroups", ""))
            actions.append(
                "<form method='post' action='/approve'>%s<input type='hidden' name='g' "
                "value='%s'><input type='hidden' name='n' value='%d'>"
                "<input type='hidden' name='sid' value='%s'>"
                "<button type='submit'>Approve and publish</button></form>"
                % (self.token(account), e(group), row["number"], secrets.token_hex(12)))
            return ("<article class='post' aria-label='Waiting for approval'>"
                    "<p class='note info'><strong>Waiting for approval.</strong> %s wrote "
                    "this for %s. It appears there once a moderator approves it. "
                    "Turning a post down isn't possible here yet: leave it.</p>"
                    "<header><span class='author'>%s</span><span class='soft small'>%s</span>"
                    "</header><p><strong>%s</strong></p>%s<div class='actions'>%s</div>"
                    "</article>"
                    % (e(who(str(proto.get("From", "")))), e(groups),
                       e(who(str(proto.get("From", "")))), e(short),
                       e(decoded(str(proto.get("Subject", ""))) or "(no subject)"),
                       rendered_body(text), "".join(actions)))
        actions.append("<a class='button quiet' href='%s'>Reply</a>"
                       % e(href("/new", g=group, re=row["number"])))
        if account.state.my_post(msgid):
            actions.append("<a class='button quiet' href='%s'>Remove my post</a>"
                           % e(href("/remove", id=msgid, g=group, n=row["number"])))
        classes = "post" + (" d%d" % min(depth, 3) if depth else "") + (" new" if fresh else "")
        return ("<article class='%s' id='n%d'>"
                "<header><span class='author'>%s</span>"
                "<span class='soft small' title='%s'>%s</span>%s</header>%s"
                "<div class='actions'>%s</div></article>"
                % (classes, row["number"], e(author), e(full), e(short),
                   "<span class='pill new'>new</span>" if fresh else "",
                   rendered_body(article_text(message)), "".join(actions)))

    def find_page(self, account):
        q = self.query()
        msgid, group = q.get("id", ""), q.get("g", "")
        if not re.fullmatch(r"<[^<>\s]{1,500}>", msgid):
            self.missing(account)
            return

        def query(client):
            if group:
                if group_line(client, group)[0] is None:
                    return None
            status = client.cmd("STAT " + msgid)[0]
            if status.startswith("223"):
                return fn_client.number(status.split()[1])
            return None
        number = self.server.node.reading(account, query)
        if number:
            self.redirect(href("/t", g=group, n=number))
            return
        self.page("Not here", "<h1>That earlier post isn't here</h1><p>It may have been "
                  "removed, or it is in a group that isn't open to you.</p><p><a href='%s'>"
                  "Back</a></p>" % e(href("/g", name=group) if group else "/"), account,
                  code=404)

    # ---------------------------------------------------------- writing

    def sender(self, account) -> str:
        name = account.state.data.get("name") or account.user
        return email.utils.formataddr(
            (name, "%s@%s" % (account.user, self.server.mail_domain)), charset="utf-8")

    def msgid(self, account) -> str:
        return "<fn-reader.%s.%s@%s>" % (
            dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ"),
            secrets.token_hex(6), self.server.mail_domain)

    def compose_page(self, account, fields=None, message=""):
        q = fields or self.query()
        group = q.get("g", "")
        parent = fn_client.number(q.get("re", ""))
        subject, refs, quoted = q.get("subject", ""), q.get("refs", ""), ""
        if parent and fields is None:
            def query(client):
                if group_line(client, group)[0] is None:
                    return None
                rows = over_rows(client, parent, parent)
                return rows[0] if rows else None
            row = self.server.node.reading(account, query)
            if row is None:
                self.missing(account)
                return
            subject = reply_subject(decoded(row["subject"]))
            refs = reply_references(row["references"], row["message_id"])
            quoted = who(row["from"])
        sid = q.get("sid") or secrets.token_hex(12)
        warn = ("<p class='note no' role='alert'>%s</p>" % e(message)) if message else ""
        heading = ("Reply to %s" % quoted) if quoted else (
            "Reply" if refs else "New post in %s" % group)
        self.page(heading,
                  "<p class='small'><a href='%s'>&larr; %s</a></p><h1>%s</h1>%s"
                  "<form method='post' action='/post'>%s"
                  "<input type='hidden' name='sid' value='%s'>"
                  "<input type='hidden' name='g' value='%s'>"
                  "<input type='hidden' name='refs' value='%s'>"
                  "<input type='hidden' name='re' value='%s'>"
                  "<label for='subject'>Subject</label>"
                  "<input type='text' id='subject' name='subject' value='%s' maxlength='200' "
                  "required>"
                  "<label for='body'>Message</label>"
                  "<textarea id='body' name='body' required>%s</textarea>"
                  "<p class='soft small'>Posting as %s. Everyone who can read %s will see "
                  "it.</p><div class='actions'><button type='submit'>Post</button>"
                  "<a class='button quiet' href='%s'>Cancel</a></div></form>"
                  % (e(href("/g", name=group)), e(group), e(heading), warn,
                     self.token(account), e(sid), e(group), e(refs), e(parent or ""),
                     e(subject), e(q.get("body", "")), e(self.sender(account)), e(group),
                     e(href("/t", g=group, n=parent) if parent else href("/g", name=group))),
                  account)

    def post(self, account, fields):
        sid = fields.get("sid", "")
        if not re.fullmatch(r"[0-9a-f]{24}", sid):
            self.redirect("/")
            return
        state = account.state
        if state.record(sid) is not None:     # the same form again: never a second POST
            self.redirect(href("/sent", id=sid))
            return
        group = fields.get("g", "")
        subject = " ".join(fields.get("subject", "").split())
        text = fields.get("body", "")
        refs = " ".join(r for r in fields.get("refs", "").split()
                        if re.fullmatch(r"<[^<>\s]+>", r))
        if not subject or not text.strip():
            self.compose_page(account, fields, "Please write a subject and a message.")
            return
        if not re.fullmatch(r"[\x21-\x7e]+", group):
            self.missing(account)
            return
        def status_of(client):
            status, body = client.cmd("LIST ACTIVE " + group, multiline=True)
            rows = [line.split() for line in body] if status.startswith("215") else []
            return next((row[3] for row in rows if len(row) > 3 and row[0] == group), "")
        moderated = self.server.node.reading(account, status_of) == "m"
        msgid = self.msgid(account)
        extra, body = body_lines(text)
        lines = (header_value("From", self.sender(account)) + ["Newsgroups: " + group] +
                 header_value("Subject", subject) + ["Message-ID: " + msgid] +
                 (["References: " + refs] if refs else []) + extra + [""] + body)
        self.submit(account, sid, {"kind": "post", "group": group, "message_id": msgid,
                                   "lines": lines, "subject": subject, "moderated": moderated,
                                   "back": href("/g", name=group)})

    def submit(self, account, sid: str, record: dict):
        """Record the exact article, then POST it once. The node's answer is final."""
        state = account.state
        with account.lock:
            if state.record(sid) is not None:
                self.redirect(href("/sent", id=sid))
                return
            state.begin(sid, record)
            result = self.server.node.posting(account, record["lines"], record["message_id"])
            state.finish(sid, outcome=result.word, detail=result.detail,
                         status_lines=result.status_lines)
        if result.word == ACCEPTED and record["kind"] == "post":
            self.mark_own(account, record["group"], record["message_id"])
        self.redirect(href("/sent", id=sid))

    def mark_own(self, account, group: str, msgid: str) -> None:
        """What you wrote is not news to you: the node's number for it, marked read."""
        def query(client):
            if group_line(client, group)[0] is None:
                return None
            status = client.cmd("STAT " + msgid)[0]
            return fn_client.number(status.split()[1]) if status.startswith("223") else None
        try:
            number = self.server.node.reading(account, query)
        except fn_client.Stop:
            return
        if number:
            account.state.mark(group, [number])

    def sent_page(self, account):
        sid = self.query().get("id", "")
        record = account.state.record(sid) if re.fullmatch(r"[0-9a-f]{24}", sid) else None
        if record is None:
            self.page("Not found", "<h1>We have no record of that</h1>", account, code=404)
            return
        self.page("Sent", self.outcome(account, record), account)

    def outcome(self, account, record: dict) -> str:
        kind, word = record["kind"], record["outcome"]
        said = " ".join(line for line in record.get("status_lines", [])[-1:]) or \
            record.get("detail", "")
        settled = next((c for c in reversed(record.get("checks", []))
                        if c.get("settled") in ("accepted", "refused")), None)
        details = ("<details><summary>What the server said</summary><p class='said'>%s</p>"
                   "%s</details>"
                   % (e(said), "".join("<p class='said'>Checked %s: %s</p>"
                                       % (e(c["at"]), e(c["said"]))
                                       for c in record.get("checks", []))))
        back = "<p><a class='button' href='%s'>Back to %s</a></p>" % (
            e(record.get("back", "/")), e(record.get("group", "the groups")))
        if word == UNSENT:
            return ("<h1>Not sent</h1><p class='note no' role='alert'><strong>We couldn't "
                    "reach the server, so nothing was sent.</strong> You can try again; it "
                    "sends the very same thing.</p><form method='post' action='/check'>%s"
                    "<input type='hidden' name='id' value='%s'><button type='submit'>Try "
                    "again</button></form>%s%s"
                    % (self.token(account), e(record["sid"]), back, details))
        if kind == "remove":
            return self.removal_outcome(account, record, details, back)
        verb = {"post": "post", "approve": "approval"}[kind]
        if word == ACCEPTED or (settled and settled["settled"] == "accepted"):
            if kind == "approve":
                head = "<p class='note ok' role='status'><strong>Approved.</strong> The post " \
                       "is now published.</p>"
            elif record.get("moderated"):
                head = "<p class='note ok' role='status'><strong>Sent!</strong> A moderator " \
                       "will look at it before it appears.</p>"
            else:
                head = "<p class='note ok' role='status'><strong>Posted!</strong> Your post " \
                       "is up.</p>"
            if settled and word != ACCEPTED:
                head += "<p class='soft small'>We checked, and it did go through.</p>"
            return "<h1>Done</h1>" + head + back + details
        if word == REFUSED or (settled and settled["settled"] == "refused"):
            again = ""
            if kind == "post":
                again = ("<form method='post' action='/edit'>%s<input type='hidden' name='id' "
                         "value='%s'><p><button type='submit'>Edit and try again</button></p>"
                         "</form>" % (self.token(account), e(record["sid"])))
            return ("<h1>Not posted</h1><p class='note no' role='alert'><strong>The server "
                    "didn't take this %s.</strong> Nothing was published.</p>"
                    "<p>The reason it gave:</p><p class='said'>%s</p>%s%s"
                    % (verb, e(said), again, back))
        return ("<h1>Not sure yet</h1><p class='note maybe' role='status'><strong>We couldn't "
                "tell whether your %s went through.</strong> Please don't write it again. "
                "Press the button to find out; it sends the very same %s, so it can never "
                "appear twice.</p><form method='post' action='/check'>%s"
                "<input type='hidden' name='id' value='%s'><button type='submit'>Check "
                "now</button></form>%s%s"
                % (verb, verb, self.token(account), e(record["sid"]), back, details))

    def edit_again(self, account, fields):
        """A refused post's fields in a new form (a new Message-ID when posted)."""
        record = account.state.record(fields.get("id", "")) \
            if re.fullmatch(r"[0-9a-f]{24}", fields.get("id", "")) else None
        if record is None or record.get("kind") != "post" or record["outcome"] != REFUSED:
            self.redirect("/")
            return
        refs = next((line.split(":", 1)[1].strip() for line in record["lines"]
                     if line.lower().startswith("references:")), "")
        self.compose_page(account, {"g": record["group"], "subject": record.get("subject", ""),
                                    "refs": refs, "body": article_text(parse_article(
                                        record["lines"])), "sid": secrets.token_hex(12)})

    def check(self, account, fields):
        """NNT-019: re-send the same article under the same Message-ID; record beside."""
        sid = fields.get("id", "")
        state = account.state
        record = state.record(sid) if re.fullmatch(r"[0-9a-f]{24}", sid) else None
        if record is None:
            self.redirect("/")
            return
        if record["outcome"] == UNSENT:
            with account.lock:
                result = self.server.node.posting(account, record["lines"],
                                                  record["message_id"])
                state.finish(sid, outcome=result.word, detail=result.detail,
                             status_lines=result.status_lines)
        elif record["outcome"] == UNCERTAIN:
            with account.lock:
                answer = self.server.node.posting(account, record["lines"],
                                                  record["message_id"])
                settled = fn_client.reconciliation(answer)
                checks = record.get("checks", []) + [{
                    "at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
                    "settled": settled.word,
                    "said": (answer.status_lines[-1:] or [answer.detail])[0]}]
                state.finish(sid, checks=checks)
        self.redirect(href("/sent", id=sid))

    # ---------------------------------------------------------- removing

    def remove_page(self, account):
        q = self.query()
        msgid, group = q.get("id", ""), q.get("g", "")
        if account.state.my_post(msgid) is None:
            self.page("Not yours", "<h1>You can only remove posts you wrote here</h1>",
                      account, code=404)
            return
        self.page("Remove my post",
                  "<h1>Remove your post?</h1><p>It will disappear from this server for "
                  "everyone. Copies other servers already have may stay there.</p>"
                  "<form method='post' action='/remove'>%s<input type='hidden' name='id' "
                  "value='%s'><input type='hidden' name='g' value='%s'>"
                  "<input type='hidden' name='sid' value='%s'>"
                  "<div class='actions'><button class='danger' type='submit'>Remove it</button>"
                  "<a class='button quiet' href='%s'>Keep it</a></div></form>"
                  % (self.token(account), e(msgid), e(group), secrets.token_hex(12),
                     e(href("/t", g=group, n=q.get("n")) if q.get("n") else
                       href("/g", name=group))), account)

    def remove(self, account, fields):
        msgid, group, sid = fields.get("id", ""), fields.get("g", ""), fields.get("sid", "")
        target = account.state.my_post(msgid)
        if target is None or not re.fullmatch(r"[0-9a-f]{24}", sid):
            self.redirect("/")
            return
        newsgroups = next((line.split(":", 1)[1].strip() for line in target["lines"]
                           if line.lower().startswith("newsgroups:")), group)
        cancel = self.msgid(account)
        # RFC 5537 section 5.3; the node decides whether this login's cancel withdraws
        # the target (SEC-006: the same account; books/control-authority.lisp).
        lines = (header_value("From", self.sender(account)) + ["Newsgroups: " + newsgroups,
                 "Subject: cmsg cancel " + msgid, "Message-ID: " + cancel,
                 "Control: cancel " + msgid, "", "cancel"])
        self.submit(account, sid, {"kind": "remove", "group": group, "message_id": cancel,
                                   "target": msgid, "lines": lines,
                                   "back": href("/g", name=group)})

    def removal_outcome(self, account, record, details, back) -> str:
        word = record["outcome"]
        settled = any(c.get("settled") == "accepted" for c in record.get("checks", []))
        if word == REFUSED:
            return ("<h1>Not removed</h1><p class='note no' role='alert'><strong>The server "
                    "didn't take the removal.</strong> Your post is still there.</p>"
                    "<p class='said'>%s</p>%s" % (e(record.get("detail", "")), back))
        if word != ACCEPTED and not settled:
            return ("<h1>Not sure yet</h1><p class='note maybe' role='status'><strong>We "
                    "couldn't tell whether the removal went through.</strong></p>"
                    "<form method='post' action='/check'>%s<input type='hidden' name='id' "
                    "value='%s'><button type='submit'>Check now</button></form>%s%s"
                    % (self.token(account), e(record["sid"]), back, details))

        def query(client):
            return client.cmd("STAT " + record["target"])[0]
        status = self.server.node.reading(account, query)
        if status.startswith("430"):
            return ("<h1>Removed</h1><p class='note ok' role='status'><strong>Your post has "
                    "been removed</strong> from this server.</p>%s%s" % (back, details))
        return ("<h1>Still there</h1><p class='note no' role='alert'><strong>The server took "
                "the removal but still shows the post.</strong></p><p class='said'>%s</p>%s%s"
                % (e(status), back, details))

    # ---------------------------------------------------------- moderation

    def approve(self, account, fields):
        group, number = fields.get("g", ""), fn_client.number(fields.get("n", ""))

        def query(client):
            if group_line(client, group)[0] is None or not number:
                return None
            got, body = client.cmd("ARTICLE %d" % number, multiline=True)
            return body if got.startswith("220") else None
        lines = self.server.node.reading(account, query)
        if lines is None or not is_envelope(parse_article(lines)):
            self.missing(account)
            return
        # RFC 5537 section 3.5.1: the envelope's body is the proto-article; the
        # moderator posts it with Approved (the node checks the login moderates it).
        proto = lines[lines.index("") + 1:]
        cut = proto.index("") if "" in proto else len(proto)
        msgid = next((line.split(":", 1)[1].strip() for line in proto[:cut]
                      if line.lower().startswith("message-id:")), "")
        approved = ["Approved: %s@%s" % (account.user, self.server.mail_domain)] + proto
        sid = fields.get("sid", "")
        if not re.fullmatch(r"[0-9a-f]{24}", sid):
            self.redirect("/")
            return
        self.submit(account, sid, {"kind": "approve", "group": group, "message_id": msgid,
                                   "lines": approved, "back": href("/g", name=group)})

    # ---------------------------------------------------------- settings

    def me_page(self, account, message=""):
        state = account.state
        posts = [r for r in state.records() if r.get("kind") == "post"][:20]
        rows = "".join(
            "<li><div class='row'><a class='title' href='%s'>%s</a><span class='pill'>%s"
            "</span></div><div class='soft small'>%s · %s</div></li>"
            % (e(href("/sent", id=r["sid"])), e(r.get("subject") or "(no subject)"),
               e({"accepted": "posted", "refused": "not posted"}.get(r["outcome"], "not sure")),
               e(r.get("group", "")), e(r.get("at", "")))
            for r in posts)
        self.page("You",
                  "<h1>You</h1><p>You're signed in as <strong>%s</strong>.</p>%s"
                  "<form method='post' action='/me'>%s<label for='name'>Your name on posts"
                  "</label><input type='text' id='name' name='name' value='%s' maxlength='80'>"
                  "<p class='soft small'>People see this next to what you write. Your posts "
                  "are sent as %s.</p><button type='submit'>Save</button></form>"
                  "<h2>What you sent from here</h2>%s"
                  % (e(account.user), ("<p class='note ok'>%s</p>" % e(message)) if message
                     else "", self.token(account), e(state.data.get("name", "")),
                     e(self.sender(account)),
                     "<ul class='list'>%s</ul>" % rows if rows else "<p>Nothing yet.</p>"),
                  account)

    def save_me(self, account, fields):
        name = " ".join(fields.get("name", "").split())[:80]
        name = "".join(c for c in name if c.isprintable())
        account.state.set_name(name)
        self.me_page(account, "Saved.")


# ------------------------------------------------------------------ main


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--node", required=True, help="the node's NNTP address, HOST:PORT")
    parser.add_argument("--tls-cert", help="the node's certificate (or its CA) to verify")
    parser.add_argument("--plain-node", action="store_true",
                        help="no TLS to the node: loopback development only")
    parser.add_argument("--listen", default="127.0.0.1:8920", help="HOST:PORT to serve on")
    parser.add_argument("--https-cert", help="certificate for the browser side")
    parser.add_argument("--https-key", help="its key")
    parser.add_argument("--state", required=True, help="directory for read marks and records")
    parser.add_argument("--site", default="Our news", help="the name shown on every page")
    parser.add_argument("--mail-domain", help="domain for From and Message-ID (default: node host)")
    parser.add_argument("--timeout", type=float, default=30.0)
    return parser


def main(argv=None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    host_text, port_text = fn_client.split_node(args.node)
    if not host_text or not (port_text or "").isdigit():
        parser.error("--node must be HOST:PORT")
    args.host, args.port = host_text, int(port_text)
    host, _, port = args.listen.rpartition(":")
    host = host.strip("[]") or "127.0.0.1"
    loopback = host in ("127.0.0.1", "::1", "localhost")
    if args.plain_node and args.host not in ("127.0.0.1", "::1", "localhost"):
        parser.error("--plain-node is for a loopback node only; use --tls-cert")
    if not args.plain_node and not args.tls_cert:
        parser.error("--tls-cert is required: the node's certificate is verified")
    if bool(args.https_cert) != bool(args.https_key):
        parser.error("--https-cert and --https-key go together")
    if not args.https_cert and not loopback:
        parser.error("passwords cross this listener: serve HTTPS (--https-cert/--https-key) "
                     "or listen on loopback behind a TLS proxy")
    state = Path(args.state).expanduser()
    state.mkdir(mode=0o700, parents=True, exist_ok=True)
    os.chmod(state, 0o700)
    node = Node(args)
    server = Reader((host, int(port)), node, state, site=args.site,
                    mail_domain=args.mail_domain or args.host, secure=bool(args.https_cert))
    if args.https_cert:
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.minimum_version = ssl.TLSVersion.TLSv1_2
        context.load_cert_chain(args.https_cert, args.https_key)
        server.socket = context.wrap_socket(server.socket, server_side=True,
                                            do_handshake_on_connect=False)
    print("fn reader: %s for %s; open %s://%s:%s/" % (
        node.name, args.site, "https" if args.https_cert else "http", host,
        server.server_address[1]), flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())

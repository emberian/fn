#!/usr/bin/env python3
"""Loopback human reader/composer for an fn NNTP node.

This is a separate client process. It never opens the Store, changes fn's
state directly, or treats viewing an article as a processing acknowledgement.
Use an SSH loopback forward for a remote node; the HTTP listener and its NNTP
target are both restricted to loopback for this first interface.
"""
from __future__ import annotations

import argparse
import html
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import hmac
import secrets
from types import SimpleNamespace
from urllib.parse import parse_qs, urlencode, urlsplit

import fn_client
from nntp_session import Disconnected, Session

MAX_LINE = 8192
MAX_BLOCK = 262144
MAX_BLOCK_LINES = 2048
MAX_FORM = 24576
MAX_BODY = 16384
MAX_RECENT = 40


class BoundedSession(Session):
    """The existing NNTP wire client with finite reader allocation."""

    def line(self) -> str:
        while b"\r\n" not in self.buf:
            if len(self.buf) > MAX_LINE:
                raise Disconnected("NNTP line exceeds the web client limit")
            chunk = self.sock.recv(4096)
            if not chunk:
                raise Disconnected("the node closed the connection")
            self.buf += chunk
        out, self.buf = self.buf.split(b"\r\n", 1)
        if len(out) > MAX_LINE:
            raise Disconnected("NNTP line exceeds the web client limit")
        return out.decode("utf-8", "replace")

    def block(self) -> list[str]:
        lines, size = [], 0
        while True:
            one = self.line()
            if one == ".":
                return lines
            size += len(one.encode("utf-8")) + 2
            if size > MAX_BLOCK or len(lines) >= MAX_BLOCK_LINES:
                raise Disconnected("NNTP block exceeds the web client limit")
            lines.append(one[1:] if one.startswith("..") else one)


class FormErrors:
    def error(self, message: str) -> None:
        raise ValueError(message)


class Backend:
    def __init__(self, args, user: str, password: str):
        self.args, self.user, self.password = args, user, password

    def using(self, operation):
        client = fn_client.Client(self.args, self.user, self.password,
                                  session_factory=BoundedSession)
        try:
            client.open()
            return operation(client)
        finally:
            client.close()

    def groups(self):
        return self.using(lambda client: client.groups())

    def recent(self, group: str):
        def query(client):
            status, _ = client.cmd("GROUP " + group)
            if not status.startswith("211"):
                return fn_client.Result(fn_client.REFUSED, status, {}, "")
            fields = status.split()
            low = fn_client.number(fields[2]) if len(fields) > 2 else None
            high = fn_client.number(fields[3]) if len(fields) > 3 else None
            if low is None or high is None or high < 0:
                raise fn_client.Stop(fn_client.UNCERTAIN, "invalid GROUP range: " + status)
            start = max(low, high - MAX_RECENT + 1)
            if start > high:
                rows = []
            else:
                overview, body = client.cmd("OVER %d-%d" % (start, high), multiline=True)
                if overview.startswith("224"):
                    rows = []
                    for line in body:
                        parts = line.split("\t")
                        number = fn_client.number(parts[0]) if parts else None
                        if number is None or not start <= number <= high:
                            continue
                        rows.append({"number": number,
                                     "subject": parts[1] if len(parts) > 1 else "(no subject)",
                                     "from": parts[2] if len(parts) > 2 else "",
                                     "date": parts[3] if len(parts) > 3 else "",
                                     "message_id": parts[4] if len(parts) > 4 else "",
                                     "references": parts[5] if len(parts) > 5 else ""})
                elif overview[:3] in ("420", "423"):
                    rows = []
                else:
                    return fn_client.Result(fn_client.REFUSED, overview, {}, "")
            return fn_client.Result(fn_client.DONE, status,
                                    {"group": group, "rows": rows, "low": low,
                                     "high": high}, "")
        return self.using(query)

    def article(self, group: str, number: int):
        return self.using(lambda client: client.show(str(number), group))

    def post(self, group: str, subject: str, sender: str, references: str,
             body: str):
        form = SimpleNamespace(group=group, subject=subject, sender=sender,
                               references=references, message_id="", body_file="",
                               host=self.args.host)
        lines, msgid = fn_client.compose(form, self.user, FormErrors(), body)
        try:
            return self.using(lambda client: client.post(group, lines, msgid))
        except fn_client.Stop as exc:
            # A connection failure before POST still has a stable identifier
            # for later settlement. Keep it through the HTTP boundary.
            return fn_client.Result(exc.word, exc.detail,
                                    {"message_id": msgid}, "")


def e(value) -> str:
    return html.escape(str(value if value is not None else ""), quote=True)


def href(path: str, **parameters) -> str:
    return path + ("?" + urlencode(parameters) if parameters else "")


def group_token(value: str) -> bool:
    return bool(value) and len(value) <= 240 and all(
        c.isascii() and (c.isalnum() or c in ".-_+") for c in value)


def depth_of(row: dict, by_id: dict, seen=None) -> int:
    seen = set() if seen is None else seen
    msgid = row["message_id"]
    if msgid in seen:
        return 0
    refs = row["references"].split()
    parent = next((by_id[ref] for ref in reversed(refs)
                   if ref in by_id and ref != msgid), None)
    return min(4, 1 + depth_of(parent, by_id, seen | {msgid})) if parent else 0


STYLE = """
:root { color-scheme: light; font-family: system-ui, sans-serif; background:#f5f3eb; color:#172725 }
body { max-width: 940px; margin: 0 auto; padding: 1.5rem 1rem 5rem; line-height:1.5 }
header { display:flex; align-items:baseline; justify-content:space-between; border-bottom:2px solid #214e43; margin-bottom:1.5rem }
h1,h2 { line-height:1.2; letter-spacing:-.03em } h1 { font-size:2rem; margin:.5rem 0 } h2 { font-size:1.45rem }
a { color:#145f50; text-decoration-thickness:1px; text-underline-offset:.17em }
a:hover { color:#922e24 } nav a { margin-right:1rem }
.card, article { background:#fffefa; border:1px solid #cbd5cd; border-radius:12px; padding:1rem 1.2rem; margin:.7rem 0; box-shadow:0 2px 5px #193d2b0d }
.meta { color:#52645d; font-size:.88rem; overflow-wrap:anywhere }
.badge { display:inline-block; border-radius:100px; padding:.15rem .6rem; font-size:.8rem; background:#e2efe7; color:#144d3d }
.accepted { background:#daf1df } .refused { background:#fae0d9 } .uncertain { background:#fff0be }
.thread { border-left:3px solid #b7d5c6 } pre { white-space:pre-wrap; overflow-wrap:anywhere; font-family:ui-monospace, monospace }
input,textarea { box-sizing:border-box; width:100%; padding:.7rem; margin:.2rem 0 .9rem; border:1px solid #9cad9e; border-radius:6px; font:inherit; background:#fff }
textarea { min-height:12rem } label { display:block; font-weight:650 }
button,.button { display:inline-block; border:0; border-radius:6px; padding:.65rem 1rem; background:#145f50; color:white; font:inherit; cursor:pointer; text-decoration:none }
button:hover,.button:hover { background:#0b4439 } .muted { color:#52645d }
"""


class Handler(BaseHTTPRequestHandler):
    server: "WebServer"

    def setup(self):
        super().setup()
        self.connection.settimeout(15)

    def log_message(self, *_args) -> None:
        # Paths contain article identifiers and form handling may carry private
        # content. The local UI does not put requests into access logs.
        pass

    def page(self, title: str, content: str, status: int = 200):
        page = ("<!doctype html><html lang='en'><meta charset='utf-8'>"
                "<meta name='viewport' content='width=device-width,initial-scale=1'>"
                "<title>" + e(title) + " · fn</title><style>" + STYLE + "</style>"
                "<body><header><h1><a href='/'>fn / news</a></h1>"
                "<span class='muted'>local reader</span></header>" + content + "</body></html>")
        encoded = page.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(encoded)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("Referrer-Policy", "no-referrer")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Security-Policy", "default-src 'none'; style-src 'unsafe-inline'; form-action 'self'; base-uri 'none'; frame-ancestors 'none'")
        self.end_headers()
        self.wfile.write(encoded)

    def valid_host(self) -> bool:
        return self.headers.get("Host") == "127.0.0.1:%d" % self.server.server_port

    def get_parameters(self):
        if len(self.path) > 2048:
            raise ValueError("request URL is too long")
        parts = urlsplit(self.path)
        return parts.path, {k: v[0] for k, v in parse_qs(parts.query).items()}

    def outcome(self, word: str, detail: str, msgid: str = ""):
        link = ("<p><a href='" + e(href("/find", id=msgid)) +
                "'>Check this Message-ID</a></p>") if msgid else ""
        self.page(word.title(), "<div class='card'><span class='badge " + e(word) +
                  "'>" + e(word) + "</span><h2>" + e(detail) + "</h2>" +
                  ("<p>Message-ID: <code>" + e(msgid) + "</code></p>" if msgid else "") +
                  link + "</div>", 200 if word in ("done", "accepted") else 503)

    def run_backend(self, operation):
        try:
            return operation()
        except fn_client.Stop as exc:
            self.outcome(exc.word, exc.detail)
        except (OSError, Disconnected) as exc:
            self.outcome(fn_client.UNCERTAIN, "The NNTP connection failed: " + str(exc))
        return None

    def do_GET(self):
        if not self.valid_host():
            self.send_error(400)
            return
        try:
            path, values = self.get_parameters()
            if path == "/":
                result = self.run_backend(self.server.backend.groups)
                if result is None:
                    return
                if result.word != fn_client.DONE:
                    self.outcome(result.word, result.detail)
                    return
                cards = "".join("<article><h2><a href='" + e(href("/g", name=row["group"])) +
                                "'>" + e(row["group"]) + "</a></h2><p class='meta'>" +
                                e(row["first"]) + "–" + e(row["last"]) +
                                " · " + e(row["status"]) + "</p></article>"
                                for row in result.data["groups"])
                self.page("Groups", "<h2>Groups</h2>" + (cards or "<p>No groups are served.</p>"))
            elif path == "/g":
                group = values.get("name", "")
                if not group_token(group):
                    raise ValueError("invalid group name")
                result = self.run_backend(lambda: self.server.backend.recent(group))
                if result is None:
                    return
                if result.word != fn_client.DONE:
                    self.outcome(result.word, result.detail)
                    return
                rows = result.data["rows"]
                by_id = {row["message_id"]: row for row in rows if row["message_id"]}
                cards = "".join("<article class='thread' style='margin-left:" +
                                str(depth_of(row, by_id) * 18) + "px'><h2><a href='" +
                                e(href("/a", group=group, number=row["number"])) + "'>" +
                                e(row["subject"]) + "</a></h2><p class='meta'>" +
                                e(row["from"]) + " · " + e(row["date"]) +
                                " · #" + e(row["number"]) + "</p></article>"
                                for row in rows)
                self.page(group, "<nav><a href='/'>Groups</a><a href='" +
                          e(href("/compose", group=group)) + "'>Write a post</a></nav>"
                          "<h2>" + e(group) + "</h2><p class='muted'>Recent articles · local numbers</p>" +
                          (cards or "<p>No articles in the recent window.</p>"))
            elif path == "/a":
                group, raw = values.get("group", ""), values.get("number", "")
                if not group_token(group) or not raw.isascii() or not raw.isdecimal() or len(raw) > 10:
                    raise ValueError("invalid article address")
                number = int(raw)
                if number < 1:
                    raise ValueError("invalid article number")
                result = self.run_backend(lambda: self.server.backend.article(group, number))
                if result is None:
                    return
                if result.word != fn_client.DONE:
                    self.outcome(result.word, result.detail)
                    return
                one = result.data["articles"][0]
                fields = one["headers"]
                first = lambda name: fn_client.first(fields, name) or ""
                present = bool(first("fn-statement"))
                provenance = ("<p><span class='badge'>Authorship evidence: " +
                              ("FN-Statement present; not verified here" if present else
                               "no FN-Statement in this article") + "</span></p>"
                              "<p class='meta'>From header (claimed): " + e(first("from")) +
                              "<br>Path: " + e(first("path") or "not supplied") +
                              "<br>Injection-Info: " + e(first("injection-info") or "not supplied") +
                              "<br>Injection-Date: " + e(first("injection-date") or "not supplied") +
                              "</p><p class='muted'>Viewing does not acknowledge application processing.</p>")
                self.page(first("subject") or "Article", "<nav><a href='" +
                          e(href("/g", name=group)) + "'>" + e(group) + "</a><a href='" +
                          e(href("/compose", group=group, reply=number)) + "'>Reply</a></nav>"
                          "<article><h2>" + e(first("subject") or "(no subject)") +
                          "</h2><p class='meta'>" + e(one["message_id"]) +
                          " · local #" + e(number) + "</p>" + provenance +
                          "<pre>" + e("\n".join(one["body"])) + "</pre></article>")
            elif path == "/compose":
                group = values.get("group", "")
                if not group_token(group):
                    raise ValueError("invalid group name")
                subject, references = "", ""
                if "reply" in values:
                    raw = values["reply"]
                    if not raw.isascii() or not raw.isdecimal() or len(raw) > 10 or int(raw) < 1:
                        raise ValueError("invalid reply number")
                    result = self.run_backend(lambda: self.server.backend.article(group, int(raw)))
                    if result is None:
                        return
                    if result.word != fn_client.DONE:
                        self.outcome(result.word, result.detail)
                        return
                    fields = result.data["articles"][0]["headers"]
                    old_subject = fn_client.first(fields, "subject") or ""
                    subject = old_subject if old_subject.lower().startswith("re:") else "Re: " + old_subject
                    msgid = fn_client.first(fields, "message-id") or ""
                    references = ((fn_client.first(fields, "references") or "") + " " +
                                  msgid).strip()
                    if len(references) > 800:
                        references = msgid
                form = ("<form method='post' action='/post'><input type='hidden' name='csrf' value='" +
                        e(self.server.token) + "'><input type='hidden' name='group' value='" + e(group) +
                        "'><input type='hidden' name='references' value='" + e(references) +
                        "'><label>Subject<input name='subject' maxlength='240' required value='" +
                        e(subject[:240]) + "'></label><label>From (optional)<input name='sender' maxlength='240' value='" +
                        e(self.server.backend.user) + "'></label><label>Message<textarea name='body' maxlength='16384' required></textarea></label>"
                        "<button>Post to " + e(group) + "</button></form>")
                self.page("Compose", "<nav><a href='" + e(href("/g", name=group)) +
                          "'>" + e(group) + "</a></nav><h2>Write a post</h2>" + form)
            elif path == "/find":
                msgid = values.get("id", "")
                if not (len(msgid) <= 250 and msgid.startswith("<") and msgid.endswith(">")
                        and "\r" not in msgid and "\n" not in msgid):
                    raise ValueError("invalid Message-ID")
                result = self.run_backend(lambda: self.server.backend.using(
                    lambda client: client.show(msgid, "")))
                if result is None:
                    return
                self.outcome(result.word, result.detail, msgid)
            else:
                self.page("Not found", "<p>Page not found.</p>", 404)
        except ValueError as exc:
            self.page("Invalid request", "<p>" + e(exc) + "</p>", 400)

    def do_POST(self):
        if not self.valid_host() or self.path != "/post":
            self.send_error(400)
            return
        expected = "http://127.0.0.1:%d" % self.server.server_port
        if self.headers.get("Origin") != expected:
            self.page("Refused", "<p>Form origin was not this local reader.</p>", 403)
            return
        try:
            length = int(self.headers.get("Content-Length", "-1"))
            if not 0 <= length <= MAX_FORM:
                raise ValueError("form is too large")
            raw = self.rfile.read(length)
            values = {k: v[0] for k, v in parse_qs(raw.decode("utf-8", "strict"),
                                                    keep_blank_values=True,
                                                    max_num_fields=16).items()}
            if not hmac.compare_digest(values.get("csrf", ""), self.server.token):
                self.page("Refused", "<p>Form token is invalid.</p>", 403)
                return
            group, subject = values.get("group", ""), values.get("subject", "")
            sender, references, body = (values.get("sender", ""),
                                        values.get("references", ""), values.get("body", ""))
            if (not group_token(group) or not subject or len(subject) > 240 or
                    len(sender) > 240 or len(references) > 800 or len(body.encode()) > MAX_BODY or
                    not body.strip() or any("\r" in x or "\n" in x
                                            for x in (subject, sender, references)) or
                    any(len(line.encode()) > 998 for line in body.splitlines())):
                raise ValueError("post fields are invalid or too large")
            result = self.run_backend(lambda: self.server.backend.post(
                group, subject, sender, references, body))
            if result is not None:
                self.outcome(result.word, result.detail, result.data.get("message_id", ""))
        except (ValueError, UnicodeDecodeError) as exc:
            self.page("Invalid post", "<p>" + e(exc) + "</p>", 400)


class WebServer(ThreadingHTTPServer):
    daemon_threads = True

    def __init__(self, port: int, backend: Backend):
        self.backend = backend
        self.token = secrets.token_urlsafe(32)
        super().__init__(("127.0.0.1", port), Handler)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--node", default="127.0.0.1:1119")
    parser.add_argument("--port", type=int, default=8919, help="loopback HTTP port")
    parser.add_argument("--cafile")
    parser.add_argument("--plain", action="store_true")
    parser.add_argument("--credentials")
    parser.add_argument("--timeout", type=float, default=15.0)
    args = parser.parse_args(argv)
    fn_client.resolve(args, parser)
    if args.host not in ("127.0.0.1", "::1"):
        parser.error("the initial web client requires a loopback NNTP target")
    if not 0 <= args.port < 65536 or not 0 < args.timeout <= 60:
        parser.error("invalid HTTP port or timeout")
    user, password = ("", "") if args.plain else fn_client.credentials(args, parser)
    if not args.plain and not (user and password):
        parser.error("set client credentials or pass a mode-0600 --credentials file")
    with WebServer(args.port, Backend(args, user, password)) as server:
        print("fn web client: http://127.0.0.1:%d/" % server.server_port, flush=True)
        server.serve_forever()


if __name__ == "__main__":
    main()

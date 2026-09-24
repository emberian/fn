"""A fake node that speaks just enough NNTP for the two client-side tools.

It wraps its socket in REAL TLS with a certificate `make_pair` writes with
openssl, so `tools/node_probe.py` and `tools/fn_client.py` are exercised over
a handshake rather than over a mock.  It is a fake and not a model: the codes
and the wording it sends were read off the books that own them --
`books/nntp-responses.lisp` for the LIST ACTIVE line (`name high low y`),
`books/nntp-auth.lisp` for `480 authentication required`, `483` and
`440 posting not permitted for this principal`, `books/nntp-post.lisp` for the
two 441 lines that keep a refusal and an uncertain outcome apart -- but nothing
here is derived from those books, and a test against this fake says what the
client does with an answer, never that the node gives it.

Every switch names one thing about a node a client has to survive:

    protected_only      AUTHINFO is 483 until the TLS layer is up
    require_auth        the reader commands are 480 until the login
    offer_starttls      STARTTLS is advertised and answered at all
    accept_post         this principal may POST, or gets 440
    fail_article        one number answers 403 instead of the article
    echo_password       the login refusal quotes the password back
    refuse_post         the article is taken and then refused, 441
    refusal             which 441 refusal line that is
    uncertain_post      the article is taken and the outcome is uncertain, 441
    drop_after_article  the article is taken and the socket closes: no reply
    drop_before_greeting  the connection is accepted and closed, unspoken
    close_after_382     STARTTLS is agreed to and the socket then closes
    host                where it listens, so `::1` can be reached as `::1`

The last two arrived from the frozen 915d5c72 node on 2026-09-22
(planning/evidence/fn-client-915-2026-09-22.md).  `drop_before_greeting` is
what an `ssh -L` forwarder does once the owner behind it has stopped: the
connection is accepted on this side and closed with nothing said, which is
not the `ECONNREFUSED` the earlier "not listening" case produced.  `host` is
there because `[listener] host` admits `::1` (docs/operator.md) and no test
had ever named a node that way.  That node also answered `101 capability
list follows`, `205 closing connection` and `423 no article with that
number` where this fake says something shorter; the wording is left alone so
nothing here can be mistaken for the node's own voice.
"""
import socket
import ssl
import subprocess
import threading


class FakeNode(threading.Thread):
    """Serves one connection after another until stopped."""

    def __init__(self, cert, key, protected_only=True, password="right", accept_post=True,
                 offer_starttls=True, require_auth=True, refuse_post=False,
                 uncertain_post=False, drop_after_article=False, fail_article=None,
                 echo_password=False, groups=("fn.agents",), drop_before_greeting=False,
                 host="127.0.0.1", refusal="441 posting failed; the article was refused",
                 close_after_382=False):
        super().__init__(daemon=True)
        self.context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        self.context.load_cert_chain(cert, key)
        self.protected_only = protected_only
        self.password = password
        self.accept_post = accept_post
        self.offer_starttls = offer_starttls
        self.require_auth = require_auth
        self.refuse_post = refuse_post
        self.refusal = refusal
        self.uncertain_post = uncertain_post
        self.drop_after_article = drop_after_article
        self.drop_before_greeting = drop_before_greeting
        self.close_after_382 = close_after_382
        self.fail_article = fail_article
        self.echo_password = echo_password
        self.articles = {}
        # Optional literal HDR :fn-verified values used by reader-client tests.
        self.verdicts = {}
        self.numbers = {name: {} for name in groups}
        self.host = host
        family = socket.AF_INET6 if ":" in host else socket.AF_INET
        self.listener = socket.socket(family)
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind((host, 0))
        self.listener.listen(4)
        self.port = self.listener.getsockname()[1]
        self.stopping = False
        self.seen = []

    def stop(self):
        self.stopping = True
        self.listener.close()

    # ---- the article table ---------------------------------------------
    #
    # `articles` is keyed by Message-ID, which is what the whole article is;
    # `numbers` maps each group to the local numbers it allocated, which is a
    # different concept and deliberately a different table.

    def inject(self, group, lines):
        """File one article's lines and allocate it a number in one group."""
        msgid = header(lines, "message-id") or "<%d@fake.invalid>" % (len(self.articles) + 1)
        self.articles[msgid] = lines
        table = self.numbers.setdefault(group, {})
        number = max(table, default=0) + 1
        table[number] = msgid
        return number

    def seed(self, group, subject, body, msgid=None, sender="yue <yue@fake.invalid>"):
        msgid = msgid or "<seed-%d@fake.invalid>" % (len(self.articles) + 1)
        return self.inject(group, ["From: " + sender, "Newsgroups: " + group,
                                   "Subject: " + subject, "Message-ID: " + msgid,
                                   "Date: Mon, 21 Sep 2026 00:00:00 +0000", "", body])

    def summary(self, group):
        table = self.numbers.get(group)
        if table is None:
            return None
        if not table:
            return (0, 1, 0)
        return (len(table), min(table), max(table))

    def locate(self, group, token):
        """(number, message-id) for a token that is a number or a Message-ID."""
        if token.startswith("<"):
            for name, table in self.numbers.items():
                for number, msgid in table.items():
                    if msgid == token and (group is None or name == group):
                        return (0 if group is None else number, msgid)
            return (None, token) if token in self.articles else (None, None)
        table = self.numbers.get(group) or {}
        try:
            number = int(token)
        except ValueError:
            return (None, None)
        return (number, table[number]) if number in table else (None, None)

    # ---- the wire -------------------------------------------------------

    def run(self):
        while not self.stopping:
            try:
                conn, _ = self.listener.accept()
            except OSError:
                return
            try:
                self.serve(conn)
            except (OSError, ssl.SSLError):
                pass
            finally:
                try:
                    conn.close()
                except OSError:
                    pass

    def serve(self, conn):
        conn.settimeout(10)
        buf = b""
        tls = False
        authenticated = False
        selected = None

        def line():
            nonlocal buf
            while b"\r\n" not in buf:
                chunk = conn.recv(4096)
                if not chunk:
                    raise OSError("client went away")
                buf += chunk
            out, buf = buf.split(b"\r\n", 1)
            return out.decode()

        def send(text):
            conn.sendall(text.encode() + b"\r\n")

        def block(lines):
            for one in lines:
                send(("." + one) if one.startswith(".") else one)
            send(".")

        def take_article():
            lines = []
            while True:
                one = line()
                if one == ".":
                    return lines
                lines.append(one[1:] if one.startswith("..") else one)

        if self.drop_before_greeting:
            # Accepted and then closed with nothing said.  A forwarder in
            # front of a stopped owner does exactly this, and it is not the
            # refused connection a stopped listener gives.
            conn.close()
            return
        send("200 fake node ready")
        try:
            while True:
                cmd = line()
                self.seen.append(cmd if not cmd.startswith("AUTHINFO PASS") else "AUTHINFO PASS *")
                words = cmd.split()
                verb = words[0].upper() if words else ""
                if verb == "CAPABILITIES":
                    caps = ["VERSION 2", "READER"]
                    if self.accept_post:
                        caps.append("POST")
                    if self.offer_starttls and not tls:
                        caps.append("STARTTLS")
                    if not authenticated and (tls or not self.protected_only):
                        caps.append("AUTHINFO USER")
                    send("101 capabilities")
                    block(caps)
                elif verb == "STARTTLS":
                    if tls or not self.offer_starttls:
                        send("502 already or never")
                        continue
                    send("382 continue with TLS negotiation")
                    if self.close_after_382:
                        return
                    assert buf == b"", "the fake never takes pipelined octets"
                    conn = self.context.wrap_socket(conn, server_side=True)
                    tls = True
                elif verb == "AUTHINFO":
                    if self.protected_only and not tls:
                        send("483 a protected channel is required; use STARTTLS")
                    elif words[1].upper() == "USER":
                        send("381 password required")
                    elif words[1].upper() == "PASS":
                        if " ".join(words[2:]) == self.password:
                            authenticated = True
                            send("281 authentication accepted")
                        elif self.echo_password:
                            # A node that quotes the secret back at the
                            # client.  No fn node does this; a client that
                            # renders whatever it is told has to survive one.
                            send("481 authentication failed for %s" % " ".join(words[2:]))
                        else:
                            send("481 authentication failed")
                    else:
                        send("501 syntax")
                elif self.require_auth and not authenticated and verb in RESTRICTED:
                    # books/nntp-auth.lisp fn-auth-restricted-keywordp: the
                    # command is refused and NOT performed.
                    send("480 authentication required")
                elif verb == "LIST":
                    variant = words[1].upper() if len(words) > 1 else "ACTIVE"
                    if variant != "ACTIVE":
                        send("503 data item not stored")
                        continue
                    send("215 list of active newsgroups follows")
                    block(["%s %d %d y" % (name, self.summary(name)[2], self.summary(name)[1])
                           for name in sorted(self.numbers)])
                elif verb == "GROUP":
                    found = self.summary(words[1]) if len(words) > 1 else None
                    if found is None:
                        send("411 no such newsgroup")
                        continue
                    selected = words[1]
                    send("211 %d %d %d %s" % (found[0], found[1], found[2], selected))
                elif verb in ("ARTICLE", "HEAD", "BODY", "STAT"):
                    token = words[1] if len(words) > 1 else None
                    if token is None:
                        send("420 no current article")
                        continue
                    if not token.startswith("<") and selected is None:
                        send("412 no newsgroup selected")
                        continue
                    number, msgid = self.locate(selected, token)
                    if number is not None and number == self.fail_article:
                        send("403 internal fault")
                        continue
                    if msgid is None or msgid not in self.articles:
                        send("430 no article with that message-id" if token.startswith("<")
                             else "423 no article with that number")
                        continue
                    lines = self.articles[msgid]
                    cut = lines.index("") if "" in lines else len(lines)
                    if verb == "STAT":
                        send("223 %d %s retrieved" % (number or 0, msgid))
                    elif verb == "HEAD":
                        send("221 %d %s" % (number or 0, msgid))
                        block(lines[:cut])
                    elif verb == "BODY":
                        send("222 %d %s" % (number or 0, msgid))
                        block(lines[cut + 1:])
                    else:
                        send("220 %d %s" % (number or 0, msgid))
                        block(lines)
                elif verb in ("OVER", "XOVER"):
                    if selected is None:
                        send("412 no newsgroup selected")
                        continue
                    wanted = in_range(sorted(self.numbers[selected]),
                                      words[1] if len(words) > 1 else "")
                    if not wanted:
                        send("423 no articles in that range")
                        continue
                    send("224 overview information follows")
                    block([self.over_line(selected, number) for number in wanted])
                elif verb == "HDR" and len(words) == 3 and words[1].lower() == ":fn-verified":
                    if not words[2].isascii() or not words[2].isdecimal() or selected is None:
                        send("501 syntax")
                        continue
                    number = int(words[2])
                    msgid = self.numbers.get(selected, {}).get(number)
                    if msgid not in self.articles:
                        send("423 no article with that number")
                        continue
                    send("225 headers follow")
                    block([str(number) + " " +
                           self.verdicts.get(msgid, "absent no-field")])
                elif verb == "POST":
                    if not self.accept_post:
                        send("440 posting not permitted for this principal")
                        continue
                    send("340 send article to be posted")
                    lines = take_article()
                    if self.drop_after_article:
                        # The article text is in; the reply never comes.  A
                        # client cannot tell this from a node that stored it.
                        return
                    if self.refuse_post:
                        send(self.refusal)
                        continue
                    if self.uncertain_post:
                        send("441 posting failed; the outcome is uncertain, do not repost")
                        continue
                    groups = (header(lines, "newsgroups") or "").split(",")
                    for name in [g.strip() for g in groups if g.strip()] or ["fn.agents"]:
                        self.inject(name, lines)
                    send("240 article received OK")
                elif verb == "QUIT":
                    send("205 bye")
                    return
                else:
                    send("500 unknown")
        finally:
            conn.close()

    def over_line(self, group, number):
        # RFC 3977 section 8.3.2 and specs/nntp.md: exactly eight fields, no
        # Xref, the byte and line counts of the retained octets.
        lines = self.articles[self.numbers[group][number]]
        cut = lines.index("") if "" in lines else len(lines)
        return "\t".join([str(number), header(lines, "subject") or "",
                          header(lines, "from") or "", header(lines, "date") or "",
                          header(lines, "message-id") or "",
                          header(lines, "references") or "",
                          str(sum(len(one) + 2 for one in lines)), str(len(lines) - cut - 1)])


RESTRICTED = {"POST", "GROUP", "LISTGROUP", "LIST", "NEXT", "LAST", "ARTICLE", "HEAD",
              "BODY", "STAT", "OVER", "XOVER", "HDR", "XHDR", "XPAT", "NEWGROUPS"}


def header(lines, name):
    for one in lines:
        if one == "":
            return None
        if one.lower().startswith(name + ":"):
            return one.split(":", 1)[1].strip()
    return None


def in_range(numbers, spec):
    """RFC 3977 section 6.1.1.2 ranges: `n`, `n-`, `n-m`, or the whole group."""
    if not spec:
        return numbers
    if "-" not in spec:
        return [n for n in numbers if n == int(spec)]
    low, _, high = spec.partition("-")
    first = int(low)
    last = int(high) if high else max(numbers, default=first)
    return [n for n in numbers if first <= n <= last]


def make_pair(directory):
    cert, key = directory / "cert.pem", directory / "key.pem"
    subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-sha256",
                    "-days", "2", "-subj", "/CN=localhost",
                    "-addext", "subjectAltName=IP:127.0.0.1,DNS:localhost",
                    "-keyout", str(key), "-out", str(cert)],
                   check=True, capture_output=True)
    return cert, key

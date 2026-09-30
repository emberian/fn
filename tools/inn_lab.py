#!/usr/bin/env python3
"""A real INN news server on one side of the wire and the native fn owner on the other.

tools/deploy_gate.py establishes that one commit serves, dies and recovers.
tools/v0_matrix.py puts two fn nodes beside each other.  This is the third
question, and the only one whose answer does not come from our own code: does
fn meet *legacy Usenet* -- InterNetNews, the server most of the remaining
Usenet runs -- and where exactly does it fail to.

The fn side is the saved native image through its public entry
(``packaging/fn-native``), named by ``--native-image``, or the lab does not
run: the development Python reader it fell back to on 2026-09-20 is retired
(decision D07), and a lab that measured it would be measuring something no
node runs.  The INN install is not shipped or torn down: it is the lab.  It
lives at ``--inn-prefix`` (``/tank/fn/inn/<version>`` on hbox), was built from
the release tarball whose sha256 is recorded in ``tests/inn/pin.json``, runs as
the ordinary user on high ports, and stays on the box between runs.  What this
tool ships per run is the fn commit (for the launcher and the lab's drivers)
under ``--lab-root``, with deploy_gate's step accounting and evidence
renderer, reused by subclassing ``DeployGate``, not copied.

A byte-transparent relay (``tap.py``) sits on each of the two transit
connections, fn's feed into innd and INN's innfeed into fn, and logs every
octet both ways.  It is how the record carries the exact reply each server
gave the other: innd and innfeed log counts, not replies.

The rows, in order:

* ``fn-post``         -- an article POSTed to the fn owner (240), read back.
* ``fn-feeds-inn``    -- fn's outbound feed offers it to innd by IHAVE; the
                         reply to the offer and to the article, from the tap.
* ``inn-serves-fn``   -- nnrpd serves that article; its octets against fn's,
                         header by header (RFC 5537 section 3.6 lets a relay
                         change Path and Xref and nothing else).
* ``operator-post``   -- the same, for an article submitted through
                         ``operator post`` rather than POST.
* ``inn-control``     -- IHAVE into innd by hand: 235, then 435 for the same
                         Message-ID, then 437 for a Path naming INN.
* ``innfeed-feeds-fn``-- INN's own innfeed offers that article to fn; fn's
                         replies from the tap, and fn serves it after.
* ``duplicates``      -- a second offer of an article each side holds: 435.
* ``fn-loop``         -- an article whose Path names fn's own path identity,
                         offered to fn: refused, and not served.
* ``fn-term``         -- SIGTERM of the owner, ``recover``, restart, reread:
                         the articles are served byte-identical.
* ``innd-cut``        -- SIGKILL of innd and a restart: its history still
                         refuses both articles as duplicates.

    python3 tools/inn_lab.py HEAD --host hbox --native-image IMG \\
        --native-openssl-prefix /tank/fn/toolchains/openssl-3.5.8

Dry run.  ``--dry-run --home DIR --inn-prefix DIR/fake-inn --native-image
tests/inn_lab_fake/native/fn-host`` runs every script through bash on this
machine with ``HOME`` redirected and no ssh; tests/test_inn_lab.py drives it
against ``tests/inn_lab_fake``, a stand-in INN and a stand-in image whose
replies are that directory's and say nothing whatever about INN or about fn.
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import email.utils
import json
from pathlib import Path
import shlex
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

import deploy_gate                                            # noqa: E402
import farm                                                   # noqa: E402
from deploy_gate import (evidence_path, repo_root, report,    # noqa: E402
                         GROUPS, GateError, Host, LocalHost, SshHost, Step,
                         resolve)

DEFAULT_HOST = "hbox"
DEFAULT_INN_VERSION = "2.7.4"
DEFAULT_INN_ROOT = "/tank/fn/inn"
DEFAULT_LAB_ROOT = "$HOME/fn-inn-lab"
# The port scheme, in one place.  The 114xx decade is this lab's: the deployed
# node has 1119, the v0 matrix 11190/11191 and the other lanes 113xx.  INN's
# own ports keep their last two digits (119 transit, 120 reader), the fn owner
# sits at 90 as it does in the matrix, and the two relays are the ports just
# below INN's, so a stray connection to the wrong one is obvious in a log.
INN_PORT = 11419          # innd: transit (IHAVE/CHECK/TAKETHIS)
NNRPD_PORT = 11420        # nnrpd: the reader daemon, read-back only
INN_SECURITY_PORT = 11421 # optional certificate-verified STARTTLS reader
FN_PORT = 11490           # the native fn owner's listener
TAP_OUT_PORT = 11418      # fn's peer record names this; the relay forwards to innd
TAP_IN_PORT = 11417       # innfeed.conf names this; the relay forwards to fn

INN_PATH_IDENTITY = "inn.hbox.test"
FN_PATH_IDENTITY = "fnA.hbox.test"
# The lab's own hand-made articles originate at a site that is neither server,
# so neither server's loop check fires on them and INN's innfeed offers them on.
LAB_PATH_IDENTITY = "lab.example.invalid"
FN_PEER_NAME = "inn"
GROUP = GROUPS[0]
# RFC 5537 section 3.6: a relaying agent MUST NOT alter anything but these.
RELAY_MAY_CHANGE = ("path", "xref")


def shell_fixture_path(path: str) -> str:
    """Quote a fixture path, retaining only the lab's known HOME prefix expansion."""
    if path.startswith("$HOME/"):
        return '"$HOME"/' + shlex.quote(path[len("$HOME/"):])
    return shlex.quote(path)


def reported_pid(output: str) -> str:
    """The pid a `...-UP pid=$(cat <pidfile>)` step reported, or "".

    An empty pid file (the server is up but has not written one, or writes
    one under another name) used to make this an `IndexError` inside
    `inn_start`, which reaches a caller as a harness crash and a
    `setUpClass` error: indistinguishable from a broken lab.  A pid the lab
    does not know is a recorded gap -- the lab then kills nothing, which is
    the safe direction -- so this answers "" and never raises.
    """
    if "pid=" not in output:
        return ""
    tail = output.split("pid=")[-1].strip().splitlines()
    if not tail:
        return ""
    word = tail[0].split()[0] if tail[0].split() else ""
    return word if word.isdigit() else ""


# Message-IDs carry a per-run tag.  INN's history is deliberately NOT reset
# between runs -- the install is the lab, and a history that survives is what
# the innd-restart control asserts -- so a fixed Message-ID makes the second
# run of the transfer scenario a duplicate of the first.
FED_ID = "<inn-lab-fed-{tag}@example.invalid>"
LOOP_ID = "<inn-lab-loop-{tag}@example.invalid>"
LOOP2_ID = "<inn-lab-loop2-{tag}@example.invalid>"
FN_POST_ID = "<inn-lab-fn-post-{tag}@example.invalid>"
FN_OPERATOR_ID = "<inn-lab-fn-operator-{tag}@example.invalid>"
FN_LOOP_ID = "<inn-lab-fn-loop-{tag}@example.invalid>"
INN_CHECKGROUPS_ID = "<inn-lab-checkgroups-{tag}@example.invalid>"
FN_PROTECTED_ID = "<inn-lab-fn-protected-{tag}@example.invalid>"
FN_FROM_ID = "<inn-lab-fn-from-{tag}@example.invalid>"
FN_PATH_ID = "<inn-lab-fn-path-{tag}@example.invalid>"
FN_STREAM_ID = "<inn-lab-fn-stream-{tag}@example.invalid>"
INN_STREAM_ID = "<inn-lab-inn-stream-{tag}@example.invalid>"
ABSENT_ID = "<inn-lab-absent-{tag}@example.invalid>"
ID_TEMPLATES = ("FED_ID", "LOOP_ID", "LOOP2_ID", "FN_POST_ID", "FN_OPERATOR_ID",
                "FN_LOOP_ID", "FN_FROM_ID", "FN_PATH_ID", "FN_PROTECTED_ID", "INN_CHECKGROUPS_ID", "FN_STREAM_ID", "INN_STREAM_ID", "ABSENT_ID")


def message_ids(tag: str) -> dict:
    """This run's Message-IDs, keyed by the template name."""
    return {name: globals()[name].format(tag=tag) for name in ID_TEMPLATES}


def article(msgid: str, subject: str, date: str, path: str | None = None,
            group: str = GROUP, body: str = "From the fn INN interop lab.",
            sender: str = "lab@example.invalid") -> bytes:
    """One article's octets, CRLF lines, RFC 5536 order.

    `path` None is an article as a posting agent writes it without Path: RFC
    5537 section 3.4.1 lets the injecting agent add it.  A supplied `path` is
    accepted by fn's POST since D32 (2026-09-25) and prefixed with fn's
    identity (books/injection.lisp, recipe v3); a malformed one is refused
    (`:path-malformed`)."""
    lines = (["Path: {}".format(path)] if path is not None else []) + [
        "From: " + sender,
        "Newsgroups: " + group,
        "Subject: " + subject,
        "Date: " + date,
        "Message-ID: " + msgid,
        "",
        body]
    return ("\r\n".join(lines) + "\r\n").encode("ascii")


def expected_injection(posted: bytes) -> dict:
    """Which injection fields fn's copy of POSTED must carry (RFC 5537 3.5).

    Path (items 8, 9) and Injection-Info (item 10, fn always adds it) are
    always there.  Item 11: an Injection-Date the proto-article had stays; one
    is added only when the proto-article lacked Date or Message-ID, since
    with both it MUST NOT be added."""
    had = {name: bool(header_value(posted, name))
           for name in ("Date", "Message-ID", "Injection-Date")}
    return {"Path": True,
            "Injection-Date": had["Injection-Date"]
            or not (had["Date"] and had["Message-ID"]),
            "Injection-Info": True}


# --------------------------------------------------------------------------
# reading octets: what the tap saw, and what two copies of an article differ in


def _crlf_lines(data: bytes) -> list:
    """Complete CRLF-terminated lines; a trailing fragment is not a line yet."""
    parts = data.split(b"\r\n")
    return parts[:-1]


def _take_block(lines: list, index: int) -> tuple:
    """A dot-terminated block from `index`, unstuffed, as octets (RFC 3977 3.1.1)."""
    body = []
    while index < len(lines):
        one = lines[index]
        index += 1
        if one == b".":
            return b"".join(line + b"\r\n" for line in body), index, True
        body.append(one[1:] if one.startswith(b"..") else one)
    return b"".join(line + b"\r\n" for line in body), index, False


def exchanges(client: bytes, server: bytes) -> dict:
    """Pair one connection's commands with its replies, in order.

    NNTP answers in the order it was asked, including in streaming mode
    (RFC 4644 section 2.1), so a command's reply is the next unconsumed
    server line.  IHAVE and POST carry their article after a 335/340 and are
    answered twice; TAKETHIS carries it at once and is answered once, after
    it.  Every reply is kept verbatim."""
    sent = _crlf_lines(client)
    said = [one.decode("utf-8", "replace") for one in _crlf_lines(server)]
    greeting = said.pop(0) if said else ""
    out = []
    index = 0
    while index < len(sent):
        command = sent[index].decode("utf-8", "replace")
        index += 1
        verb = command.split(" ")[0].upper() if command else ""
        entry = {"command": command, "reply": "", "article": None, "result": ""}
        if verb == "TAKETHIS":
            entry["article"], index, _ = _take_block(sent, index)
        entry["reply"] = said.pop(0) if said else ""
        if ((verb == "IHAVE" and entry["reply"].startswith("335"))
                or (verb == "POST" and entry["reply"].startswith("340"))):
            entry["article"], index, _ = _take_block(sent, index)
            entry["result"] = said.pop(0) if said else ""
        out.append(entry)
    return {"greeting": greeting, "exchanges": out}


def tap_connections(text: str, pair: str) -> list:
    """The tap log's connections on one relay, oldest first, as byte streams."""
    streams: dict = {}
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            one = json.loads(line)
        except ValueError:
            continue
        if one.get("pair") != pair or "data" not in one:
            continue
        stream = streams.setdefault(one["conn"], {"client": b"", "server": b""})
        stream[one["way"]] += base64.b64decode(one["data"])
    return [streams[key] for key in sorted(streams)]


def find_exchange(text: str, pair: str, msgid: str) -> dict | None:
    """The last offer or transfer of `msgid` on `pair`, merged across verbs.

    A streaming peer sends CHECK and then TAKETHIS; a non-streaming one sends
    IHAVE.  What is returned says which, with each reply verbatim, and whether
    the exchange is complete (a transfer has its final reply)."""
    found = None
    for stream in tap_connections(text, pair):
        parsed = exchanges(stream["client"], stream["server"])
        for entry in parsed["exchanges"]:
            words = entry["command"].split()
            if len(words) < 2 or words[1] != msgid:
                continue
            verb = words[0].upper()
            if verb not in ("IHAVE", "CHECK", "TAKETHIS"):
                continue
            if found is None or verb == "CHECK":
                found = {"greeting": parsed["greeting"], "verbs": [], "offer": "",
                         "result": "", "article": None}
            found["verbs"].append(verb)
            if verb == "IHAVE":
                found["offer"], found["result"] = entry["reply"], entry["result"]
                found["article"] = entry["article"]
            elif verb == "CHECK":
                found["offer"] = entry["reply"]
            else:
                found["result"] = entry["reply"]
                found["article"] = entry["article"]
    if found is not None:
        code = found["offer"][:3]
        # Done when the offer was declined, or the transfer was answered.
        found["complete"] = bool(found["result"]) or (
            bool(code) and code not in ("335", "238"))
    return found


def split_article(octets: bytes) -> tuple:
    """(headers as [(name, raw value)], body) with folded lines unfolded."""
    head, sep, body = octets.partition(b"\r\n\r\n")
    if not sep:
        head, body = octets, b""
    headers = []
    for line in head.split(b"\r\n"):
        if not line:
            continue
        if line[:1] in (b" ", b"\t") and headers:
            name, value = headers[-1]
            headers[-1] = (name, value + b"\r\n" + line)
            continue
        name, _, value = line.partition(b":")
        headers.append((name.decode("ascii", "replace"), value))
    return headers, body


def header_differences(first: bytes, second: bytes) -> dict:
    """Which header fields two copies of one article differ in, by name.

    `changed` names a field both carry with different values (or a different
    number of times); `only_first`/`only_second` name a field one copy lacks.
    Names are compared case-insensitively (RFC 5322 section 1.2.2) and the
    body octet for octet."""
    a_headers, a_body = split_article(first)
    b_headers, b_body = split_article(second)

    def by_name(headers):
        table: dict = {}
        for name, value in headers:
            table.setdefault(name.lower(), []).append(value)
        return table

    a, b = by_name(a_headers), by_name(b_headers)
    changed = sorted(name for name in set(a) & set(b) if a[name] != b[name])
    only_first = sorted(set(a) - set(b))
    only_second = sorted(set(b) - set(a))
    order_a = [name for name, _ in ((n.lower(), v) for n, v in a_headers)
               if name in b]
    order_b = [name for name, _ in ((n.lower(), v) for n, v in b_headers)
               if name in a]
    return {"identical": first == second, "changed": changed,
            "only_first": only_first, "only_second": only_second,
            "body_identical": a_body == b_body, "order_identical": order_a == order_b}


def relay_changes_permitted(diff: dict) -> bool:
    """RFC 5537 section 3.6: only Path and Xref, and never the body."""
    touched = set(diff["changed"]) | set(diff["only_first"]) | set(diff["only_second"])
    return diff["body_identical"] and touched <= set(RELAY_MAY_CHANGE)


def describe_differences(diff: dict) -> str:
    if diff["identical"]:
        return "byte-identical"
    parts = []
    if diff["changed"]:
        parts.append("changed: " + ", ".join(diff["changed"]))
    if diff["only_first"]:
        parts.append("only in the first: " + ", ".join(diff["only_first"]))
    if diff["only_second"]:
        parts.append("only in the second: " + ", ".join(diff["only_second"]))
    if not diff["order_identical"]:
        parts.append("the shared fields are in a different order")
    parts.append("body identical" if diff["body_identical"] else "BODY DIFFERS")
    return "; ".join(parts)


def header_value(octets: bytes, name: str) -> str:
    for one, value in split_article(octets)[0]:
        if one.lower() == name.lower():
            return value.strip().decode("utf-8", "replace")
    return ""


def streaming_transfer_completed(exchange, msgid):
    """Require both streaming replies to name this exact article, not IHAVE."""
    if not exchange or exchange.get("verbs") != ["CHECK", "TAKETHIS"]:
        return False
    offer = str(exchange.get("offer", "")).split()
    result = str(exchange.get("result", "")).split()
    return (len(offer) >= 2 and offer[:2] == ["238", msgid]
            and len(result) >= 2 and result[:2] == ["239", msgid]
            and bool(exchange.get("article")))


# --------------------------------------------------------------------------
# INN's configuration.  These five templates are the lab: docs/interop-inn.md
# quotes them, the evidence file records what was on disk, and the tool writes
# exactly this and nothing else.


INN_CONF = """\
# fn INN interop lab -- generated by tools/inn_lab.py.  Loopback only.
pathhost:               {inn_identity}
domain:                 hbox.test
organization:           "fn interop lab"
server:                 127.0.0.1
port:                   {inn_port}
bindaddress:            127.0.0.1
mta:                    "/usr/sbin/sendmail -oi %s"
hismethod:              hisv6
ovmethod:               tradindexed
enableoverview:         true
allownewnews:           true
maxartsize:             1000000
artcutoff:              0
wanttrash:              false
nnrpdposthost:          none
runasuser:              {user}
runasgroup:             {group}
pathnews:               {prefix}
logipaddr:              true
xrefslave:              false
"""

# incoming.conf has no `identity` key (inncheck rejects it); a peer is named by
# the block label and recognised by address.  specs/peering.md section 5's
# `identity: fnA` is INN's *newsfeeds* site name, written there.
INCOMING_CONF = """\
# fn INN interop lab -- INN accepts transit from the fn node over loopback.
streaming:      true
max-connections: 8

peer fn {{
    hostname:        127.0.0.1
    patterns:        fn.*
    streaming:       true
    max-connections: 4
}}
"""

# The ME site's exclusion sub-field is INN's inbound loop check: an article
# whose Path names one of these is rejected 437 (innd/art.c:2108, "Unwanted
# site %s in path").  INN does NOT reject on its own pathhost by default, so
# without this line specs/peering.md section 5's S8 would silently pass.
# It lists INN's OWN identity and nothing else: adding fn's identity here would
# refuse every article fn ever feeds, which a first draft of this file did and
# tests/test_inn_lab.py caught before the lab was pointed at a box.
#
# The `fn` site's own exclusion is the other direction, and it is what every
# INN peering carries: the site's name is `fn`, innfeed.conf's peer block is
# named after it, and an article whose Path already names fn's path identity
# is not offered back to fn (newsfeeds(5), "sitename/exclude").  Without it
# INN offers fn's own articles straight back, which fn answers 435 -- harmless,
# and not what a configured INN does.
NEWSFEEDS = """\
# fn INN interop lab -- generated by tools/inn_lab.py.
# ME's exclusion sub-field: an incoming article whose Path names one of these
# sites is refused 437 (innd/art.c ME.Exclusions).
ME/{inn_identity}:*::
innfeed!:!*:Tc,Wnm*:{prefix}/bin/innfeed -y
fn/{fn_identity}:fn.*:Tm:innfeed!
"""

INNFEED_CONF = """\
# fn INN interop lab -- the outbound half: INN offers fn.* to the fn node,
# through the lab's relay on port {innfeed_port}, which forwards to the owner.
pid-file:        innfeed.pid
log-file:        innfeed.log
status-file:     innfeed.status
backlog-directory: {prefix}/spool/innfeed
use-mmap:        false
initial-reconnect-time: 5
max-reconnect-time:     60

peer fn {{
    ip-name:             127.0.0.1
    port-number:         {innfeed_port}
    streaming:           true
    max-connections:     1
    initial-connections: 1
    drop-deferred:       false
}}
"""

READERS_CONF = """\
# fn INN interop lab -- nnrpd reads back what innd stored.  Loopback only.
auth "localhost" {{
    hosts: "localhost, 127.0.0.1, ::1"
    default: "<localhost>"
}}
access "localhost" {{
    users: "<localhost>"
    newsgroups: "*"
    access: RPA
}}
"""

READERS_SECURITY_CONF = """\
# Separate STARTTLS reader; no default identity or anonymous read access.
auth "protected-fixture" {{
    hosts: "127.0.0.1"
    require_encryption: true
    auth: "ckpasswd -f {prefix}/db/security-newsusers"
}}
access "protected-fixture" {{
    users: "fn-lab"
    newsgroups: "fn.*"
    access: {access}
    nnrpdposthost: 127.0.0.1
    nnrpdpostport: {inn_port}
}}
"""


CONFIG_FILES = ("inn.conf", "incoming.conf", "newsfeeds", "innfeed.conf",
                "readers.conf")




# --------------------------------------------------------------------------
# the drivers that run on the host

INN_DRIVER = r'''#!/usr/bin/env python3
"""The INN lab's socket phases.  No fn module is imported.

Python 3.13 removed nntplib (PEP 594), so every NNTP exchange here is a raw
socket, and every article is sent and read as octets: a transit client
written against the wire is the only kind that can hand a server a Path it
must refuse, and the only kind whose read-back can be compared byte for byte.
"""
import argparse, base64, json, socket, ssl, sys


class Wire:
    def __init__(self, port, timeout=30, source_address=None):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=timeout,
            source_address=(source_address, 0) if source_address else None)
        self.file = self.sock.makefile("rb")
        self.greeting = self.line()

    def line(self):
        raw = self.file.readline()
        if not raw:
            raise EOFError("the server closed the connection")
        return raw.rstrip(b"\r\n").decode("utf-8", "replace")

    def cmd(self, text):
        self.sock.sendall(text.encode() + b"\r\n")
        return self.line()

    def starttls(self, cafile):
        """The real peer's 382, then certificate/name-verified TLS on it."""
        reply = self.cmd("STARTTLS")
        if not reply.startswith("382"):
            raise RuntimeError("STARTTLS refused: " + reply)
        self.file.close()
        context = ssl.create_default_context(cafile=cafile)
        self.sock = context.wrap_socket(self.sock, server_hostname="127.0.0.1")
        self.file = self.sock.makefile("rb")
        return reply

    def block(self):
        """A dot-terminated block, unstuffed, as the octets it carries."""
        out = b""
        while True:
            raw = self.file.readline()
            if not raw:
                raise EOFError("the server closed the connection inside a block")
            if raw == b".\r\n":
                return out
            out += raw[1:] if raw.startswith(b"..") else raw

    def send_block(self, octets):
        payload = b""
        for one in octets.split(b"\r\n")[:-1]:
            payload += (b"." + one if one.startswith(b".") else one) + b"\r\n"
        self.sock.sendall(payload + b".\r\n")

    def close(self):
        try:
            self.cmd("QUIT")
        except Exception:
            pass
        try:
            self.sock.close()
        except Exception:
            pass


def octets(path):
    with open(path, "rb") as handle:
        return handle.read()


def transfer(wire, msgid, path):
    """IHAVE, and the article if the offer is taken: both replies verbatim."""
    offer = wire.cmd("IHAVE " + msgid)
    if not offer.startswith("335"):
        return offer, ""
    wire.send_block(octets(path))
    return offer, wire.line()


def fetch_one(wire, msgid):
    status = wire.cmd("ARTICLE " + msgid)
    body = wire.block() if status.startswith("220") else b""
    return status, base64.b64encode(body).decode()


def read(args):
    """nnrpd: GROUP, ARTICLE by Message-ID, and an unknown Message-ID."""
    wire = Wire(args.port)
    out = {"greeting": wire.greeting, "group": wire.cmd("GROUP " + args.group)}
    out["article"], out["octets"] = fetch_one(wire, args.msgid)
    out["absent"] = wire.cmd("ARTICLE " + args.absent)
    if out["absent"].startswith("220"):
        wire.block()
    wire.close()
    out["ok"] = (out["group"].startswith("211") and out["article"].startswith("220")
                 and out["absent"].startswith("43"))
    return out


def ihave(args):
    """innd: a transfer, the duplicate, a Path naming INN, CHECK both ways."""
    wire = Wire(args.port)
    out = {"greeting": wire.greeting, "mode_stream": wire.cmd("MODE STREAM")}
    out["offer"], out["transfer"] = transfer(wire, args.msgid, args.file)
    out["duplicate"], out["duplicate_transfer"] = transfer(wire, args.msgid, args.file)
    out["loop_offer"], out["loop_result"] = transfer(wire, args.loop_msgid, args.loop_file)
    if not out["loop_result"]:
        out["loop_result"] = out["loop_offer"]
    out["check_unknown"] = wire.cmd("CHECK " + args.absent)
    out["check_duplicate"] = wire.cmd("CHECK " + args.msgid)
    wire.close()
    out["ok"] = (out["transfer"].startswith("235")
                 and out["duplicate"].startswith("435")
                 and out["loop_result"].startswith("437")
                 and out["check_unknown"].startswith("238")
                 and out["check_duplicate"].startswith("438"))
    return out


def offer(args):
    """One IHAVE offer (and transfer, if taken); with --read, then ARTICLE."""
    wire = Wire(args.port)
    out = {"greeting": wire.greeting}
    out["offer"], out["result"] = transfer(wire, args.msgid, args.file)
    if args.read:
        out["after"], out["octets"] = fetch_one(wire, args.msgid)
    wire.close()
    out["ok"] = True
    return out


def stream(args):
    """Complete a fresh MODE/CHECK/TAKETHIS transfer; never substitute IHAVE."""
    wire = Wire(args.port)
    try:
        out = {"greeting": wire.greeting, "mode_stream": wire.cmd("MODE STREAM")}
        out["offer"], out["result"] = "", ""
        if out["mode_stream"].startswith("203"):
            out["offer"] = wire.cmd("CHECK " + args.msgid)
            if out["offer"].split()[:2] == ["238", args.msgid]:
                wire.sock.sendall(("TAKETHIS " + args.msgid + "\r\n").encode())
                wire.send_block(octets(args.file))
                out["result"] = wire.line()
        out["ok"] = (out["offer"].split()[:2] == ["238", args.msgid]
                     and out["result"].split()[:2] == ["239", args.msgid])
        return out
    finally:
        wire.close()


def post(args):
    """POST (RFC 3977 section 6.3.1), then the article read back by Message-ID."""
    wire = Wire(args.port)
    out = {"greeting": wire.greeting, "post": wire.cmd("POST")}
    out["result"] = ""
    if out["post"].startswith("340"):
        wire.send_block(octets(args.file))
        out["result"] = wire.line()
    out["article"], out["octets"] = fetch_one(wire, args.msgid)
    wire.close()
    out["ok"] = out["result"].startswith("240") and out["article"].startswith("220")
    return out


def fetch(args):
    wire = Wire(args.port)
    out = {"greeting": wire.greeting}
    out["article"], out["octets"] = fetch_one(wire, args.msgid)
    wire.close()
    out["ok"] = out["article"].startswith("220")
    return out


def caps(args):
    wire = Wire(args.port)
    out = {"greeting": wire.greeting}
    status = wire.cmd("CAPABILITIES")
    out["status"] = status
    out["capabilities"] = (wire.block().decode("utf-8", "replace").split("\r\n")[:-1]
                           if status.startswith("101") else [])
    wire.close()
    out["ok"] = status.startswith("101")
    return out


def protected_read(args):
    """Real nnrpd STARTTLS, failed/successful USER/PASS and authenticated read.

    The password is a scratch fixture file, never argv or JSON evidence.
    This is the reader/authentication arm; no relay/discharge claim follows.
    """
    wire = Wire(args.port)
    out = {"greeting": wire.greeting}
    try:
        out["starttls"] = wire.starttls(args.cafile)
        out["tls"] = wire.sock.version()
        out["bad_user"] = wire.cmd("AUTHINFO USER " + args.username)
        if out["bad_user"].startswith("381"):
            out["bad_pass"] = wire.cmd("AUTHINFO PASS not-the-fixture-password")
        else:
            out["bad_pass"] = ""
        out["before_login"] = wire.cmd("GROUP " + args.group)
        out["user"] = wire.cmd("AUTHINFO USER " + args.username)
        if not out["user"].startswith("381"):
            out["ok"] = False
            return out
        password = octets(args.password_file).decode("ascii").rstrip("\n")
        if not password or "\r" in password or "\n" in password:
            raise ValueError("password fixture must be one nonempty ASCII line")
        out["pass"] = wire.cmd("AUTHINFO PASS " + password)
        if not out["pass"].startswith("281"):
            out["ok"] = False
            return out
        out["group"] = wire.cmd("GROUP " + args.group)
        out["article"], out["octets"] = fetch_one(wire, args.msgid)
        out["ok"] = (out["bad_user"].startswith("381")
                     and out["bad_pass"].startswith("481")
                     and out["before_login"].startswith("480")
                     and out["group"].startswith("211")
                     and out["article"].startswith("220"))
        return out
    finally:
        wire.close()


def group_ids(wire, group):
    status = wire.cmd("LISTGROUP " + group)
    out = {"reply": status, "stats": [], "ids": []}
    if status.startswith("211"):
        numbers = wire.block().decode("ascii").splitlines()
        for number in numbers:
            if not number.isdecimal():
                raise ValueError("LISTGROUP returned a nonnumeric fixture article number")
            stat = wire.cmd("STAT " + number)
            out["stats"].append(stat)
            fields = stat.split()
            if len(fields) >= 3 and fields[0] == "223":
                out["ids"].append(fields[2])
    return out


def control_view(args):
    # Different loopback source from the address-authorized INN peer: this
    # connection is a reader, without removing or changing the peer record.
    wire = Wire(args.port, source_address=args.reader_source)
    try:
        out = {"greeting": wire.greeting,
               "filing": group_ids(wire, args.group),
               "ordinary": group_ids(wire, args.other_group)}
        out["active"] = wire.cmd("LIST ACTIVE " + args.probe_group)
        out["active_rows"] = (wire.block().decode("ascii").splitlines()
                              if out["active"].startswith("215") else [])
        out["article"], out["octets"] = fetch_one(wire, args.msgid)
        out["ok"] = (out["filing"]["reply"].startswith("211")
                     and out["ordinary"]["reply"].startswith("211")
                     and args.msgid in out["filing"]["ids"]
                     and args.msgid not in out["ordinary"]["ids"]
                     and out["active"].startswith("215") and not out["active_rows"]
                     and out["article"].startswith("220"))
        return out
    finally:
        wire.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="phase", required=True)
    for name in ("read", "ihave", "offer", "stream", "post", "fetch", "caps", "protected-read", "control-view"):
        one = sub.add_parser(name)
        one.add_argument("--port", type=int, required=True)
        one.add_argument("--group", default="fn.letters")
        one.add_argument("--msgid", default="")
        one.add_argument("--file", default="")
        one.add_argument("--absent", default="<absent@example.invalid>")
        one.add_argument("--loop-msgid", default="")
        one.add_argument("--loop-file", default="")
        one.add_argument("--read", action="store_true",
                         help="offer: read the Message-ID back on the same connection")
        one.add_argument("--reader-source", default="127.0.0.2")
        one.add_argument("--other-group", default="fn.letters")
        one.add_argument("--probe-group", default="fn.checkgroups.proposed")
        one.add_argument("--cafile", default="")
        one.add_argument("--username", default="fn-lab")
        one.add_argument("--password-file", default="")
    args = parser.parse_args()
    handler = {"read": read, "ihave": ihave, "offer": offer, "post": post,
               "fetch": fetch, "caps": caps, "protected-read": protected_read,
               "control-view": control_view, "stream": stream}[args.phase]
    try:
        result = handler(args)
    except Exception as error:
        print(json.dumps({"ok": False, "error": "{}: {}".format(
            type(error).__name__, error)}))
        return 1
    print(json.dumps(result))
    return 0 if result.get("ok") else 1


if __name__ == "__main__":
    sys.exit(main())
'''

# The relay.  One process, one listener per `LISTEN:FORWARD` pair, every chunk
# logged as a JSON line with its direction (`client` is what the connecting
# side sent, `server` what the listening side answered).  It forwards octets
# unchanged and in order, and it is on loopback, so the only thing it adds to
# either conversation is a hop both servers see as 127.0.0.1 -- which is the
# address each server's peer record admits anyway.
TAP_DRIVER = r'''#!/usr/bin/env python3
import base64, json, socket, sys, threading, time

log = open(sys.argv[1], "a", buffering=1)
lock = threading.Lock()


def note(**fields):
    with lock:
        log.write(json.dumps(fields) + "\n")


def pump(source, sink, pair, conn, way):
    try:
        while True:
            data = source.recv(65536)
            if not data:
                break
            note(t=time.time(), pair=pair, conn=conn, way=way,
                 data=base64.b64encode(data).decode())
            sink.sendall(data)
    except Exception as error:
        note(t=time.time(), pair=pair, conn=conn, way=way, error=repr(error))
    finally:
        for one in (source, sink):
            try:
                one.shutdown(socket.SHUT_RDWR)
            except Exception:
                pass


def serve(listen, forward):
    pair = "{}>{}".format(listen, forward)
    server = socket.socket()
    server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server.bind(("127.0.0.1", listen))
    server.listen(16)
    conn = 0
    while True:
        client, _ = server.accept()
        conn += 1
        try:
            upstream = socket.create_connection(("127.0.0.1", forward), timeout=10)
            upstream.settimeout(None)
        except Exception as error:
            note(t=time.time(), pair=pair, conn=conn, way="open", error=repr(error))
            client.close()
            continue
        note(t=time.time(), pair=pair, conn=conn, way="open")
        threading.Thread(target=pump, args=(client, upstream, pair, conn, "client"),
                         daemon=True).start()
        threading.Thread(target=pump, args=(upstream, client, pair, conn, "server"),
                         daemon=True).start()


for spec in sys.argv[2:]:
    listen, forward = (int(one) for one in spec.split(":"))
    threading.Thread(target=serve, args=(listen, forward), daemon=True).start()
while True:
    time.sleep(3600)
'''


# --------------------------------------------------------------------------
# the lab


class InnLab(deploy_gate.DeployGate):
    """The deploy gate's machinery, with a real INN on one end and the image on the other."""

    TITLE = "INN interop lab"
    TOOL = "tools/inn_lab.py"
    PREAMBLE = (
        "A real InterNetNews server, built from the release tarball pinned below and",
        "left installed on the box, peered with one fn node run from the saved native",
        "image named below through its public entry. This records what ran. INN's",
        "replies are INN's; fn's are fn's; each is quoted from the relay that carried",
        "it. A row that could not run is a skip carrying the reason, never a weaker",
        "scenario under the same name.")
    FACT_KEYS = ("os", "kernel", "python3", "native image", "native launcher",
                 "native core", "native runtime", "certificates", "inn version",
                 "inn tarball sha256", "inn prefix", "ports", "inn server", "fn node",
                 "fn path identity", "fn peer record", "fn post", "fn feed to inn",
                 "inn read of fn's article", "fn post vs fn served",
                 "fn served vs inn served", "operator post feed", "inn control",
                 "innfeed to fn", "inn served vs fn served", "duplicates", "fn loop",
                 "fn term", "innd cut", "inn protected reader", "fn protected injection", "actual checkgroups control")
    # What this lab decides.  Nothing of deploy_gate's own inventory is
    # inherited: those assertions are about the development store CLI and
    # its certificates, and this lab runs neither.
    ASSERTIONS = {
        "entry-point-listening": (
            "the native owner (`packaging/fn-native operator CONFIG run`) reached "
            "LISTENING on the port the lab configured", ("",)),
        "native-subject-measured": (
            "the launcher, the image, the core it loads and the runtime were "
            "digested before anything ran", ("",)),
        "path-identity-set": (
            "`policy set path-identity` was accepted, so fn can recognise its own "
            "name in a Path (RFC 5537 3.2)", ("",)),
        "peer-record-accepted": (
            "the fn node holds a peer record naming INN, read back by `peer list`",
            ("",)),
        "ports-free": ("the ports the lab needs were free before it started", ("",)),
        "innd-up": ("innd came up", ("",)),
        "nnrpd-up": ("nnrpd came up on its port", ("",)),
        "tap-up": ("the relay listened on both of its ports", ("",)),
        "fn-post-240": ("POST to the fn owner drew 340 then 240, and the article "
                        "reads back by Message-ID", ("",)),
        "fn-feeds-inn": (
            "fn's outbound feed offered the posted article to innd by IHAVE, and "
            "innd answered 335 then 235", ("",)),
        "inn-serves-fn-article": (
            "nnrpd serves the article fn fed, changed only where RFC 5537 3.6 "
            "permits a relay to change it (Path, Xref)", ("",)),
        "operator-post-feeds-inn": (
            "an article submitted through `operator post` reaches innd through "
            "fn's outbound feed, injected: Path naming fn and Injection-Info, and "
            "Injection-Date only when the submission lacked Date or Message-ID "
            "(RFC 5537 3.5 item 11)", ("",)),
        "fn-post-from-invalid-441": (
            "a POST whose From names no address (`From: yue`) draws 441 from fn "
            "and is not served (RFC 5536 3.1.2)", ("",)),
        "fn-post-supplied-path-240": (
            "a POST that supplies `Path: not-for-mail`, as tin sends, draws 240 and "
            "reads back (D32; RFC 5537 3.4.1 and 3.2.1: the injecting agent "
            "prefixes its identity)", ("",)),
        "inn-transfer-235": ("a hand-made IHAVE into innd draws 335 then 235", ("",)),
        "inn-duplicate-435": (
            "a second IHAVE of an article innd holds draws 435", ("", "fn-article")),
        "inn-loop-437": ("an article whose Path names INN draws 437 from innd", ("",)),
        "innfeed-feeds-fn": (
            "INN's innfeed offered an article to fn and fn took it (238/239 or "
            "335/235)", ("",)),
        "bidirectional-streaming": (
            "fresh native fn and INN articles crossed their respective actual "
            "outbound feeds by CHECK/TAKETHIS with subject-matched 238/239 "
            "and receiver readback changed only in Path/Xref", ("fn-to-inn", "inn-to-fn")),
        "fn-serves-inn-article": (
            "fn serves the article innfeed transferred with every octet but Path and "
            "Xref as it arrived (RFC 5537 3.7: a serving agent alters nothing else)",
            ("",)),
        "fn-serves-own-path-identity": (
            "the Path fn serves for an article it took by transit names fn's own "
            "path identity (RFC 5537 3.7 step 6, by way of 3.2.1)", ("",)),
        "fn-serves-no-sender-xref": (
            "fn does not serve the sending server's Xref on an article it took by "
            "transit (RFC 5537 3.7 step 7; specs/peering.md 2.3, `Xref` is never "
            "stored)", ("",)),
        "fn-duplicate-435": (
            "a second IHAVE of an article fn holds draws 435 from fn",
            ("inn-article", "fn-article")),
        "fn-loop-refused": (
            "an article whose Path names fn's own path identity is refused by fn "
            "(RFC 5537 3.6 step 3; 435 or 437) and is not served", ("",)),
        "fn-term-stopped": ("the owner exited on SIGTERM", ("",)),
        "innd-survived-fn-term": (
            "innd was still running after the fn owner was stopped", ("",)),
        "fn-recover": ("`operator CONFIG recover` exited 0 after the SIGTERM", ("",)),
        "fn-articles-survived-term": (
            "after SIGTERM, recover and restart, fn serves the articles it held "
            "byte-identical", ("fn-article", "inn-article")),
        "inn-checkgroups-control": (
            "a real Control: checkgroups article accepted by INN reached fn through "
            "innfeed, was served unchanged except permitted Path/Xref changes, "
            "filed in control.checkgroups rather than its ordinary Newsgroups, "
            "and did not automatically create its proposed group", ("",)),
        "fn-protected-injection": (
            "with its clear feed paused, native fn's separate STARTTLS/USER-PASS "
            "peer received accepted feed code235 for a fresh article; the real "
            "authenticated nnrpd reader served that Message-ID, subject and body, "
            "and the article was absent from the clear transit relay", ("",)),
        "inn-protected-reader": (
            "the separate nnrpd reader completed certificate/name-verified STARTTLS "
            "(382), refused a bad password (481) and unauthenticated read (480), "
            "then accepted USER/PASS (281) and served fn's article (220) with "
            "only the already permitted relay header changes", ("",)),
        "innd-died": ("innd died on SIGKILL, so the control really cut", ("",)),
        "innd-restarted": ("innd came back after the SIGKILL", ("",)),
        "inn-history-survived-kill": (
            "after innd's SIGKILL and restart, a second IHAVE of an article it "
            "acknowledged before draws 435", ("inn-article", "fn-article")),
    }
    STANDING_GAPS = (
        "INN and fn are on ONE host, over loopback. Nothing here exercises a real\n"
        "  network, a partition, latency, or two machines' clocks disagreeing.",
        "Both transit connections pass through the lab's relay (tap.py). It forwards\n"
        "  octets unchanged and in order, and both servers see it as 127.0.0.1, the\n"
        "  address each peer record admits; it is still a hop neither would have.",
        "No TLS, no AUTHINFO, no Distribution header, no control messages, no\n"
        "  cancel and no expiry: incoming.conf and fn's peer record authorise by\n"
        "  source address only, which on loopback authorises everything local.",
        "A SIGKILL of innd and a SIGTERM of the owner are process deaths, not power\n"
        "  loss, and killing one server is not a partition.",
        "No RFC 3977/4644/5537 conformance audit. The assertions are this driver's,\n"
        "  and a held row says the two programs interoperated on that exchange.",
        "The native image is consumed as named; nothing here re-establishes which\n"
        "  source or which certificates it was built from.")

    def __init__(self, *args, native_image, inn_prefix, inn_version, inn_port,
                 nnrpd_port, fn_port, tap_out_port, tap_in_port,
                 lab_root=DEFAULT_LAB_ROOT, native_openssl_prefix=None,
                 extra_overlays=(), feed_wait=90, inn_security=False,
                 inn_security_port=INN_SECURITY_PORT, inn_security_feed=False, inn_controls=False,
                 inn_streaming=False, **kwargs):
        super().__init__(*args, **kwargs)
        if not native_image:
            raise GateError("the fn side is the native image or the lab does not run "
                            "(D07): --native-image is required")
        self.native_image = native_image
        self.native_openssl_prefix = native_openssl_prefix
        self.inn_prefix = inn_prefix
        self.inn_version = inn_version
        self.inn_security = inn_security
        self.inn_security_port = inn_security_port
        self.inn_controls = inn_controls
        self.inn_streaming = inn_streaming
        if not inn_streaming:
            self.ASSERTIONS = {name: value for name, value in self.ASSERTIONS.items()
                               if name != "bidirectional-streaming"}
        if not inn_controls:
            self.ASSERTIONS = {name: value for name, value in self.ASSERTIONS.items()
                               if name != "inn-checkgroups-control"}
        self.inn_security_feed = inn_security_feed
        if inn_security_feed and not inn_security:
            raise GateError("--inn-security-feed requires --inn-security")
        if not inn_security_feed:
            self.ASSERTIONS = {name: value for name, value in self.ASSERTIONS.items()
                               if name != "fn-protected-injection"}
        if inn_security and inn_prefix.rstrip("/") == "{}/{}".format(
                DEFAULT_INN_ROOT, inn_version):
            raise GateError("--inn-security requires a separate TLS-capable "
                            "--inn-prefix, not the standing plaintext install")
        if inn_security:
            self.STANDING_GAPS = tuple(
                "The optional reader uses verified STARTTLS and USER/PASS; the "
                "transit relays remain clear and address-authorized. The optional "
                "native protected injection is recorded separately. No "
                "Distribution, control messages, cancel or expiry is exercised."
                if gap.startswith("No TLS,") else gap for gap in self.STANDING_GAPS)
        if inn_controls:
            self.STANDING_GAPS = tuple(
                gap.replace("No TLS, no AUTHINFO, no Distribution header, no control messages, no",
                    "No TLS, no AUTHINFO, no Distribution header; unsigned checkgroups filing only, no")
                   .replace("Distribution, control messages, cancel or expiry is exercised.",
                    "Distribution, authenticated control discharge, cancel or expiry is exercised. "
                    "Unsigned checkgroups filing is selected separately.")
                for gap in self.STANDING_GAPS)
        if not inn_security:
            # An unselected optional row is not an observed failure or a pass.
            self.ASSERTIONS = {name: assertion for name, assertion in self.ASSERTIONS.items()
                               if name != "inn-protected-reader"}
        self.inn_port = inn_port
        self.nnrpd_port = nnrpd_port
        self.fn_port = fn_port
        self.tap_out_port = tap_out_port
        self.tap_in_port = tap_in_port
        self.feed_wait = feed_wait
        self.extra_overlays = list(extra_overlays)
        self.lab_root = lab_root
        # Everything this run writes lives under the lab root, never under the
        # deploy gate's ~/fn-deploy: the box's other gates own that tree.
        self.deploy = "{}/{}".format(lab_root, self.deploy_id)
        self.deploy_lock = "{}/.locks/{}.lock".format(lab_root, self.deploy_id)
        self.run = "{}/gate-run".format(self.deploy)
        self.node_dir = "{}/node".format(self.deploy)
        self.store = "{}/store".format(self.node_dir)
        self.config = "{}/fn.toml".format(self.node_dir)
        self.tap_log = "{}/tap.log".format(self.run)
        self.fn_pid = ""
        self.inn_running = False
        self.started_pids: dict = {}      # only what this run started is ever killed
        self.held_octets: dict = {}       # what fn served before the SIGTERM
        self.inn_holds: list = []         # Message-IDs innd acknowledged
        self.tap_text = ""                # the relay's log, read before cleanup
        self.tag = "{}-{}".format(self.rev, dt.datetime.now(
            dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
        self.ids = message_ids(self.tag)
        self.date = email.utils.formatdate(localtime=False)

    # -- plumbing ---------------------------------------------------------
    def bin(self, name: str) -> str:
        return "{}/bin/{}".format(self.inn_prefix, name)

    def ship(self):
        lock = self.sh("acquire deploy lock", """
mkdir -p {root}/.locks
if ! mkdir {lock} 2>/dev/null; then
  echo "deploy identity is already active: {identity}"
  exit 73
fi
""".format(root=self.lab_root, lock=self.deploy_lock, identity=self.deploy_id))
        if lock.rc != 0:
            raise GateError(lock.first_line or "deploy identity is already active")
        self.deploy_lock_acquired = True
        start = time.monotonic()
        done = self.host.deploy(self.repo, self.commit, self.deploy, timeout=600)
        output = done.stdout.decode("utf-8", "replace")
        self.steps.append(Step("ship archive", "git archive {} | tar -x -C {}".format(
            self.rev, self.deploy), done.returncode, output, time.monotonic() - start))
        if done.returncode != 0:
            raise GateError("could not ship the archive: " + output[:400])
        self.sh("make run dir", "mkdir -p {} {}".format(self.run, self.node_dir))
        for overlay in ([self.overlay] if self.overlay else []) + self.extra_overlays:
            self.push_tree(overlay)
        self.push_file(INN_DRIVER, "{}/inn.py".format(self.run), mode="755")
        self.push_file(TAP_DRIVER, "{}/tap.py".format(self.run), mode="755")

    def drive_inn(self, phase: str, extra: str, name: str, timeout=120) -> Step:
        return self.sh(name, self.cd("python3 {}/inn.py {} {}".format(
            self.run, phase, extra)), timeout=timeout, expect=None)

    @staticmethod
    def payload(step: Step) -> dict:
        for line in reversed(step.output.splitlines()):
            line = line.strip()
            if line.startswith("{"):
                try:
                    return json.loads(line)
                except ValueError:
                    continue
        return {}

    @staticmethod
    def octets_of(result: dict) -> bytes:
        try:
            return base64.b64decode(result.get("octets") or "")
        except ValueError:
            return b""

    def derive(self, name, source: Step, note="", ok=False) -> Step:
        """A second step over a probe's result: the assertion its answer must meet.

        Its code is the assertion's, never the driver's exit code: one driver
        phase carries several assertions."""
        step = Step(name, source.command, 0 if ok else 1, source.output, 0.0, note, 0)
        self.steps.append(step)
        return step

    def put_article(self, name: str, octets: bytes) -> str:
        remote = "{}/{}.article".format(self.run, name)
        self.push_file(octets, remote)
        return remote

    def wait_tap(self, pair_ports: tuple, msgid: str, what: str) -> dict | None:
        """Poll the relay's log until `msgid`'s exchange on one pair is complete.

        The polls are not steps; the one step recorded is the last read, with
        the number of polls, so the record says what was waited for and how
        long without a row per second."""
        pair = "{}>{}".format(*pair_ports)
        clock = time.monotonic()
        polls, found, done = 0, None, None
        while True:
            polls += 1
            done = self.host.sh("cat {} 2>/dev/null || true".format(self.tap_log), 60)
            text = done.stdout.decode("utf-8", "replace")
            self.tap_text = text or self.tap_text
            found = find_exchange(text, pair, msgid)
            if (found and found["complete"]) or time.monotonic() - clock > self.feed_wait:
                break
            time.sleep(2)
        summary = ("{} on {}: {}".format(
            "+".join(found["verbs"]), pair,
            " / ".join(one for one in (found["offer"], found["result"]) if one))
            if found else "no exchange for {} on {} after {:.0f} s".format(
                msgid, pair, time.monotonic() - clock))
        self.steps.append(Step(
            "relay log: {}".format(what), "cat {} (polled {} times, pair {})".format(
                self.tap_log, polls, pair), 0, summary + "\n",
            time.monotonic() - clock, "", None))
        return found

    # -- the native subject -------------------------------------------------
    def native_subject(self):
        """Digest the launcher, the image, the core it execs and its runtime.

        The core an image loads is the one its launcher script names after
        `--core`, which need not be the sidecar beside it; both are digested
        and the record says which one ran."""
        step = self.sh("native subject", self.cd(r"""
image={image}
test -x "$image" || {{ echo "NATIVE-IMAGE-MISSING $image"; exit 4; }}
test -x packaging/fn-native || {{ echo NATIVE-WRAPPER-MISSING; exit 4; }}
if command -v sha256sum >/dev/null 2>&1; then
  digest() {{ sha256sum "$1" | awk '{{print $1}}'; }}
else
  digest() {{ shasum -a 256 "$1" | awk '{{print $1}}'; }}
fi
core=$(sed -n 's/.*--core "\([^"]*\)".*/\1/p' "$image" | head -1)
runtime=$(sed -n 's/^exec "\([^"]*\)".*/\1/p' "$image" | head -1)
echo "NATIVE-LAUNCHER packaging/fn-native $(digest packaging/fn-native)"
echo "NATIVE-IMAGE $image $(digest "$image")"
if [ -s "$image.core" ]; then echo "NATIVE-SIDECAR $image.core $(digest "$image.core")"; fi
if [ -n "$core" ] && [ -s "$core" ]; then echo "NATIVE-CORE $core $(digest "$core")"; else echo "NATIVE-CORE $image.core $(digest "$image.core" 2>/dev/null || echo absent)"; fi
if [ -n "$runtime" ] && [ -x "$runtime" ]; then echo "NATIVE-RUNTIME $runtime $(digest "$runtime")"; else echo "NATIVE-RUNTIME unmeasured"; fi
""".format(image=shlex.quote(self.native_image))), timeout=600, expect=None)
        marks = {}
        for line in step.output.splitlines():
            if line.startswith("NATIVE-") and " " in line:
                key, _, value = line.partition(" ")
                marks[key] = value.strip()
        ok = step.rc == 0 and all(key in marks for key in (
            "NATIVE-LAUNCHER", "NATIVE-IMAGE", "NATIVE-CORE"))
        self.facts["native image"] = marks.get("NATIVE-IMAGE", self.native_image)
        self.facts["native launcher"] = marks.get("NATIVE-LAUNCHER", "(not measured)")
        core = marks.get("NATIVE-CORE", "(not measured)")
        sidecar = marks.get("NATIVE-SIDECAR", "")
        if sidecar and core.split()[-1:] == sidecar.split()[-1:]:
            core += " (the sidecar beside the image has the same digest)"
        elif sidecar:
            core += " (the sidecar {} differs)".format(sidecar)
        self.facts["native core"] = core
        self.facts["native runtime"] = marks.get("NATIVE-RUNTIME", "(not measured)")
        self.facts["certificates"] = ("not acquired: the lab consumes the saved image "
                                      "it was given, as the v0 matrix's native slice does")
        self.check("native-subject-measured", ok,
                   "the native subject was not measured: {}".format(step.first_line),
                   observed=step.first_line or "no output")
        if not ok:
            raise GateError("the native image did not measure: {}".format(
                step.first_line or "no output"))

    # -- the fn node ------------------------------------------------------
    def native_node(self):
        init = self.sh("fn store init", self.cd(self.native(
            "store", self.store, "init", GROUP)), timeout=600, expect=None)
        if init.rc != 0:
            raise GateError("fn store init failed: {}".format(init.output[:400]))
        # The heredoc is unquoted on purpose: the lab root is `$HOME/...` and
        # fn.toml wants the absolute path, which the remote shell expands.
        self.sh("fn.toml", """
cat > {config} <<FN_TOML
[store]
path = "{store}"

[listener]
host = "127.0.0.1"
port = {port}

[posting]
enabled = true

[control]
path = "{node}/control.sock"
FN_TOML
cat {config}
""".format(config=self.config, store=self.store, port=self.fn_port,
           node=self.node_dir))
        ident = self.sh("fn policy set path-identity", self.cd(self.operator(
            "policy", "set", "path-identity", FN_PATH_IDENTITY)), timeout=600,
            expect=None)
        self.facts["fn path identity"] = "{} (rc={}, {})".format(
            FN_PATH_IDENTITY, ident.rc, ident.output.strip().splitlines()[-1:]
            and ident.output.strip().splitlines()[-1])
        self.check("path-identity-set", ident.rc == 0,
                   "`policy set path-identity {}` exited {}: {}. fn cannot recognise "
                   "its own name in a Path, so the loop row below is about an "
                   "unconfigured node.".format(FN_PATH_IDENTITY, ident.rc,
                                               ident.first_line),
                   observed=ident.first_line or "no output")
        # The record's grammar is books/native-admin.lisp `fn-native-admin-peer-plan`:
        # NAME PATH-IDENTITY ADDRESS PORT INBOUND OUTBOUND SOURCE-ADDRESS STREAMING.
        # Streaming `false` makes fn's feed speak IHAVE (RFC 3977 6.3.2), the
        # verb every INN takes; the address is the relay, which forwards to innd.
        added = self.sh("fn peer record for INN", self.cd(self.operator(
            "peer", "add", FN_PEER_NAME, INN_PATH_IDENTITY, "127.0.0.1",
            str(self.tap_out_port), "'fn.*'", "'fn.*'", "127.0.0.1", "false")),
            timeout=600, expect=None)
        listing = self.sh("fn peer list", self.cd(self.operator("peer", "list")),
                          timeout=600, expect=None)
        line = next((one for one in listing.output.splitlines()
                     if one.startswith(FN_PEER_NAME + " ")), "")
        self.facts["fn peer record"] = line or "(no peer line)"
        self.check("peer-record-accepted",
                   added.rc == 0 and INN_PATH_IDENTITY in line,
                   "the fn node has no peer record for INN (`peer add` exit {}), so "
                   "its listener resolves INN's address to no peer and its feed has "
                   "no target: every transit row below is about an unconfigured "
                   "node.".format(added.rc),
                   observed=line or listing.first_line or "no peer line")
        self.sh("fn status before the owner starts", self.cd(self.operator("status")),
                timeout=600, expect=None)

    def start_fn(self, tag: str) -> bool:
        log = "{}/owner-{}.log".format(self.node_dir, tag)
        step = self.sh("start the native owner ({})".format(tag), self.cd("""
rm -f {log}
nohup {command} > {log} 2>&1 < /dev/null &
echo $! > {node}/owner.pid
for i in $(seq 1 120); do
  if grep -m1 '^LISTENING' {log}; then echo "OWNER-UP pid=$(cat {node}/owner.pid)"; exit 0; fi
  if ! kill -0 $(cat {node}/owner.pid) 2>/dev/null; then echo OWNER-DIED; tail -25 {log}; exit 1; fi
  sleep 1
done
echo OWNER-TIMEOUT; tail -25 {log}; exit 1
""".format(log=log, command=self.operator("run"), node=self.node_dir)),
            timeout=300, expect=None)
        listening = next((one for one in step.output.splitlines()
                          if one.startswith("LISTENING")), "")
        up = step.rc == 0 and listening == "LISTENING {}".format(self.fn_port)
        if tag == "main":
            self.check("entry-point-listening", up,
                       "the native owner did not reach `LISTENING {}`: {}".format(
                           self.fn_port, step.first_line or "no output"),
                       observed=listening or step.first_line or "no output")
        if step.rc != 0:
            return False
        self.fn_pid = reported_pid(step.output)
        if self.fn_pid:
            self.started_pids["fn"] = self.fn_pid
        self.facts["fn node"] = "native owner pid {} on port {} ({}), store {}".format(
            self.fn_pid or "?", self.fn_port, tag, self.store)
        return bool(listening)

    def stop_fn(self, name: str) -> Step:
        """SIGTERM by the recorded pid; SIGKILL only if it is still there after 60 s."""
        pid = self.started_pids.get("fn")
        if not pid:
            return self.sh(name, "echo 'no owner pid recorded; nothing to stop'")
        step = self.sh(name, """
kill -TERM {pid} 2>/dev/null || true
for i in $(seq 1 60); do kill -0 {pid} 2>/dev/null || break; sleep 1; done
if kill -0 {pid} 2>/dev/null; then kill -9 {pid}; echo "OWNER-KILLED-AFTER-60S"; else echo OWNER-GONE; fi
""".format(pid=pid), timeout=120, expect=None)
        self.started_pids.pop("fn", None)
        return step

    # -- INN --------------------------------------------------------------
    def inn_preflight(self):
        ports = (self.inn_port, self.nnrpd_port, self.fn_port, self.tap_out_port,
                 self.tap_in_port) + ((self.inn_security_port,) if self.inn_security else ())
        step = self.sh("INN install", """
P={prefix}
if [ ! -x $P/bin/innd ]; then echo "NO-INN $P"; exit 1; fi
echo "innd=$($P/bin/innconfval version 2>&1 | head -1)"
echo "tarball=$(cat $(dirname $P)/src/inn-{version}.tar.gz.sha256 2>/dev/null | head -1)"
# A connect probe, not `ss -ltn`: it is portable (the dry run is a laptop),
# and "something answers there" is the question, not "the kernel lists it".
for p in {ports}; do
  if python3 -c "import socket,sys; s=socket.socket(); s.settimeout(2); sys.exit(0 if s.connect_ex(('127.0.0.1',$p))==0 else 1)"; then
    echo "port $p BUSY"; else echo "port $p free"; fi
done
""".format(prefix=self.inn_prefix, version=self.inn_version,
           ports=" ".join(str(one) for one in ports)), expect=None)
        if step.rc != 0:
            raise GateError("no INN at {}: build it first, see docs/interop-inn.md"
                            .format(self.inn_prefix))
        busy = []
        for line in step.output.splitlines():
            if line.startswith("innd="):
                self.facts["inn version"] = line[len("innd="):].strip()
            if line.startswith("tarball="):
                self.facts["inn tarball sha256"] = line[len("tarball="):].strip()
            if " BUSY" in line:
                busy.append(line)
        self.facts["inn prefix"] = self.inn_prefix
        self.facts["ports"] = (
            "innd {} (transit), nnrpd {} (reader), fn owner {}, relay {} -> innd "
            "(fn's peer record names it), relay {} -> fn (innfeed.conf names it)".format(
                self.inn_port, self.nnrpd_port, self.fn_port, self.tap_out_port,
                self.tap_in_port))
        if busy:
            self.inconclusive(
                "ports-free", "{}: something was already listening there before the lab "
                "started; the lab touched nothing and started nothing.".format(
                    "; ".join(busy)),
                "a port the lab needs was already in use", observed="; ".join(busy))
            raise GateError("a port the lab needs is in use: {}".format("; ".join(busy)))
        self.check("ports-free", True, "", observed="all {} ports free".format(len(ports)))

    def inn_configure(self):
        """Write the five configuration files and cold-start history if absent."""
        user = self.sh("INN news user", "echo user=$(id -un) group=$(id -gn)")
        who = dict(part.split("=", 1) for part in user.output.split() if "=" in part)
        fields = dict(prefix=self.inn_prefix, inn_port=self.inn_port,
                      innfeed_port=self.tap_in_port, inn_identity=INN_PATH_IDENTITY,
                      fn_identity=FN_PATH_IDENTITY, user=who.get("user", "news"),
                      group=who.get("group", "news"))
        self.sh("INN directories", "mkdir -p {p}/etc {p}/bin {p}/spool/articles "
                "{p}/spool/incoming {p}/spool/outgoing {p}/spool/overview "
                "{p}/spool/tmp {p}/spool/innfeed {p}/db {p}/log {p}/run {p}/tmp".format(
                    p=self.inn_prefix))
        for name, template in (("inn.conf", INN_CONF),
                               ("incoming.conf", INCOMING_CONF),
                               ("newsfeeds", NEWSFEEDS),
                               ("innfeed.conf", INNFEED_CONF),
                               ("readers.conf", READERS_CONF)):
            contents = template.format(**fields)
            if name == "newsfeeds" and self.inn_controls:
                contents = contents.replace(":fn.*:Tm:", ":fn.*,control.checkgroups:Tm:")
            if name == "inn.conf" and self.inn_security:
                contents += ("tlscertfile: {p}/etc/security-cert.pem\n"
                             "tlskeyfile: {p}/etc/security-key.pem\n").format(p=self.inn_prefix)
            self.push_file(contents, "{}/etc/{}".format(self.inn_prefix, name), mode="640")
        if self.inn_security:
            self.inn_security_configure(fields)
        # innfeed appends for ever; a tail of it must be THIS run's.
        self.sh("truncate innfeed's log", ": > {p}/log/innfeed.log".format(
            p=self.inn_prefix))
        self.sh("INN history cold start", """
P={p}
if [ ! -f $P/db/history.dir ]; then
  : > $P/db/history
  $P/bin/makedbz -i -f $P/db/history
  mv $P/db/history.n.dir $P/db/history.dir
  mv $P/db/history.n.hash $P/db/history.hash
  mv $P/db/history.n.index $P/db/history.index
fi
if [ ! -f $P/db/active ]; then
  printf 'control 0000000000 0000000001 n\\njunk 0000000000 0000000001 n\\n' > $P/db/active
  : > $P/db/active.times
  : > $P/db/newsgroups
fi
ls $P/db
""".format(p=self.inn_prefix), timeout=300)
        self.sh("inncheck", "{} 2>&1 | head -20".format(self.bin("inncheck")),
                expect=None)
        for name in CONFIG_FILES:
            self.sh("INN {} as written".format(name),
                    "cat {}/etc/{}".format(self.inn_prefix, name))

    def inn_security_configure(self, fields):
        """Only the explicitly isolated test prefix; credentials are scratch files."""
        fields = dict(fields, access="RPIA" if self.inn_security_feed else "RA")
        self.push_file(READERS_SECURITY_CONF.format(**fields),
                       "{}/etc/readers-security.conf".format(self.inn_prefix), mode="640")
        openssl = (self.native_openssl_prefix.rstrip("/") + "/bin/openssl"
                   if self.native_openssl_prefix else "openssl")
        step = self.sh("INN protected-reader fixture", """
set -e
P={p}
umask 077
{ssl} rand -hex 24 > {run}/inn-security.password
{{ printf 'FNAUTH1\\nfn-lab\\n'; cat {run}/inn-security.password; }} > {run}/inn-security.fnauth
hash=$({ssl} passwd -6 -stdin < {run}/inn-security.password)
printf 'fn-lab:%s\\n' "$hash" > $P/db/security-newsusers
{ssl} req -x509 -newkey rsa:2048 -nodes -days 2 -sha256 \\
  -subj /CN=127.0.0.1 -addext subjectAltName=IP:127.0.0.1 \\
  -keyout $P/etc/security-key.pem -out $P/etc/security-cert.pem 2>/dev/null
{ssl} x509 -in $P/etc/security-cert.pem -noout -fingerprint -sha256
""".format(p=self.inn_prefix, run=self.run, ssl=shlex.quote(openssl)), expect=None)
        if step.rc != 0:
            raise GateError("cannot prepare INN protected-reader scratch fixture")

    def inn_security_start(self):
        step = self.sh("start protected nnrpd", """
P={p}
nohup $P/bin/nnrpd -D -4 127.0.0.1 -p {port} -c readers-security.conf \\
  > $P/log/nnrpd-security-stdout.log 2>&1 < /dev/null &
for i in $(seq 1 30); do
  if python3 -c "import socket,sys; s=socket.socket(); s.settimeout(2); sys.exit(0 if s.connect_ex(('127.0.0.1',{port}))==0 else 1)"; then
    echo "NNRPD-UP pid=$(cat $P/run/nnrpd-{port}.pid 2>/dev/null)"; exit 0; fi
  sleep 1
done
echo NNRPD-TIMEOUT; tail -10 $P/log/nnrpd-security-stdout.log; exit 1
""".format(p=self.inn_prefix, port=self.inn_security_port), timeout=90, expect=None)
        pid = reported_pid(step.output)
        if pid:
            self.started_pids["nnrpd-security"] = pid
        if step.rc != 0 or not pid:
            raise GateError("protected nnrpd did not start with an owned, recorded pid")
        self.facts["ports"] += "; protected nnrpd {} (STARTTLS reader)".format(self.inn_security_port)

    def innd_start(self, name: str, append=False) -> Step:
        return self.sh(name, """
P={p}
{reset}
nohup $P/bin/innd -d >> $P/log/innd-stdout.log 2>&1 < /dev/null &
for i in $(seq 1 60); do
  if $P/bin/ctlinnd -t 2 mode 2>/dev/null | grep -q 'Server running'; then
    echo "INND-UP pid=$(cat $P/run/innd.pid 2>/dev/null)"; exit 0
  fi
  sleep 1
done
echo INND-TIMEOUT; tail -20 $P/log/innd-stdout.log; exit 1
""".format(p=self.inn_prefix, reset="" if append else "rm -f $P/log/innd-stdout.log"),
            timeout=180, expect=None)

    def inn_start(self) -> bool:
        step = self.innd_start("start innd")
        up = step.rc == 0 and "INND-UP" in step.output
        self.check("innd-up", up, "innd did not come up: {}".format(step.first_line),
                   observed=step.first_line or "no output")
        if not up:
            self.facts["inn server"] = "innd did not start"
            return False
        pid = reported_pid(step.output)
        if pid:
            self.started_pids["innd"] = pid
        else:
            self.limitation("innd-pid-unrecorded",
                            "innd answered `Server running` but wrote no pid to "
                            "{}/run/innd.pid, so this run will not kill it".format(
                                self.inn_prefix))
        self.inn_running = True
        for group in GROUPS + (("control.checkgroups",) if self.inn_controls else ()):
            self.sh("ctlinnd newgroup {}".format(group),
                    "{} newgroup {} y $(id -un)".format(self.bin("ctlinnd"), group),
                    expect=None)
        self.sh("INN active", "cat {}/db/active".format(self.inn_prefix))
        # innd does not bring the innfeed channel up from a cold start here;
        # a reload does, and it is the same thing rc.news does after a change.
        self.sh("ctlinnd reload newsfeeds",
                "{} -t 10 reload newsfeeds 'inn lab' 2>&1; sleep 3; "
                "cat {}/run/innfeed.pid 2>/dev/null || echo NO-INNFEED-PID".format(
                    self.bin("ctlinnd"), self.inn_prefix), expect=None)
        nnrpd = self.sh("start nnrpd", """
P={p}
# `nnrpd -D` daemonises, so $! is the shell child that exits: the pid to
# remember is the one nnrpd writes itself, run/nnrpd-<port>.pid.
nohup $P/bin/nnrpd -D -p {port} > $P/log/nnrpd-stdout.log 2>&1 < /dev/null &
for i in $(seq 1 30); do
  if python3 -c "import socket,sys; s=socket.socket(); s.settimeout(2); sys.exit(0 if s.connect_ex(('127.0.0.1',{port}))==0 else 1)"; then
    echo "NNRPD-UP pid=$(cat $P/run/nnrpd-{port}.pid 2>/dev/null)"; exit 0; fi
  sleep 1
done
echo NNRPD-TIMEOUT; tail -10 $P/log/nnrpd-stdout.log; exit 1
""".format(p=self.inn_prefix, port=self.nnrpd_port), timeout=90, expect=None)
        if nnrpd.rc == 0 and "NNRPD-UP" in nnrpd.output:
            nnrpd_pid = reported_pid(nnrpd.output)
            if nnrpd_pid:
                self.started_pids["nnrpd"] = nnrpd_pid
            else:
                self.limitation(
                    "nnrpd-pid-unrecorded",
                    "nnrpd is listening on port {} but wrote no pid to "
                    "{}/run/nnrpd-{}.pid, so this run will not kill it".format(
                        self.nnrpd_port, self.inn_prefix, self.nnrpd_port))
            self.check("nnrpd-up", True, "", observed=nnrpd.first_line)
        else:
            self.check("nnrpd-up", False, "nnrpd did not come up on port {}: {}".format(
                self.nnrpd_port, nnrpd.first_line), observed=nnrpd.first_line or "no output")
        self.facts["inn server"] = "innd pid {} on port {}, nnrpd on port {}".format(
            pid, self.inn_port, self.nnrpd_port)
        return True

    def tap_start(self) -> bool:
        step = self.sh("start the relay", """
: > {log}
nohup python3 {run}/tap.py {log} {out}:{inn} {inport}:{fn} > {run}/tap.stdout 2>&1 < /dev/null &
echo $! > {run}/tap.pid
for i in $(seq 1 20); do
  up=0
  for p in {out} {inport}; do
    python3 -c "import socket,sys; s=socket.socket(); s.settimeout(2); sys.exit(0 if s.connect_ex(('127.0.0.1',$p))==0 else 1)" && up=$((up+1))
  done
  if [ $up = 2 ]; then echo "TAP-UP pid=$(cat {run}/tap.pid)"; exit 0; fi
  sleep 1
done
echo TAP-TIMEOUT; cat {run}/tap.stdout; exit 1
""".format(log=self.tap_log, run=self.run, out=self.tap_out_port, inn=self.inn_port,
           inport=self.tap_in_port, fn=self.fn_port), timeout=60, expect=None)
        up = step.rc == 0 and "TAP-UP" in step.output
        if up and reported_pid(step.output):
            self.started_pids["tap"] = reported_pid(step.output)
        self.check("tap-up", up, "the relay did not come up: {}".format(step.first_line),
                   observed=step.first_line or "no output")
        return up

    def inn_stop(self):
        """Only what this run started, and only by the pid it recorded."""
        for name in ("nnrpd-security", "nnrpd"):
            if name in self.started_pids:
                self.sh("stop " + name, "kill {} 2>/dev/null || true; echo stopped".format(
                    self.started_pids.pop(name)))
        if self.inn_running:
            self.sh("ctlinnd shutdown", "{} -t 5 shutdown 'inn lab done' 2>&1 || true"
                    .format(self.bin("ctlinnd")), expect=None)
            # `kill -0 0` asks about the whole process group and succeeds, so
            # an unknown innd pid must not be spelled 0: read the pid file.
            self.sh("innd and innfeed are gone", """
for i in $(seq 1 20); do
  kill -0 {pid} 2>/dev/null || break; sleep 1
done
kill -0 {pid} 2>/dev/null && echo INND-ALIVE || echo INND-GONE
pid=$(cat {p}/run/innfeed.pid 2>/dev/null || echo -1)
kill -0 $pid 2>/dev/null && echo INNFEED-ALIVE || echo INNFEED-GONE
""".format(pid=self.started_pids.get("innd")
           or "$(cat {}/run/innd.pid 2>/dev/null || echo -1)".format(self.inn_prefix),
           p=self.inn_prefix), expect=None)
            self.inn_running = False

    # -- the scenarios ----------------------------------------------------
    def reply_summary(self, found: dict | None) -> str:
        if not found:
            return "(no exchange on the relay)"
        return "{}: {}".format("+".join(found["verbs"]), " / ".join(
            one for one in (found["offer"], found["result"]) if one) or "(no reply)")

    def scenario_checkgroups_control(self):
        """Actual unsigned control traffic and C1 filing, not authorized discharge."""
        made = self.sh("fn control.checkgroups filing group", self.cd(self.operator(
            "group", "create", "control.checkgroups")), timeout=600, expect=None)
        if made.rc != 0:
            self.check("inn-checkgroups-control", False, "control filing group was refused",
                       observed=made.first_line)
            return
        msgid = self.ids["INN_CHECKGROUPS_ID"]
        payload = article(msgid, "actual unsigned checkgroups control", self.date,
            path=LAB_PATH_IDENTITY + "!not-for-mail",
            body="fn.checkgroups.proposed\tA group this unsigned control must not create.")
        payload = payload.replace(b"\r\n\r\n", b"\r\nControl: checkgroups\r\n\r\n", 1)
        path = self.put_article("checkgroups", payload)
        probe = self.drive_inn("offer", "--port {} --msgid {} --file {}".format(
            self.inn_port, shlex.quote(msgid), shell_fixture_path(path)), "actual checkgroups into INN")
        offered = self.payload(probe)
        self.sh("flush actual control feed", "{} -t 10 flush fn 2>&1 || true".format(
            self.bin("ctlinnd")), expect=None)
        found = self.wait_tap((self.tap_in_port, self.fn_port), msgid, "actual checkgroups control")
        transferred = bool(found and (
            (found["offer"].startswith("238") and found["result"].startswith("239"))
            or (found["offer"].startswith("335") and found["result"].startswith("235"))))
        observed = self.drive_inn("control-view", "--port {} --group control.checkgroups "
            "--other-group {} --msgid {}".format(self.fn_port, GROUP, shlex.quote(msgid)),
            "read actual control filing and unchanged group authority")
        view = self.payload(observed)
        served = self.octets_of(view)
        arrived = (found or {}).get("article") or b""
        preserved = bool(arrived and served and header_value(served, "Control") == "checkgroups"
                         and relay_changes_permitted(header_differences(arrived, served)))
        ok = bool(probe.rc == 0 and str(offered.get("offer", "")).startswith("335")
                  and str(offered.get("transfer", "")).startswith("235")
                  and transferred and observed.rc == 0 and view.get("ok") and preserved)
        self.facts["actual checkgroups control"] = "INN={}/{}; fn={}; filing={}; ordinary={}; proposed={}; Control={}".format(
            offered.get("offer"), offered.get("transfer"), self.reply_summary(found),
            view.get("filing", {}).get("ids"), view.get("ordinary", {}).get("ids"),
            view.get("active_rows"), header_value(served, "Control"))
        self.check("inn-checkgroups-control", ok, "actual checkgroups control failed its filing/no-execution assertion",
                   observed=self.facts["actual checkgroups control"])

    @staticmethod
    def protected_feed_acceptance(text, peer, msgid):
        wanted = {"accepted", "feed", "peer=" + peer,
                  "message-id=" + msgid, "code=235"}
        return next((line for line in text.splitlines()
                     if line.startswith("accepted feed ") and wanted.issubset(set(line.split()))), "")

    def wait_protected_feed(self, peer, msgid):
        started = time.monotonic()
        polls = 0
        line = ""
        path = self.node_dir + "/owner-main.log"
        while True:
            polls += 1
            done = self.host.sh("cat {} 2>/dev/null || true".format(path), 60)
            line = self.protected_feed_acceptance(done.stdout.decode("utf-8", "replace"),
                                                  peer, msgid)
            if line or time.monotonic() - started > self.feed_wait:
                break
            time.sleep(2)
        self.steps.append(Step("native protected-feed outcome", "cat {} ({} polls)".format(
            path, polls), 0, line or "no matching accepted code235", time.monotonic() - started))
        return line

    def scenario_protected_feed(self):
        """Native feed to nnrpd injection: TLS/auth scope, not relay preservation."""
        peer = "inn-security"
        pause = self.sh("pause clear INN feed", self.cd(self.operator(
            "peer", "feed", FN_PEER_NAME, "pause")), timeout=600, expect=None)
        if pause.rc != 0:
            self.check("fn-protected-injection", False, "clear feed could not be paused",
                       observed=pause.first_line)
            return
        added = self.sh("native protected INN injection peer", self.cd(self.operator(
            "peer", "add", peer, INN_PATH_IDENTITY, "127.0.0.1",
            str(self.inn_security_port), "-", "'fn.*'", "source-address", "127.0.0.1",
            self.run + "/inn-security.fnauth", "false", "false", "starttls", "127.0.0.1",
            self.inn_prefix + "/etc/security-cert.pem")), timeout=600, expect=None)
        if added.rc != 0:
            self.check("fn-protected-injection", False, "protected peer was refused",
                       observed=added.first_line)
            return
        self.sh("native protected peer as applied", self.cd(self.operator("peer", "list")),
                timeout=600, expect=None)
        msgid = self.ids["FN_PROTECTED_ID"]
        payload = article(msgid, "native protected INN injection", self.date)
        path = self.put_article("fn-protected", payload)
        posted = self.drive_inn("post", "--port {} --msgid {} --file {}".format(
            self.fn_port, shlex.quote(msgid), shell_fixture_path(path)), "POST for protected native feed")
        accepted = (self.wait_protected_feed(peer, msgid)
                    if posted.rc == 0 and self.payload(posted).get("ok") else "")
        probe = self.drive_inn("protected-read",
            "--port {} --cafile {} --password-file {} --group {} --msgid {}".format(
                self.inn_security_port,
                shell_fixture_path(self.inn_prefix + "/etc/security-cert.pem"),
                shell_fixture_path(self.run + "/inn-security.password"), GROUP,
                shlex.quote(msgid)), "read native protected injection from INN")
        read = self.payload(probe)
        served = self.octets_of(read)
        same_payload = bool(served and header_value(served, "Message-ID") == msgid
                            and header_value(served, "Subject") == header_value(payload, "Subject")
                            and header_differences(payload, served)["body_identical"])
        self.read_tap()
        clear = find_exchange(self.tap_text, "{}>{}".format(self.tap_out_port, self.inn_port), msgid)
        ok = bool(posted.rc == 0 and self.payload(posted).get("ok") and accepted and probe.rc == 0
                  and read.get("ok") and same_payload and clear is None)
        self.facts["fn protected injection"] = "{}; ARTICLE={}; payload={}; clear relay={}".format(
            accepted or "no accepted protected feed code235", read.get("article"),
            "same Message-ID/Subject/body" if same_payload else "missing or changed",
            "absent" if clear is None else self.reply_summary(clear))
        self.check("fn-protected-injection", ok,
                   "native protected injection did not establish every selected assertion",
                   observed=self.facts["fn protected injection"])

    def scenario_protected_read(self):
        probe = self.drive_inn("protected-read",
            "--port {} --cafile {} --password-file {} --group {} --msgid {}".format(
                self.inn_security_port,
                shell_fixture_path(self.inn_prefix + "/etc/security-cert.pem"),
                shell_fixture_path(self.run + "/inn-security.password"), GROUP,
                shlex.quote(self.ids["FN_POST_ID"])), "INN protected reader")
        result = self.payload(probe)
        original = self.held_octets.get("fn-article", b"")
        served = self.octets_of(result)
        diff = header_differences(original, served)
        ok = bool(probe.rc == 0 and result.get("ok") and original and served
                  and relay_changes_permitted(diff))
        self.facts["inn protected reader"] = (
            "STARTTLS={}; TLS={}; bad PASS={}; before login={}; PASS={}; "
            "ARTICLE={}; {}".format(result.get("starttls"), result.get("tls"),
                result.get("bad_pass"), result.get("before_login"), result.get("pass"),
                result.get("article"), describe_differences(diff)))
        self.check("inn-protected-reader", ok,
                   "the selected protected reader did not establish all TLS/auth/read assertions",
                   observed=self.facts["inn protected reader"])

    def scenario_fn_posts(self):
        """POST to the owner; its feed offers the article to innd; nnrpd serves it."""
        msgid = self.ids["FN_POST_ID"]
        posted = article(msgid, "posted on fn, fed to INN", self.date)
        self.post_file = self.put_article("fn-post", posted)
        probe = self.drive_inn("post", "--port {} --msgid '{}' --file {}".format(
            self.fn_port, msgid, self.post_file), name="POST {} to the fn owner".format(msgid))
        result = self.payload(probe)
        served = self.octets_of(result)
        self.facts["fn post"] = "POST='{}' article='{}' ARTICLE='{}'".format(
            result.get("post"), result.get("result"), result.get("article"))
        self.check("fn-post-240", bool(result.get("ok")),
                   "POST to the fn owner did not end 240 with the article readable: "
                   "POST='{}' result='{}' ARTICLE='{}' {}".format(
                       result.get("post"), result.get("result"), result.get("article"),
                       result.get("error", "")),
                   observed="{} / {}".format(result.get("post"), result.get("result")))
        if served:
            self.held_octets["fn-article"] = served
            diff = header_differences(posted, served)
            self.facts["fn post vs fn served"] = (
                "{}; the injected Path is `{}`".format(describe_differences(diff),
                                                       header_value(served, "Path")))
        found = self.wait_tap((self.tap_out_port, self.inn_port), msgid,
                              "fn's feed offers {} to innd".format(msgid))
        fed = (found or {}).get("article") or b""
        self.facts["fn feed to inn"] = "{}{}".format(
            self.reply_summary(found),
            "; the octets fed are {} to what fn serves".format(
                "identical" if fed == served else
                "not identical ({})".format(describe_differences(
                    header_differences(served, fed)))) if fed and served else "")
        ok = bool(found and found["verbs"] == ["IHAVE"]
                  and found["offer"].startswith("335")
                  and found["result"].startswith("235"))
        self.check("fn-feeds-inn", ok,
                   "fn's feed to innd did not end IHAVE/335/235 for {}: {}".format(
                       msgid, self.reply_summary(found)),
                   observed=self.reply_summary(found))
        if ok:
            self.inn_holds.append(msgid)
        read = self.drive_inn(
            "read", "--port {} --group {} --msgid '{}' --absent '{}'".format(
                self.nnrpd_port, GROUP, msgid, self.ids["ABSENT_ID"]),
            name="read {} back from INN's nnrpd".format(msgid))
        back = self.payload(read)
        inn_octets = self.octets_of(back)
        self.facts["inn read of fn's article"] = "GROUP='{}' ARTICLE='{}' absent='{}'".format(
            back.get("group"), back.get("article"), back.get("absent"))
        if inn_octets and served:
            self.inn_copy_of_fn = inn_octets
            diff = header_differences(served, inn_octets)
            self.facts["fn served vs inn served"] = (
                "{}; Path fn=`{}` inn=`{}`; Xref inn=`{}`".format(
                    describe_differences(diff), header_value(served, "Path"),
                    header_value(inn_octets, "Path"), header_value(inn_octets, "Xref")))
            self.check("inn-serves-fn-article", relay_changes_permitted(diff),
                       "nnrpd's copy of {} differs from fn's beyond Path and Xref: "
                       "{}".format(msgid, describe_differences(diff)),
                       observed=describe_differences(diff))
        else:
            self.record("inn-serves-fn-article", deploy_gate.NOT_EXERCISED,
                        "nnrpd did not serve {} ('{}'), so there is nothing to compare"
                        .format(msgid, back.get("article")),
                        blocker="the article did not reach INN or fn served none")
        if ok:
            dup = self.drive_inn("offer", "--port {} --msgid '{}' --file {}".format(
                self.inn_port, msgid, self.post_file),
                name="IHAVE {} into innd again".format(msgid))
            again = self.payload(dup)
            self.check("inn-duplicate-435", str(again.get("offer", "")).startswith("435"),
                       "a second IHAVE of fn's {} drew '{}' from innd, not 435".format(
                           msgid, again.get("offer")),
                       instance="fn-article", observed=str(again.get("offer")))

    def scenario_operator_post(self):
        """`operator post`: the offline submission verb, and what its feed carries."""
        msgid = self.ids["FN_OPERATOR_ID"]
        payload = article(msgid, "submitted through operator post", self.date)
        path = self.put_article("fn-operator", payload)
        step = self.sh("operator post {}".format(msgid), self.cd(self.operator(
            "post", "--message-id", shlex.quote(msgid), "--payload", path,
            "--group", GROUP)), timeout=600, expect=None)
        found = self.wait_tap((self.tap_out_port, self.inn_port), msgid,
                              "fn's feed offers {} to innd".format(msgid))
        fed = (found or {}).get("article") or b""
        path_header = header_value(fed, "Path") if fed else ""
        self.facts["operator post feed"] = "post rc={} ({}); {}; the fed article's Path " \
            "is {}".format(step.rc, step.output.strip().splitlines()[-1]
                           if step.output.strip() else "", self.reply_summary(found),
                           "`{}`".format(path_header) if path_header else "ABSENT")
        want = expected_injection(payload)
        present = {name: bool(fed and header_value(fed, name))
                   for name in ("Path", "Injection-Date", "Injection-Info")}
        if fed:
            self.facts["operator post vs fed"] = "{}; the fed Path is {}".format(
                describe_differences(header_differences(payload, fed)),
                "`{}`".format(path_header) if path_header else "ABSENT")
        self.facts["operator post injection"] = "expected {}; fed {}".format(
            ", ".join("{}={}".format(k, "yes" if v else "no") for k, v in want.items()),
            ", ".join("{}={}".format(k, "yes" if v else "no") for k, v in present.items()))
        ok = bool(found and found["offer"][:3] in ("335", "238")
                  and found["result"][:3] in ("235", "239")
                  and present == want
                  and FN_PATH_IDENTITY in path_header.split("!")[:-1])
        self.check("operator-post-feeds-inn", ok,
                   "`operator post` accepted {} (rc={}) and fn's feed offered it to innd, "
                   "which answered {}. The octets fed carry {} Path header and {}, where "
                   "{} was expected. `operator post` is a posting agent's submission, "
                   "so fn is its injecting agent: it adds Path and Injection-Info "
                   "(RFC 5537 3.5 items 8 to 10; RFC 5536 3.1.6 makes Path mandatory) "
                   "and adds Injection-Date only when the submission lacks Date or "
                   "Message-ID (3.5 item 11: MUST NOT when it had both). "
                   "books/owner.lisp fn-own-operator-submit is where fn does that."
                   .format(msgid, step.rc, self.reply_summary(found),
                           "a `{}`".format(path_header) if path_header else "NO",
                           self.facts["operator post injection"].split("; fed ")[1],
                           ", ".join(k for k, v in want.items() if v)),
                   observed=self.reply_summary(found))

    def scenario_from_invalid(self):
        """POST with `From: yue`, which names no address: 441, and nothing served.

        RFC 5536 3.1.2 makes From a mailbox-list (RFC 5322 3.6.2); the
        agents run of 2026-09-22 saw the image answer 240 and serve it."""
        msgid = self.ids["FN_FROM_ID"]
        posted = article(msgid, "a From that names no address", self.date, sender="yue")
        path = self.put_article("fn-from", posted)
        probe = self.drive_inn("post", "--port {} --msgid '{}' --file {}".format(
            self.fn_port, msgid, path), name="POST {} (From: yue) to the fn owner".format(
                msgid))
        result = self.payload(probe)
        reply, after = str(result.get("result", "")), str(result.get("article", ""))
        self.facts["fn post from yue"] = "POST='{}' article='{}' ARTICLE='{}'".format(
            result.get("post"), reply, after)
        self.check("fn-post-from-invalid-441",
                   reply.startswith("441") and after.startswith("430"),
                   "POST of {} with `From: yue` drew '{}' and ARTICLE then drew '{}': "
                   "RFC 5536 3.1.2 makes From a mailbox-list, so the posting must be "
                   "refused (441) and never served".format(msgid, reply, after),
                   observed="{} / ARTICLE {}".format(reply, after))

    def scenario_supplied_path(self):
        """POST with a supplied Path, as tin sends: 240, and fn prefixes it.

        D32 (2026-09-25): RFC 5537 3.4.1 lets a proto-article carry Path and
        3.2.1 has the injecting agent prepend its identity.  Until D32 fn
        answered `441 posting failed; Path must not be supplied`."""
        msgid = self.ids["FN_PATH_ID"]
        posted = article(msgid, "a Path the posting agent supplied", self.date,
                         path="not-for-mail")
        path = self.put_article("fn-path", posted)
        probe = self.drive_inn("post", "--port {} --msgid '{}' --file {}".format(
            self.fn_port, msgid, path), name="POST {} (Path: not-for-mail) to the fn owner"
            .format(msgid))
        result = self.payload(probe)
        reply, after = str(result.get("result", "")), str(result.get("article", ""))
        self.facts["fn post supplied path"] = "POST='{}' article='{}' ARTICLE='{}'".format(
            result.get("post"), reply, after)
        self.check("fn-post-supplied-path-240",
                   reply.startswith("240") and after.startswith("220"),
                   "POST of {} with `Path: not-for-mail` drew '{}' and ARTICLE drew '{}': "
                   "D32 accepts a supplied Path and prefixes it with {}!".format(
                       msgid, reply, after, FN_PATH_IDENTITY),
                   observed="{} / ARTICLE {}".format(reply, after))

    def scenario_inn_control(self):
        """INN's inbound path by hand: a transfer, a duplicate and a Path loop."""
        fed = article(self.ids["FED_ID"], "handed to INN, fed on to fn", self.date,
                      path="{}!not-for-mail".format(LAB_PATH_IDENTITY))
        loop = article(self.ids["LOOP_ID"], "a Path that names INN", self.date,
                       path="{}!{}!not-for-mail".format(INN_PATH_IDENTITY,
                                                        LAB_PATH_IDENTITY))
        self.fed_octets = fed
        self.fed_file = self.put_article("fed", fed)
        loop_file = self.put_article("inn-loop", loop)
        probe = self.drive_inn(
            "ihave", "--port {} --msgid '{}' --file {} --loop-msgid '{}' --loop-file {} "
            "--absent '{}'".format(self.inn_port, self.ids["FED_ID"], self.fed_file,
                                   self.ids["LOOP_ID"], loop_file, self.ids["ABSENT_ID"]),
            name="IHAVE {} into innd".format(self.ids["FED_ID"]))
        result = self.payload(probe)
        self.facts["inn control"] = (
            "MODE STREAM='{mode}' IHAVE='{offer}' transfer='{transfer}' duplicate="
            "'{dup}' loop='{loop}' CHECK(new)='{cn}' CHECK(dup)='{cd}'".format(
                mode=result.get("mode_stream"), offer=result.get("offer"),
                transfer=result.get("transfer"), dup=result.get("duplicate"),
                loop=result.get("loop_result"), cn=result.get("check_unknown"),
                cd=result.get("check_duplicate")))
        took = str(result.get("transfer", "")).startswith("235")
        self.check("inn-transfer-235", took,
                   "IHAVE {} into innd drew '{}' / '{}', not 335/235".format(
                       self.ids["FED_ID"], result.get("offer"), result.get("transfer")),
                   observed="{} / {}".format(result.get("offer"), result.get("transfer")))
        if took:
            self.inn_holds.append(self.ids["FED_ID"])
        self.check("inn-duplicate-435", str(result.get("duplicate", "")).startswith("435"),
                   "the second IHAVE of {} drew '{}', not 435".format(
                       self.ids["FED_ID"], result.get("duplicate")),
                   observed=str(result.get("duplicate")))
        self.check("inn-loop-437", str(result.get("loop_result", "")).startswith("437"),
                   "an article whose Path names {} drew '{}', not 437".format(
                       INN_PATH_IDENTITY, result.get("loop_result")),
                   observed=str(result.get("loop_result")))
        self.sh("INN history for {}".format(self.ids["FED_ID"]),
                "{} '{}' 2>&1 | head -3".format(self.bin("grephistory"), self.ids["FED_ID"]),
                expect=None)

    def scenario_innfeed_to_fn(self):
        """INN's own innfeed offers the article it took to fn, through the relay."""
        msgid = self.ids["FED_ID"]
        if msgid not in self.inn_holds:
            self.record("innfeed-feeds-fn", deploy_gate.NOT_EXERCISED,
                        "innd never took {}, so innfeed had nothing to offer".format(msgid),
                        blocker="the INN control transfer did not end 235")
            return
        self.sh("ctlinnd flush fn", "{} -t 10 flush fn 2>&1 || true".format(
            self.bin("ctlinnd")), expect=None)
        found = self.wait_tap((self.tap_in_port, self.fn_port), msgid,
                              "innfeed offers {} to fn".format(msgid))
        self.facts["innfeed to fn"] = self.reply_summary(found)
        ok = bool(found and (
            (found["offer"].startswith("238") and found["result"].startswith("239"))
            or (found["offer"].startswith("335") and found["result"].startswith("235"))))
        self.check("innfeed-feeds-fn", ok,
                   "innfeed's offer of {} to fn did not end 238/239 or 335/235: {}".format(
                       msgid, self.reply_summary(found)),
                   observed=self.reply_summary(found))
        self.sh("innfeed log", "tail -20 {}/log/innfeed.log 2>/dev/null; "
                "grep -h 'innfeed' /var/log/syslog 2>/dev/null | tail -8 || true".format(
                    self.inn_prefix), expect=None)
        got = self.drive_inn("fetch", "--port {} --msgid '{}'".format(self.fn_port, msgid),
                             name="read {} back from the fn owner".format(msgid))
        fn_octets = self.octets_of(self.payload(got))
        arrived = (found or {}).get("article") or b""
        if fn_octets and arrived:
            self.held_octets["inn-article"] = fn_octets
            diff = header_differences(arrived, fn_octets)
            self.check("fn-serves-inn-article", relay_changes_permitted(diff),
                       "fn serves {} differently from how innfeed sent it beyond Path "
                       "and Xref: {}".format(msgid, describe_differences(diff)),
                       observed=describe_differences(diff))
            served_path = header_value(fn_octets, "Path")
            names = [one for one in served_path.split("!") if one]
            self.check("fn-serves-own-path-identity", FN_PATH_IDENTITY in names[:-1],
                       "fn serves {} to a reader with `Path: {}`, which does not name "
                       "its own path identity {}: the Path it took by transit is served "
                       "unchanged, where RFC 5537 3.7 step 6 has a serving agent update "
                       "it as 3.2.1 describes (INN, the other serving agent here, served "
                       "`{}` for fn's article)".format(
                           msgid, served_path, FN_PATH_IDENTITY,
                           header_value(getattr(self, "inn_copy_of_fn", b""), "Path")),
                       observed="Path: {}".format(served_path))
            sender_xref = header_value(arrived, "Xref")
            served_xref = header_value(fn_octets, "Xref")
            self.check("fn-serves-no-sender-xref",
                       not sender_xref or served_xref != sender_xref,
                       "fn serves {} with the sender's `Xref: {}` -- INN's article "
                       "numbers, not fn's -- where RFC 5537 3.7 step 7 has a serving "
                       "agent remove it and specs/peering.md 2.3 says `Xref` is never "
                       "stored".format(msgid, served_xref),
                       observed="Xref: {}".format(served_xref or "(none)"))
            inn = self.drive_inn(
                "read", "--port {} --group {} --msgid '{}' --absent '{}'".format(
                    self.nnrpd_port, GROUP, msgid, self.ids["ABSENT_ID"]),
                name="read {} back from INN's nnrpd".format(msgid))
            inn_octets = self.octets_of(self.payload(inn))
            if inn_octets:
                self.facts["inn served vs fn served"] = (
                    "{}; Path inn=`{}` fn=`{}`; Xref inn=`{}` fn=`{}`".format(
                        describe_differences(header_differences(inn_octets, fn_octets)),
                        header_value(inn_octets, "Path"), header_value(fn_octets, "Path"),
                        header_value(inn_octets, "Xref"), header_value(fn_octets, "Xref")))
        else:
            self.record("fn-serves-inn-article", deploy_gate.NOT_EXERCISED,
                        "fn served no {} ('{}') or the relay carried no article".format(
                            msgid, self.payload(got).get("article")),
                        blocker="there was no transfer to read back")

    def offer_to_fn(self, msgid: str, path: str, name: str) -> dict:
        return self.payload(self.drive_inn(
            "offer", "--port {} --msgid '{}' --file {} --read".format(
                self.fn_port, msgid, path), name=name))

    def scenario_duplicates_and_loop(self):
        """A second offer of each article fn holds, and a Path naming fn itself."""
        facts = []
        for instance, msgid, path in (
                ("inn-article", self.ids["FED_ID"], getattr(self, "fed_file", "")),
                ("fn-article", self.ids["FN_POST_ID"], getattr(self, "post_file", ""))):
            if instance not in self.held_octets:
                self.record("fn-duplicate-435", deploy_gate.NOT_EXERCISED,
                            "fn does not hold {}, so a second offer is not a duplicate"
                            .format(msgid), instance=instance,
                            blocker="the article never reached fn")
                continue
            result = self.offer_to_fn(msgid, path, "IHAVE {} to fn again".format(msgid))
            facts.append("{}: IHAVE='{}'{}".format(
                instance, result.get("offer"),
                " transfer='{}'".format(result["result"]) if result.get("result") else ""))
            self.check("fn-duplicate-435", str(result.get("offer", "")).startswith("435"),
                       "a second IHAVE of {} drew '{}' from fn, not 435".format(
                           msgid, result.get("offer")),
                       instance=instance, observed=str(result.get("offer")))
        self.facts["duplicates"] = "; ".join(facts) or "(none offered)"
        msgid = self.ids["FN_LOOP_ID"]
        loop = article(msgid, "a Path that names fn", self.date,
                       path="{}!{}!not-for-mail".format(FN_PATH_IDENTITY,
                                                        LAB_PATH_IDENTITY))
        path = self.put_article("fn-loop", loop)
        result = self.offer_to_fn(msgid, path, "IHAVE {} (Path names {}) to fn".format(
            msgid, FN_PATH_IDENTITY))
        refused = (str(result.get("offer", "")).startswith("435")
                   or (str(result.get("offer", "")).startswith("335")
                       and str(result.get("result", "")).startswith("437")))
        stored = str(result.get("after", "")).startswith("220")
        self.facts["fn loop"] = "IHAVE='{}' transfer='{}' ARTICLE after='{}'".format(
            result.get("offer"), result.get("result"), result.get("after"))
        self.check("fn-loop-refused", refused and not stored,
                   "an article whose Path names {} drew IHAVE='{}' transfer='{}' from fn "
                   "and ARTICLE afterwards answered '{}'".format(
                       FN_PATH_IDENTITY, result.get("offer"), result.get("result"),
                       result.get("after")),
                   observed="{} / {} / {}".format(result.get("offer"), result.get("result"),
                                                  result.get("after")))

    def scenario_fn_term(self):
        """SIGTERM the owner, recover, restart, and reread what it held."""
        stop = self.stop_fn("SIGTERM the fn owner")
        self.check("fn-term-stopped", "OWNER-GONE" in stop.output,
                   "the owner did not exit within 60 s of SIGTERM: {}".format(
                       stop.first_line), observed=stop.first_line or "no output")
        survivor = self.sh("innd survived the fn owner's stop",
                           "{} -t 5 mode 2>&1 | head -2".format(self.bin("ctlinnd")),
                           expect=None)
        self.check("innd-survived-fn-term", "Server running" in survivor.output,
                   "innd was not running after the fn owner stopped: {}".format(
                       survivor.first_line), observed=survivor.first_line or "no output")
        self.sh("owner log (main)", "tail -12 {}/owner-main.log".format(self.node_dir),
                expect=None)
        rec = self.sh("fn recover", self.cd(self.operator("recover")), timeout=1800,
                      expect=None)
        self.check("fn-recover", rec.rc == 0,
                   "`recover` exited {}: {}".format(rec.rc, rec.first_line),
                   observed="rc={} {}".format(rec.rc, rec.first_line))
        status = self.sh("fn status after recover", self.cd(self.operator("status")),
                         timeout=600, expect=None)
        restarted = self.start_fn("after-term")
        results = []
        for instance, msgid in (("fn-article", self.ids["FN_POST_ID"]),
                                ("inn-article", self.ids["FED_ID"])):
            before = self.held_octets.get(instance)
            if not before or not restarted:
                self.record("fn-articles-survived-term", deploy_gate.NOT_EXERCISED,
                            "{}: {}".format(msgid, "fn never held it" if not before
                                            else "the owner did not restart"),
                            instance=instance, blocker="nothing to reread")
                continue
            got = self.payload(self.drive_inn(
                "fetch", "--port {} --msgid '{}'".format(self.fn_port, msgid),
                name="reread {} from fn after the restart".format(msgid)))
            after = self.octets_of(got)
            results.append("{} {}".format(instance, "identical" if after == before else
                                          "'{}'".format(got.get("article"))))
            self.check("fn-articles-survived-term", after == before,
                       "after SIGTERM, recover and restart fn answered '{}' for {}{}".format(
                           got.get("article"), msgid,
                           "" if not after else " with different octets: {}".format(
                               describe_differences(header_differences(before, after)))),
                       instance=instance, observed=str(got.get("article")))
        self.facts["fn term"] = "{}; recover rc={}; {}; {}".format(
            stop.first_line, rec.rc,
            status.output.strip().splitlines()[0] if status.output.strip() else "",
            ", ".join(results) or "(no reread)")

    def scenario_innd_cut(self):
        """The control: SIGKILL innd, restart it, and re-offer what it took."""
        pid = self.started_pids.get("innd")
        if not pid:
            self.skip("kill -9 innd and restart", "kill -9; innd -d",
                      "the lab never recorded an innd pid, so it will not kill one")
            return
        step = self.sh("kill -9 innd", """
kill -9 {pid} 2>/dev/null || true
for i in $(seq 1 20); do kill -0 {pid} 2>/dev/null || break; sleep 1; done
kill -0 {pid} 2>/dev/null && echo INND-ALIVE || echo INND-GONE
rm -f {p}/run/innd.pid {p}/run/control.ctl
""".format(pid=pid, p=self.inn_prefix), expect=None)
        self.inn_running = False
        self.started_pids.pop("innd", None)
        self.check("innd-died", "INND-GONE" in step.output,
                   "innd did not die on SIGKILL: {}".format(step.first_line),
                   observed=step.first_line or "no output")
        again = self.innd_start("restart innd after the kill", append=True)
        if not (again.rc == 0 and "INND-UP" in again.output):
            self.check("innd-restarted", False,
                       "innd did not come back after the SIGKILL: {}".format(
                           again.first_line), observed=again.first_line or "no output")
            self.facts["innd cut"] = "innd did not restart"
            return
        back = reported_pid(again.output)
        if back:
            self.started_pids["innd"] = back
        self.inn_running = True
        self.check("innd-restarted", True, "", observed=again.first_line)
        facts = []
        for instance, msgid, path in (
                ("inn-article", self.ids["FED_ID"], getattr(self, "fed_file", "")),
                ("fn-article", self.ids["FN_POST_ID"], getattr(self, "post_file", ""))):
            if msgid not in self.inn_holds:
                self.record("inn-history-survived-kill", deploy_gate.NOT_EXERCISED,
                            "innd never acknowledged {}".format(msgid), instance=instance,
                            blocker="nothing in INN's history to survive")
                continue
            result = self.payload(self.drive_inn(
                "offer", "--port {} --msgid '{}' --file {}".format(
                    self.inn_port, msgid, path),
                name="after innd's restart, IHAVE {}".format(msgid)))
            facts.append("{} IHAVE='{}'".format(instance, result.get("offer")))
            self.check("inn-history-survived-kill",
                       str(result.get("offer", "")).startswith("435"),
                       "after innd's SIGKILL and restart, IHAVE {} drew '{}', not 435"
                       .format(msgid, result.get("offer")),
                       instance=instance, observed=str(result.get("offer")))
        self.facts["innd cut"] = "; ".join(facts)

    # -- evidence ---------------------------------------------------------
    def read_tap(self):
        """Keep the relay's whole log before cleanup removes the tree it is in."""
        done = self.host.sh("cat {} 2>/dev/null || true".format(self.tap_log), 60)
        self.tap_text = done.stdout.decode("utf-8", "replace") or self.tap_text

    def transcript(self) -> list:
        """The relay's log as the two conversations it carried, decoded."""
        text = self.tap_text
        lines = []
        for pair, label in (("{}>{}".format(self.tap_out_port, self.inn_port),
                             "fn's feed -> innd"),
                            ("{}>{}".format(self.tap_in_port, self.fn_port),
                             "innfeed -> fn")):
            for number, stream in enumerate(tap_connections(text, pair), 1):
                lines.append("### {} (relay {}), connection {}".format(label, pair, number))
                lines.append("")
                lines.append("```")
                parsed = exchanges(stream["client"], stream["server"])
                lines.append("S: " + parsed["greeting"])
                for entry in parsed["exchanges"]:
                    lines.append("C: " + entry["command"])
                    if entry["article"] is not None and entry["command"].split()[:1] != [
                            "TAKETHIS"]:
                        lines.append("S: " + entry["reply"])
                        for one in entry["article"].decode("utf-8", "replace").split(
                                "\r\n")[:-1]:
                            lines.append("C:   " + one)
                        lines.append("C: .")
                        lines.append("S: " + entry["result"])
                    elif entry["article"] is not None:
                        for one in entry["article"].decode("utf-8", "replace").split(
                                "\r\n")[:-1]:
                            lines.append("C:   " + one)
                        lines.append("C: .")
                        lines.append("S: " + entry["reply"])
                    else:
                        lines.append("S: " + entry["reply"])
                lines += ["```", ""]
        return lines or ["(the relay carried nothing)", ""]

    def evidence(self, path, started, elapsed):
        written = super().evidence(path, started, elapsed)
        try:
            extra = self.transcript()
        except Exception as error:          # the record must still be written
            extra = ["(the relay log could not be read: {})".format(error), ""]
        text = written.read_text()
        marker = "## Raw step output"
        section = "\n".join(["## The relay's transcript", "",
                             "Every octet each server sent the other on the two transit",
                             "connections, as `tap.py` logged it. `C:` is the side that",
                             "connected, `S:` the side that listened; article lines are",
                             "indented and dot-unstuffed.", ""] + extra)
        written.write_text(text.replace(marker, section + "\n" + marker, 1))
        return written

    def scenario_bidirectional_streaming(self):
        """SCN-1041: each actual feed transfers a fresh subject and it reads back."""
        added = self.sh("enable fn's INN streaming peer", self.cd(self.operator(
            "peer", "add", FN_PEER_NAME, INN_PATH_IDENTITY, "127.0.0.1",
            str(self.tap_out_port), "'fn.*'", "'fn.*'", "127.0.0.1", "true")),
            timeout=600, expect=None)
        if added.rc != 0:
            for direction in ("fn-to-inn", "inn-to-fn"):
                self.check("bidirectional-streaming", False,
                           "native operator refused the streaming peer record",
                           instance=direction, observed=added.first_line)
            return
        for direction, ident, port, pair in (
                ("fn-to-inn", "FN_STREAM_ID", self.nnrpd_port,
                 (self.tap_out_port, self.inn_port)),
                ("inn-to-fn", "INN_STREAM_ID", self.fn_port,
                 (self.tap_in_port, self.fn_port))):
            msgid = self.ids[ident]
            payload = article(msgid, "bidirectional streaming " + direction, self.date,
                              path=LAB_PATH_IDENTITY + "!not-for-mail"
                              if direction == "inn-to-fn" else None)
            path = self.put_article("stream-" + direction, payload)
            phase = "post" if direction == "fn-to-inn" else "stream"
            entry = self.payload(self.drive_inn(phase,
                "--port {} --msgid '{}' --file {}".format(
                    self.fn_port if phase == "post" else self.inn_port, msgid, path),
                name="submit fresh streaming " + direction))
            if direction == "inn-to-fn":
                self.sh("flush fresh INN streaming article", "{} -t 10 flush fn 2>&1 || true"
                        .format(self.bin("ctlinnd")), expect=None)
            found = self.wait_tap(pair, msgid, "streaming " + direction)
            back = self.payload(self.drive_inn("fetch",
                "--port {} --msgid '{}'".format(port, msgid),
                name="read back streaming " + direction))
            served = self.octets_of(back)
            transferred = (found or {}).get("article") or b""
            source = self.octets_of(entry) if direction == "fn-to-inn" else payload
            feed_comparison = header_differences(source, transferred)
            comparison = header_differences(transferred, served)
            ok = (bool(entry.get("ok")) and streaming_transfer_completed(found, msgid)
                  and str(back.get("article", "")).startswith("220")
                  and bool(source) and header_value(source, "Message-ID") == msgid
                  and header_value(served, "Message-ID") == msgid
                  and header_value(transferred, "Message-ID") == msgid
                  and relay_changes_permitted(feed_comparison)
                  and relay_changes_permitted(comparison))
            self.check("bidirectional-streaming", ok,
                       "{} lacked a completed subject-matched streaming transfer or "
                       "unchanged receiver content: {}; {}".format(
                           direction, self.reply_summary(found), describe_differences(comparison)),
                       instance=direction,
                       observed="{}; ARTICLE {}; source-to-feed {}; feed-to-reader {}".format(
                           self.reply_summary(found), back.get("article"),
                           describe_differences(feed_comparison),
                           describe_differences(comparison)))

    # -- the whole lab ----------------------------------------------------
    def execute(self):
        self.preflight()
        self.inn_preflight()
        self.ship()
        self.native_subject()
        self.native_node()
        self.inn_configure()
        if not self.inn_start():
            raise GateError("innd did not start; see the evidence for its log")
        if self.inn_security:
            self.inn_security_start()
        if not self.tap_start():
            raise GateError("the relay did not start")
        if not self.start_fn("main"):
            raise GateError("the native owner did not reach LISTENING")
        self.sh("fn CAPABILITIES", self.cd("python3 {}/inn.py caps --port {}".format(
            self.run, self.fn_port)), expect=None)
        self.scenario_fn_posts()
        if self.inn_security:
            self.scenario_protected_read()
        self.scenario_operator_post()
        self.scenario_from_invalid()
        self.scenario_supplied_path()
        self.scenario_inn_control()
        self.scenario_innfeed_to_fn()
        self.scenario_duplicates_and_loop()
        if self.inn_controls:
            self.scenario_checkgroups_control()
        if self.inn_streaming:
            self.scenario_bidirectional_streaming()
        if self.inn_security_feed:
            self.scenario_protected_feed()
        self.scenario_fn_term()
        self.scenario_innd_cut()

    def cleanup(self):
        """No process of ours left on the box; the INN install stays."""
        try:
            self.read_tap()
        except Exception:               # the record says the relay carried nothing
            pass
        if "fn" in self.started_pids:
            self.stop_fn("stop the fn owner")
        if "tap" in self.started_pids:
            self.sh("stop the relay", "kill {} 2>/dev/null || true; echo stopped".format(
                self.started_pids.pop("tap")))
        self.inn_stop()
        # The deploy path is in the owner's and the relay's argv; this script
        # reaches bash on stdin, so the pattern is in no command line of ours.
        self.sh("stray lab processes", "if pgrep -f -- \"{}/\" >/dev/null 2>&1; then "
                "echo STRAY; pgrep -af -- \"{}/\"; else echo CLEAN; fi".format(
                    self.deploy, self.deploy), expect=None)
        if not self.keep:
            self.sh("remove the deploy tree", "rm -rf {}".format(self.deploy))
        self.release_deploy_lock()
        self.sh("the INN install is left in place",
                "ls -d {} && echo INN-KEPT".format(self.inn_prefix), expect=None)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("commit", nargs="?", default="dev",
                        help="the commit-ish whose launcher and drivers are shipped")
    parser.add_argument("--host", default=DEFAULT_HOST)
    parser.add_argument("--tree", default="dev", help="deploy identity prefix")
    parser.add_argument("--repo", default=None,
                        help="the fn worktree to read the commit from and write "
                             "evidence into (default: the one this command was "
                             "invoked from)")
    parser.add_argument("--evidence", default=None)
    parser.add_argument("--keep", action="store_true",
                        help="leave the deploy tree on the host")
    parser.add_argument("--dry-run", action="store_true",
                        help="run every script through local bash with HOME redirected")
    parser.add_argument("--home", default=None, help="the fake HOME for --dry-run")
    parser.add_argument("--native-image", default=None,
                        help="execution-host path to the saved native image (required: "
                             "the fn side is the native image or the lab does not run)")
    parser.add_argument("--native-openssl-prefix", default=None,
                        help="FN_OPENSSL_PREFIX for the image (the OpenSSL it was built "
                             "against; hbox: /tank/fn/toolchains/openssl-3.5.8)")
    parser.add_argument("--lab-root", default=DEFAULT_LAB_ROOT,
                        help="where the run's tree, store and logs live on the host")
    parser.add_argument("--inn-version", default=DEFAULT_INN_VERSION)
    parser.add_argument("--inn-prefix", default=None,
                        help="the INN install; the default is "
                             "{}/<version>".format(DEFAULT_INN_ROOT))
    parser.add_argument("--inn-port", type=int, default=INN_PORT)
    parser.add_argument("--nnrpd-port", type=int, default=NNRPD_PORT)
    parser.add_argument("--inn-security", action="store_true",
                        help="add certificate-verified STARTTLS and USER/PASS reader "
                             "checks; requires a separate TLS-capable --inn-prefix")
    parser.add_argument("--inn-controls", action="store_true",
                        help="actual unsigned Control: checkgroups via INN innfeed, "
                             "control-group filing and no automatic group creation")
    parser.add_argument("--inn-streaming", action="store_true",
                        help="complete both actual feed directions by CHECK/TAKETHIS "
                             "with fresh articles and receiver readback")
    parser.add_argument("--inn-security-feed", action="store_true",
                        help="also run native fn STARTTLS/USER-PASS IHAVE into nnrpd's "
                             "injection endpoint; requires --inn-security")
    parser.add_argument("--inn-security-port", type=int, default=INN_SECURITY_PORT)
    parser.add_argument("--fn-port", type=int, default=FN_PORT)
    parser.add_argument("--tap-out-port", type=int, default=TAP_OUT_PORT)
    parser.add_argument("--tap-in-port", type=int, default=TAP_IN_PORT)
    parser.add_argument("--feed-wait", type=int, default=90,
                        help="seconds to wait for a feed exchange on the relay")
    parser.add_argument("--overlay", action="append", default=[],
                        help="a directory copied over the shipped tree before it runs")
    args = parser.parse_args(argv)
    if not args.native_image:
        parser.error("--native-image is required: the fn side is the native image "
                     "or the lab does not run (D07)")
    ports = (args.inn_port, args.nnrpd_port, args.fn_port, args.tap_out_port,
             args.tap_in_port)
    if args.inn_security_feed and not args.inn_security:
        parser.error("--inn-security-feed requires --inn-security")
    if args.inn_security:
        if not args.inn_prefix or args.inn_prefix.rstrip("/") == "{}/{}".format(
                DEFAULT_INN_ROOT, args.inn_version):
            parser.error("--inn-security needs a separate TLS-capable --inn-prefix")
        ports += (args.inn_security_port,)
    if len(set(ports)) != len(ports):
        parser.error("all selected ports must differ: {}".format(ports))

    repo = Path(args.repo).resolve() if args.repo else repo_root()
    commit, rev = resolve(repo, args.commit)
    if args.dry_run:
        if args.home is None:
            parser.error("--dry-run needs --home")
        host: Host = LocalHost(Path(args.home).resolve())
    else:
        host = SshHost(args.host)
    overlays = [Path(one).resolve() for one in args.overlay]
    lab = InnLab(host, repo, commit, rev, args.tree,
                 overlay=overlays[0] if overlays else None,
                 keep=args.keep, nntplib_python="none",
                 acl2=farm.host_settings(args.host)["acl2"],
                 native_image=args.native_image,
                 native_openssl_prefix=args.native_openssl_prefix,
                 lab_root=args.lab_root,
                 inn_prefix=args.inn_prefix or "{}/{}".format(
                     DEFAULT_INN_ROOT, args.inn_version),
                 inn_version=args.inn_version, inn_port=args.inn_port,
                 nnrpd_port=args.nnrpd_port, fn_port=args.fn_port,
                 tap_out_port=args.tap_out_port, tap_in_port=args.tap_in_port,
                 feed_wait=args.feed_wait, extra_overlays=overlays[1:],
                 inn_security=args.inn_security, inn_security_port=args.inn_security_port,
                 inn_security_feed=args.inn_security_feed, inn_controls=args.inn_controls,
                 inn_streaming=args.inn_streaming)
    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    failure = None
    try:
        lab.execute()
    except GateError as error:
        failure = str(error)
        lab.limitation("lab-stopped-early", "the lab stopped early: {}".format(error))
    finally:
        try:
            lab.cleanup()
        except Exception as error:      # cleanup must never hide the result
            lab.limitation("cleanup-unfinished", "cleanup did not finish: {}: {}".format(
                type(error).__name__, error))
    elapsed = time.monotonic() - clock
    lab.finalize_findings()
    date = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
    target = evidence_path(args.evidence, repo, "inn-lab-{}-{}.md".format(rev, date))
    lab.evidence(target, started, elapsed)
    print("evidence: {}".format(target))
    report(lab)
    if failure:
        print("lab error: {}".format(failure))
    return lab.exit_code(failure)


if __name__ == "__main__":
    sys.exit(main())

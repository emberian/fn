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
ABSENT_ID = "<inn-lab-absent-{tag}@example.invalid>"
ID_TEMPLATES = ("FED_ID", "LOOP_ID", "LOOP2_ID", "FN_POST_ID", "FN_OPERATOR_ID",
                "FN_LOOP_ID", "ABSENT_ID")


def message_ids(tag: str) -> dict:
    """This run's Message-IDs, keyed by the template name."""
    return {name: globals()[name].format(tag=tag) for name in ID_TEMPLATES}


def article(msgid: str, subject: str, date: str, path: str | None = None,
            group: str = GROUP, body: str = "From the fn INN interop lab.") -> bytes:
    """One article's octets, CRLF lines, RFC 5536 order.

    `path` None is an article as a posting agent writes it: RFC 5537 section
    3.4.1 has the injecting agent add Path, and fn's POST refuses one that is
    already there (books/nntp-post.lisp, `:path-present`)."""
    lines = (["Path: {}".format(path)] if path is not None else []) + [
        "From: lab@example.invalid",
        "Newsgroups: " + group,
        "Subject: " + subject,
        "Date: " + date,
        "Message-ID: " + msgid,
        "",
        body]
    return ("\r\n".join(lines) + "\r\n").encode("ascii")


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
import argparse, base64, json, socket, sys


class Wire:
    def __init__(self, port, timeout=30):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=timeout)
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="phase", required=True)
    for name in ("read", "ihave", "offer", "post", "fetch", "caps"):
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
    args = parser.parse_args()
    handler = {"read": read, "ihave": ihave, "offer": offer, "post": post,
               "fetch": fetch, "caps": caps}[args.phase]
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
                 "fn term", "innd cut")
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
            "fn's outbound feed", ("",)),
        "inn-transfer-235": ("a hand-made IHAVE into innd draws 335 then 235", ("",)),
        "inn-duplicate-435": (
            "a second IHAVE of an article innd holds draws 435", ("", "fn-article")),
        "inn-loop-437": ("an article whose Path names INN draws 437 from innd", ("",)),
        "innfeed-feeds-fn": (
            "INN's innfeed offered an article to fn and fn took it (238/239 or "
            "335/235)", ("",)),
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
                 extra_overlays=(), feed_wait=90, **kwargs):
        super().__init__(*args, **kwargs)
        if not native_image:
            raise GateError("the fn side is the native image or the lab does not run "
                            "(D07): --native-image is required")
        self.native_image = native_image
        self.native_openssl_prefix = native_openssl_prefix
        self.inn_prefix = inn_prefix
        self.inn_version = inn_version
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

    def native(self, *words) -> str:
        """The packaged public entry, from the shipped tree, with the named image.

        `env` in front because the owner is started as `nohup <command> &` and
        nohup execs its first word (tools/v0_matrix.py `native_command`)."""
        env = ""
        if self.native_openssl_prefix:
            env = "FN_OPENSSL_PREFIX={} ".format(shlex.quote(self.native_openssl_prefix))
        return "env {}FN_NATIVE_HOST={} packaging/fn-native {}".format(
            env, shlex.quote(self.native_image), " ".join(words))

    def operator(self, *words) -> str:
        return self.native("operator", self.config, *words)

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
                 self.tap_in_port)
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
        self.check("ports-free", True, "", observed="all five ports free")

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
            self.push_file(template.format(**fields),
                           "{}/etc/{}".format(self.inn_prefix, name), mode="640")
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
        for group in GROUPS:
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
        if "nnrpd" in self.started_pids:
            self.sh("stop nnrpd", "kill {} 2>/dev/null || true; echo stopped".format(
                self.started_pids.pop("nnrpd")))
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
        ok = bool(found and found["offer"][:3] in ("335", "238")
                  and found["result"][:3] in ("235", "239"))
        self.check("operator-post-feeds-inn", ok,
                   "`operator post` accepted {} (rc={}) and fn's feed offered it to innd, "
                   "which answered {}. The octets fed carry {} Path header: `operator "
                   "post` stores the payload as submitted, with no injection (no Path, "
                   "no Injection-Info; RFC 5536 3.1.6 makes Path mandatory), and the "
                   "outbound feed relays it without prepending fn's path identity "
                   "(RFC 5537 3.6), so INN has no Path to accept it under.".format(
                       msgid, step.rc, self.reply_summary(found),
                       "a `{}`".format(path_header) if path_header else "NO"),
                   observed=self.reply_summary(found))

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
        if not self.tap_start():
            raise GateError("the relay did not start")
        if not self.start_fn("main"):
            raise GateError("the native owner did not reach LISTENING")
        self.sh("fn CAPABILITIES", self.cd("python3 {}/inn.py caps --port {}".format(
            self.run, self.fn_port)), expect=None)
        self.scenario_fn_posts()
        self.scenario_operator_post()
        self.scenario_inn_control()
        self.scenario_innfeed_to_fn()
        self.scenario_duplicates_and_loop()
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
    if len(set(ports)) != len(ports):
        parser.error("the five ports must differ: {}".format(ports))

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
                 feed_wait=args.feed_wait, extra_overlays=overlays[1:])
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

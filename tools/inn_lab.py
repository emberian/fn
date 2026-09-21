#!/usr/bin/env python3
"""A real INN news server on one side of the wire and an fn node on the other.

tools/deploy_gate.py establishes that one commit serves, dies and recovers.
tools/twonode_gate.py puts two fn nodes beside each other.  This is the third
question, and the only one whose answer does not come from our own code: does
fn meet *legacy Usenet* -- InterNetNews, the server most of the remaining
Usenet runs -- and where exactly does it fail to.

The INN install is not shipped or torn down: it is the lab.  It lives at
``--inn-prefix`` (``/tank/fn/inn/<version>`` on hbox), was built from the
release tarball whose sha256 is recorded in ``tests/inn/pin.json``, runs as
the ordinary user on high ports, and stays on the box between runs.  What this
tool ships per run is the fn commit, in tools/deploy_gate.py's ``~/fn-deploy``
shape, with the same certificate machinery, the same step accounting and the
same evidence renderer -- reused by subclassing ``DeployGate``, not copied.

The scenarios are specs/peering.md section 5's, restricted to what the tree
supports today.  Every one the tree cannot support is a recorded skip carrying
the exact reply that made it a skip, never a weaker scenario passing under the
same name:

* ``read``     -- INN's nnrpd serves an article back, read by a raw-socket
                  client (nntplib went out with Python 3.13/PEP 594).  fn has
                  no NNTP *client*, so the reader here is the lab's, not fn's:
                  that gap is recorded, not papered over.
* ``ihave``    -- ``IHAVE``/``335``/article/``235`` into INN over a raw
                  socket, then the same offer again for ``435``, then an
                  article whose ``Path`` already names INN for ``437``.  This
                  is INN's *inbound* path, the one fn's feed lane will drive.
* ``offer``    -- INN's own ``innfeed`` offering an article to the fn node,
                  plus the same offer by hand.  Today fn answers ``500``;
                  the exact reply and innfeed's reaction to it are the record.
* ``fn-cut``   -- SIGKILL of the fn node inside a session, recovery, reread.
* ``innd-cut`` -- SIGKILL of ``innd`` and a restart: INN's own recovery, as
                  the control that says the lab's assertions can tell a
                  surviving article from a lost one.

    python3 tools/inn_lab.py --host hbox
    python3 tools/inn_lab.py HEAD --host hbox --keep

Dry run.  ``--dry-run --home DIR --inn-prefix DIR/fake-inn`` runs every script
through bash on this machine with ``HOME`` redirected and no ssh, exactly as
the two gates' dry runs do; tests/test_inn_lab.py drives it against
``tests/inn_lab_fake``, a stand-in INN whose replies are that directory's and
say nothing whatever about INN or about fn.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

import deploy_gate                                            # noqa: E402
import farm                                                   # noqa: E402
from deploy_gate import (EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN,  # noqa: E402
                         evidence_path, repo_root, report,
                         GROUPS, GateError, Host, LocalHost, SshHost, Step,
                         resolve)

DEFAULT_HOST = "hbox"
DEFAULT_INN_VERSION = "2.7.4"
DEFAULT_INN_ROOT = "/tank/fn/inn"
# The port scheme, in one place: INN's own ports plus 10000 so nothing is
# privileged and nothing collides with fn's 8119 reader default, and fn's
# listener a decade above them so a stray connection to the wrong port is
# obvious in a log rather than silently answered by the other server.
INN_PORT = 11119          # innd: transit (IHAVE/CHECK/TAKETHIS) and reader handoff
NNRPD_PORT = 11120        # nnrpd: the reader daemon, read-back only
FN_PORT = 11190           # the fn node's listener; innfeed.conf names this port

INN_PATH_IDENTITY = "inn.hbox.test"
FN_PATH_IDENTITY = "fnA.hbox.test"


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
# run of the transfer scenario a duplicate of the first.  Two runs an hour
# apart on the same box must both be able to offer a new article.
FED_ID = "<inn-lab-fed-{tag}@example.invalid>"
LOOP_ID = "<inn-lab-loop-{tag}@example.invalid>"
LOOP2_ID = "<inn-lab-loop2-{tag}@example.invalid>"
OFFER_ID = "<inn-lab-offer-{tag}@example.invalid>"
FN_SEED_ID = "<inn-lab-fn-seed-{tag}@example.invalid>"
FN_CUT_ID = "<inn-lab-fn-cut-{tag}@example.invalid>"
UNCERTAIN_ID = "<inn-lab-uncertain-{tag}@example.invalid>"
ABSENT_ID = "<inn-lab-absent-{tag}@example.invalid>"
ID_TEMPLATES = ("FED_ID", "LOOP_ID", "LOOP2_ID", "OFFER_ID", "FN_SEED_ID",
                "FN_CUT_ID", "UNCERTAIN_ID", "ABSENT_ID")


def message_ids(tag: str) -> dict:
    """This run's Message-IDs, keyed by the template name."""
    return {name: globals()[name].format(tag=tag) for name in ID_TEMPLATES}

# --------------------------------------------------------------------------
# INN's configuration.  These four templates are the lab: docs/interop-inn.md
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
NEWSFEEDS = """\
# fn INN interop lab -- generated by tools/inn_lab.py.
# ME's exclusion sub-field: an incoming article whose Path names one of these
# sites is refused 437 (innd/art.c ME.Exclusions).
ME/{inn_identity}:*::
innfeed!:!*:Tc,Wnm*:{prefix}/bin/innfeed -y
fn:fn.*:Tm:innfeed!
"""

INNFEED_CONF = """\
# fn INN interop lab -- the outbound half: INN offers fn.* to the fn node.
pid-file:        innfeed.pid
log-file:        innfeed.log
status-file:     innfeed.status
backlog-directory: {prefix}/spool/innfeed
use-mmap:        false
initial-reconnect-time: 5
max-reconnect-time:     60

peer fn {{
    ip-name:             127.0.0.1
    port-number:         {fn_port}
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
# the driver that runs on the host

INN_DRIVER = r'''#!/usr/bin/env python3
"""The INN lab's phases.  No fn module is imported; Conn is deploy_gate's.

Python 3.13 removed nntplib (PEP 594), so every NNTP exchange here is a raw
socket.  That is not a workaround: a transit client written against the wire
is the only kind that can send a deliberately malformed Path or stop in the
middle of a transfer, which is what three of these phases do.
"""
import argparse, email.utils, json, os, socket, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from drive import Conn                 # tools/deploy_gate.py's driver


def article(msgid, group, subject, path, body="From the fn INN interop lab."):
    """One article as a list of lines, RFC 5536 order, with a Date INN needs."""
    return ["Path: {}!not-for-mail".format(path),
            "From: lab@example.invalid",
            "Newsgroups: " + group,
            "Subject: " + subject,
            "Message-ID: " + msgid,
            "Date: " + email.utils.formatdate(localtime=False),
            "",
            body]


def send_block(conn, lines):
    """A multi-line block, dot-stuffed, terminated: RFC 3977 section 3.1.1."""
    payload = b""
    for one in lines:
        raw = one.encode()
        payload += (b"." + raw if raw.startswith(b".") else raw) + b"\r\n"
    conn.sock.sendall(payload + b".\r\n")


def read(args):
    """Read back from INN's nnrpd what the transit path stored."""
    conn = Conn(args.port)
    out = {"greeting": conn.greeting}
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    out["capabilities"] = caps
    out["list_active"] = conn.cmd("LIST ACTIVE", multiline=True)
    out["group"] = conn.cmd("GROUP " + args.group)[0]
    status, lines = conn.cmd("ARTICLE " + args.msgid, multiline=True)
    out["article"] = status
    out["article_lines"] = lines
    out["absent"] = conn.cmd("ARTICLE " + args.absent, multiline=True)[0]
    conn.close()
    body = [one for one in lines if one.startswith("Message-ID:")]
    out["served_message_id"] = body[0] if body else ""
    out["path"] = ([one for one in lines if one.startswith("Path:")] or [""])[0]
    out["ok"] = (out["group"].startswith("211")
                 and out["article"].startswith("220")
                 and args.msgid in out["served_message_id"]
                 and out["absent"].startswith("43"))
    return out


def ihave(args):
    """IHAVE into INN: the transfer, the duplicate and the Path loop."""
    conn = Conn(args.port)
    out = {"greeting": conn.greeting}
    out["mode_stream"] = conn.cmd("MODE STREAM")[0]
    lines = article(args.msgid, args.group, "inn lab transfer", args.from_identity)
    out["offer"] = conn.cmd("IHAVE " + args.msgid)[0]
    if out["offer"].startswith("335"):
        send_block(conn, lines)
        out["transfer"] = conn.line()
    else:
        out["transfer"] = "(nothing sent: the offer drew " + out["offer"] + ")"

    # The same Message-ID again: INN's history must refuse it before the bytes.
    out["duplicate"] = conn.cmd("IHAVE " + args.msgid)[0]
    if out["duplicate"].startswith("335"):
        send_block(conn, lines)
        out["duplicate_transfer"] = conn.line()

    # An article whose Path already names INN: RFC 5537 section 3.6, and INN's
    # own ME exclusion list.  The Path is inside the article, so a correct
    # server says 335 first and rejects after the bytes.
    loop = article(args.loop_msgid, args.group, "inn lab loop", args.loop_identity)
    out["loop_offer"] = conn.cmd("IHAVE " + args.loop_msgid)[0]
    if out["loop_offer"].startswith("335"):
        send_block(conn, loop)
        out["loop_result"] = conn.line()
    else:
        out["loop_result"] = out["loop_offer"]

    # CHECK for a Message-ID nobody has: the streaming offer verb.
    out["check_unknown"] = conn.cmd("CHECK " + args.absent)[0]
    out["check_duplicate"] = conn.cmd("CHECK " + args.msgid)[0]
    conn.close()
    out["ok"] = (out["transfer"].startswith("235")
                 and out["duplicate"].startswith("435")
                 and out["loop_result"].startswith("437")
                 and out["check_unknown"].startswith("238")
                 and out["check_duplicate"].startswith("438"))
    return out


def offer(args):
    """What innfeed sends to fn, sent by hand: the exact replies, verbatim."""
    conn = Conn(args.port)
    out = {"greeting": conn.greeting}
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    out["capabilities"] = caps
    out["ihave_advertised"] = any(c.split()[:1] == ["IHAVE"] for c in caps if c.strip())
    out["streaming_advertised"] = any(
        c.split()[:1] == ["STREAMING"] for c in caps if c.strip())
    out["mode_stream"] = conn.cmd("MODE STREAM")[0]
    out["check"] = conn.cmd("CHECK " + args.msgid)[0]
    out["ihave"] = conn.cmd("IHAVE " + args.msgid)[0]
    out["transit"] = out["ihave"][:3] not in ("500", "501", "502")
    if out["ihave"].startswith("335"):
        send_block(conn, article(args.msgid, args.group, "inn lab offer",
                                 args.from_identity))
        out["transfer"] = conn.line()
    conn.close()
    # The absence of a transit surface is this phase's finding, not its failure.
    out["ok"] = True
    return out


def cut(args):
    """SIGKILL a server from inside a session it has already opened."""
    conn = Conn(args.port)
    out = {"mode": args.mode, "greeting": conn.greeting}
    if args.mode == "post":
        out["open"] = conn.cmd("POST")[0]
        opened = out["open"].startswith("340")
        if opened:
            conn.sock.sendall(
                ("Path: {}!not-for-mail\r\nFrom: lab@example.invalid\r\n"
                 "Subject: interrupted\r\nNewsgroups: {}\r\nMessage-ID: {}\r\n"
                 "\r\nhalf an ".format(
                     args.from_identity, args.group, args.msgid)).encode())
    elif args.mode == "ihave":
        out["open"] = conn.cmd("IHAVE " + args.msgid)[0]
        opened = out["open"].startswith("335")
        if opened:
            conn.sock.sendall(
                ("Path: {}!not-for-mail\r\nFrom: lab@example.invalid\r\n"
                 "Subject: interrupted\r\nNewsgroups: {}\r\nMessage-ID: {}\r\n"
                 "\r\nhalf an ".format(
                     args.from_identity, args.group, args.msgid)).encode())
    else:
        out["open"] = conn.cmd("GROUP " + args.group)[0]
        opened = out["open"].startswith("211")
    out["opened"] = opened
    time.sleep(0.5)
    os.kill(args.pid, 9)
    out["killed_pid"] = args.pid
    try:
        conn.sock.sendall(b"article.\r\n.\r\n")
        out["after_kill"] = "reply: " + conn.line()
    except Exception as error:         # reset, EOF or timeout: all are the cut
        out["after_kill"] = "{}: {}".format(type(error).__name__, error)
    try:
        conn.sock.close()
    except Exception:
        pass
    out["ok"] = opened and not out["after_kill"].startswith(
        ("reply: 235", "reply: 240"))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="phase", required=True)
    for name in ("read", "ihave", "offer", "cut"):
        one = sub.add_parser(name)
        one.add_argument("--port", type=int, default=0)
        one.add_argument("--group", default="fn.letters")
        one.add_argument("--msgid", default="")
        one.add_argument("--absent", default="<absent@example.invalid>")
        one.add_argument("--loop-msgid", default="<loop@example.invalid>")
        one.add_argument("--loop-identity", default="peer.example.invalid")
        one.add_argument("--from-identity", default="lab.example.invalid")
        one.add_argument("--mode", default="read")
        one.add_argument("--pid", type=int, default=0)
    args = parser.parse_args()
    handler = {"read": read, "ihave": ihave, "offer": offer, "cut": cut}[args.phase]
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


# --------------------------------------------------------------------------
# the lab


class InnLab(deploy_gate.DeployGate):
    """The deploy gate's machinery, with a real INN on the other end."""

    TITLE = "INN interop lab"
    TOOL = "tools/inn_lab.py"
    PREAMBLE = (
        "A real InterNetNews server, built from the release tarball pinned below and",
        "left installed on the box, peered with one fn node from the commit named",
        "below. This records what ran. INN's replies are INN's; fn's are fn's; every",
        "scenario the tree cannot support today is a skip carrying the exact reply",
        "that made it one, never a weaker scenario under the same name.")
    FACT_KEYS = ("os", "kernel", "python3", "acl2version", "certificates",
                 "three outcomes", "inn version", "inn tarball sha256",
                 "inn prefix", "ports",
                 "inn server", "fn node", "read", "ihave", "innfeed", "offer",
                 "fn cut", "innd cut")
    # What this lab can decide.  An INN reply is INN's own behaviour and a
    # standing control; what the lab asserts is that the two programs
    # interoperated on these exchanges, and each such assertion is here.
    ASSERTIONS = dict(deploy_gate.DeployGate.ASSERTIONS)
    ASSERTIONS.update({
        "peer-record-accepted": (
            "the fn node holds a peer record naming INN, so INN's address "
            "resolves to a peer at accept (specs/peering.md 1.1)", ("",)),
        "fn-port-as-configured": (
            "the fn node came up on the port innfeed.conf names", ("",)),
        "innd-up": ("innd came up", ("",)),
        "nnrpd-up": ("nnrpd came up on its port", ("",)),
        "ports-free": ("the ports the lab needs were free before it started",
                       ("",)),
        "inn-duplicate-435": (
            "a second IHAVE of an article INN holds draws 435", ("",)),
        "inn-loop-437": (
            "an article whose Path names INN draws 437 from INN", ("",)),
        "innfeed-logged": (
            "INN's own innfeed recorded what it offered the fn node", ("",)),
        "fn-transit-surface": (
            "the fn node serves the transit commands INN's innfeed speaks",
            ("",)),
        "innd-survived-fn-kill": (
            "innd was still running after the fn node was SIGKILLed", ("",)),
        "innd-died": ("innd died on SIGKILL, so the control really cut", ("",)),
        "innd-restarted": ("innd came back after the SIGKILL", ("",)),
    })
    STANDING_GAPS = (
        "INN and fn are on ONE host, over loopback. Nothing here exercises a real\n"
        "  network, a partition, latency, or two machines' clocks disagreeing.",
        "No TLS, no AUTHINFO, no Distribution header, no control messages, no\n"
        "  cancel and no expiry: incoming.conf authorises by source address only,\n"
        "  which on loopback authorises everything that can connect.",
        "The lab reads INN with its own raw-socket client. fn has no NNTP *client*\n"
        "  on this tree, so `fn reads from INN` means `the lab read INN on fn's\n"
        "  behalf`; the day fn has a feed client that sentence gets its subject.",
        "A SIGKILL of a server process is not a power loss, and killing one server\n"
        "  is not a partition: the other stays reachable throughout.",
        "No RFC 3977/4644/5537 conformance audit. The assertions are this driver's,\n"
        "  and a green run says the two programs interoperated on these exchanges.",
        "The certificates were not re-established here; see the certificate row.")

    def __init__(self, *args, inn_prefix, inn_version, inn_port, nnrpd_port,
                 fn_port, gate_root, server_template=None, extra_overlays=(),
                 **kwargs):
        super().__init__(*args, **kwargs)
        self.inn_prefix = inn_prefix
        self.inn_version = inn_version
        self.inn_port = inn_port
        self.nnrpd_port = nnrpd_port
        self.fn_port = fn_port
        self.gate_root = gate_root
        self.server_template = server_template
        self.extra_overlays = list(extra_overlays)
        self.node_dir = "{}/node".format(self.deploy)
        self.store = "{}/store".format(self.node_dir)
        self.fn_pid = ""
        self.fn_kind = "none"
        self.inn_running = False
        self.started_pids = {}          # only what this run started is ever killed
        self.fn_transit = ""
        self.farm_cost = ""
        self.farm_allowed = False
        self.tag = "{}-{}".format(self.rev, dt.datetime.now(
            dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
        self.ids = message_ids(self.tag)

    # -- plumbing ---------------------------------------------------------
    def bin(self, name: str) -> str:
        return "{}/bin/{}".format(self.inn_prefix, name)

    def ship(self):
        super().ship()
        for overlay in self.extra_overlays:
            self.push_tree(overlay)
        self.push_file(INN_DRIVER, "{}/inn.py".format(self.run), mode="755")

    def drive_inn(self, phase: str, extra: str, name=None, timeout=300,
                  expect=0) -> Step:
        return self.sh(name or "inn {}".format(phase), self.cd(
            "python3 {}/inn.py {} {}".format(self.run, phase, extra)),
            timeout=timeout, expect=expect)

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

    def derive(self, name, source: Step, note="", ok=False) -> Step:
        """A second step over a probe's result: the probe answered, and this is
        the assertion that answer has to satisfy.

        Its code is the assertion's, never the driver's exit code: one driver
        phase carries several assertions, and a phase that ends non-zero
        because one of them failed must not fail the others as well."""
        step = Step(name, source.command, 0 if ok else 1, source.output, 0.0,
                    note, 0)
        self.steps.append(step)
        return step

    # -- certificates -----------------------------------------------------
    def certificates(self):
        """Use the same coherent, load-checked set as every deployment gate."""
        return super().certificates()

    def farm_closure(self) -> Step:
        """No gate on the box: ask the farm for the closure, and price it."""
        if not self.farm_allowed:
            self.skip("certify for the lab",
                      "python3 tools/farm.py submit {} --closure".format(self.host.label),
                      "no gate under {} holds tree {}, and --farm was not given, so no "
                      "certificate was installed. Every fn step below ran against an "
                      "uncertified tree: the fn node's replies are its host code's, and "
                      "nothing here says ACL2 admitted the books behind them."
                      .format(self.gate_root, self.tree))
            self.facts["certificates"] = "none installed (--farm not given)"
            return self.steps[-1]
        # The invoking tree's farm.py, not this file's: `farm.py` mirrors the
        # worktree it lives in, so the main checkout's copy would certify the
        # main checkout while the lane waits for its own books.
        command = ["python3", str(self.repo / "tools/farm.py"), "submit",
                   self.host.label,
                   "--jobs", str(self.jobs), "--closure",
                   "--remote-root", "/tank/fn/lanes/inn-lab",
                   "--affected-by", "books/node.lisp"]
        clock = time.monotonic()
        done = subprocess.run(command, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - clock
        step = Step("farm closure certify", " ".join(command), done.returncode,
                    done.stdout.decode("utf-8", "replace"), elapsed,
                    "tools/farm.py submit with --closure; no gate on the box held "
                    "this tree")
        self.steps.append(step)
        self.farm_cost = "{:.0f} s wall, {} jobs".format(elapsed, self.jobs)
        self.facts["certificates"] = "farm closure certify, rc={} ({})".format(
            step.rc, self.farm_cost)
        return step

    # -- the fn node ------------------------------------------------------
    def init_node(self):
        groups = " ".join("--group {}".format(g) for g in GROUPS)
        self.sh("fn node directories", "mkdir -p {}".format(self.node_dir))
        step = self.sh("fn store init", self.cd(self.fn(
            "--store {} init {}".format(self.store, groups))), timeout=900)
        if step.rc != 0:
            raise GateError("fn store init failed: {}".format(step.output[:400]))
        self.sh("fn store config", self.cd(self.fn(
            "--store {} config".format(self.store))), timeout=900)

    def three_outcomes_node(self):
        """Accepted 0, refused 1, uncertain 3, on the fn store (D13)."""
        payload = "{}/seed.article".format(self.node_dir)
        self.push_file(
            ("Path: {}!not-for-mail\r\nFrom: lab@example.invalid\r\n"
             "Subject: seeded on the fn node\r\nNewsgroups: {}\r\n"
             "Message-ID: {}\r\n\r\nWritten on the fn node by the INN lab.\r\n"
             .format(FN_PATH_IDENTITY, GROUPS[0], self.ids["FN_SEED_ID"])).encode(), payload)
        uncertain = self.ids["UNCERTAIN_ID"]
        accepted = self.sh("fn outcome accepted", self.cd(self.fn(
            "--store {} post --message-id '{}' --payload {} --group {}".format(
                self.store, self.ids["FN_SEED_ID"], payload, GROUPS[0]))),
            timeout=900, expect=EXIT_OK)
        refused = self.sh("fn outcome refused", self.cd(self.fn(
            "--store {} inspect --message-id '{}'".format(self.store, self.ids["ABSENT_ID"]))),
            timeout=900, expect=EXIT_REFUSED)
        unsure = self.sh("fn outcome uncertain", self.cd(self.fn(
            "--store {} post --message-id '{}' --payload {} --group {} "
            "--inject-fault postpublish".format(
                self.store, uncertain, payload, GROUPS[0])),),
            timeout=900, expect=EXIT_UNCERTAIN)
        observed = (accepted.rc, refused.rc, unsure.rc)
        expected = (EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN)
        self.facts["three outcomes"] = (
            "accepted={} refused={} uncertain={} (expected {})".format(
                *observed, expected))
        self.check("outcomes-distinct", observed == expected,
                   "the three outcomes did not stay distinct in the fn exit codes: "
                   "observed {}, expected {} (D13)".format(observed, expected),
                   observed="accepted={} refused={} uncertain={}".format(*observed))
        self.sh("fn recover after the uncertain publication", self.cd(self.fn(
            "--store {} recover".format(self.store))), timeout=900)
        self.limitation(
            "uncertain-indeterminate",
            "the injected uncertain publication {} is asserted in neither direction: a "
            "postpublish fault is indeterminate by construction (D13), and a lab that "
            "asserted it either way would be asserting a coin toss.".format(uncertain))
        self.fn_peer_record()

    def fn_peer_record(self):
        """The peer record that makes INN a peer of this fn node.

        Without it the fn node answers INN's IHAVE with 502 (RFC 3977 3.2.1:
        recognized, not permitted), because a connection is a peer connection
        only when its source resolves to a configured record at accept
        (specs/peering.md 1.1).  The record must be written while no owner
        holds the store, which is why it is here and not after start_fn.
        """
        probe = self.sh("peer record CLI", self.cd(
            "python3 tools/run_store.py --store /nonexistent peer --help "
            ">/dev/null 2>&1 && echo STORE-PEER || echo NONE"), expect=None)
        if "STORE-PEER" not in probe.output:
            # waiver-ok: capability -- the probe asks this tree whether
            # `run_store.py peer` exists and prints STORE-PEER or NONE, so it
            # reads a command's OUTPUT to learn that a subcommand is absent,
            # not to learn that something failed.  The peer CLI landed on
            # 2026-09-21 (w11/twonode-feed), so on a current tree this branch
            # is not taken; it stays for a run against an older commit, and
            # the reason below is the predicate.
            self.facts["peer record"] = "no CLI on this commit"
            blocker = ("peer record: not available on this tree, so the fn node "
                       "resolves no connection to a peer and every transit command "
                       "below is answered as it would be for a reader.")
            self.skip("fn peer record for INN",
                      "run_store.py peer add (specs/peering.md 1.2, (:set-peer record))",
                      blocker)
            self.not_built("peer-record-accepted",
                           "the fn node has no peer record for INN: " + blocker,
                           "no `peer add` on this commit")
            return
        added = self.sh("fn peer record for INN", self.cd(self.fn(
            "--store {} peer add innA --path-identity {} --nntp 127.0.0.1:{} "
            "--inbound-groups '{}' --outbound-groups '{}' --streaming "
            "--source-address 127.0.0.1".format(
                self.store, INN_PATH_IDENTITY, self.inn_port,
                GROUPS[0].split(".")[0] + ".*", GROUPS[0].split(".")[0] + ".*")),),
            timeout=900, expect=None)
        listing = self.sh("fn peer list", self.cd(self.fn(
            "--store {} peer list".format(self.store))), timeout=900, expect=None)
        self.facts["peer record"] = (listing.first_line or "(no peer line)")
        self.check(
            "peer-record-accepted", added.rc == 0 and "innA" in listing.output,
            "the fn node has no peer record for INN (`peer add` exit {}), so its "
            "listener resolves INN's address to no peer and answers the transit "
            "commands as a reader: every transit result below is about an "
            "unconfigured connection, not about peering.".format(added.rc),
            observed=listing.first_line or "no peer line")

    def start_fn(self, tag="main") -> bool:
        if self.server_template:
            kind, command = "custom", self.server_template.format(
                store=self.store, run=self.node_dir, port=self.fn_port)
        else:
            kind, command = self.server_command(self.store, self.node_dir)
            command = command.replace("--port 0", "--port {}".format(self.fn_port))
        started = self.start_server("fn node ({})".format(kind), command, tag,
                                    run=self.node_dir)
        if not started and kind != "reader" and not self.server_template:
            fallback = ("python3 tools/run_reader.py --store {} --port {} --post"
                        .format(self.store, self.fn_port))
            self.check(
                "entry-point-listening", False,
                "the {} entry point did not reach LISTENING on this commit, so the lab "
                "fell back to tools/run_reader.py --post. Every fn-side reply below is "
                "the reader's, not the {}'s.".format(kind, kind),
                observed="selected={}".format(kind))
            kind, command = "reader", fallback
            started = self.start_server("fn node (reader)", command, tag,
                                        run=self.node_dir)
        if not started:
            return False
        self.fn_kind = kind
        self.fn_pid = self.sh("fn node pid", "cat {}/server.pid".format(
            self.node_dir)).output.strip()
        self.started_pids["fn"] = self.fn_pid
        self.facts["fn node"] = "{} on port {} ({}), store {}".format(
            kind, self.port, tag, self.store)
        self.check(
            "fn-port-as-configured", self.port == self.fn_port,
            "the fn node came up on port {}, not the {} innfeed.conf names: INN's "
            "outbound half cannot reach it, so the innfeed scenario below is about "
            "a connection that was never made.".format(self.port, self.fn_port),
            observed="listening={} configured={}".format(self.port, self.fn_port))
        return True

    # -- INN --------------------------------------------------------------
    def inn_preflight(self):
        step = self.sh("INN install", """
P={prefix}
if [ ! -x $P/bin/innd ]; then echo "NO-INN $P"; exit 1; fi
echo "innd=$($P/bin/innconfval version 2>&1 | head -1)"
echo "tarball=$(cat $(dirname $P)/src/inn-{version}.tar.gz.sha256 2>/dev/null | head -1)"
echo "owner=$(stat -c '%U' $P 2>/dev/null || stat -f '%Su' $P)"
# A connect probe, not `ss -ltn`: it is portable (the dry run is a laptop),
# and "something answers there" is the question, not "the kernel lists it".
for p in {inn_port} {nnrpd_port} {fn_port}; do
  if python3 -c "import socket,sys; s=socket.socket(); s.settimeout(2); sys.exit(0 if s.connect_ex(('127.0.0.1',$p))==0 else 1)"; then
    echo "port $p BUSY"; else echo "port $p free"; fi
done
""".format(prefix=self.inn_prefix, version=self.inn_version,
           inn_port=self.inn_port, nnrpd_port=self.nnrpd_port, fn_port=self.fn_port),
            expect=None)
        if step.rc != 0:
            raise GateError("no INN at {}: build it first, see docs/interop-inn.md"
                            .format(self.inn_prefix))
        for line in step.output.splitlines():
            if line.startswith("innd="):
                self.facts["inn version"] = line[len("innd="):].strip()
            if line.startswith("tarball="):
                self.facts["inn tarball sha256"] = line[len("tarball="):].strip()
            if " BUSY" in line:
                self.inconclusive(
                    "ports-free",
                    "{}: something was already listening there before the lab started. "
                    "The lab did not touch it and did not start its own server on that "
                    "port; every scenario that needed it is unfounded.".format(line),
                    "a port the lab needs was already in use", observed=line)
        if "ports-free" not in {one.key for one in self.found}:
            self.check("ports-free", True, "", observed="all three ports free")
        self.facts["inn prefix"] = self.inn_prefix
        self.facts["ports"] = ("innd {} (transit), nnrpd {} (reader), fn {} "
                               "(innfeed.conf names this)".format(
                                   self.inn_port, self.nnrpd_port, self.fn_port))

    def inn_configure(self):
        """Write the five configuration files and cold-start history if absent."""
        fields = dict(prefix=self.inn_prefix, inn_port=self.inn_port,
                      fn_port=self.fn_port, inn_identity=INN_PATH_IDENTITY,
                      fn_identity=FN_PATH_IDENTITY, user="$(id -un)",
                      group="$(id -gn)")
        user = self.sh("INN news user", "echo user=$(id -un) group=$(id -gn)")
        who = dict(part.split("=", 1) for part in user.output.split()
                   if "=" in part) if user.output.strip() else {}
        fields["user"] = who.get("user", "news")
        fields["group"] = who.get("group", "news")
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
                           "{}/etc/{}".format(self.inn_prefix, name))
        # innfeed appends for ever; a tail of it must be THIS run's, so the log
        # is truncated before innd is started and never after.
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

    def inn_start(self) -> bool:
        step = self.sh("start innd", """
P={p}
rm -f $P/log/innd-stdout.log
nohup $P/bin/innd -d > $P/log/innd-stdout.log 2>&1 < /dev/null &
for i in $(seq 1 60); do
  if $P/bin/ctlinnd -t 2 mode 2>/dev/null | grep -q 'Server running'; then
    echo "INND-UP pid=$(cat $P/run/innd.pid 2>/dev/null)"; exit 0
  fi
  sleep 1
done
echo INND-TIMEOUT; tail -20 $P/log/innd-stdout.log; exit 1
""".format(p=self.inn_prefix), timeout=180, expect=None)
        up = step.rc == 0 and "INND-UP" in step.output
        self.check("innd-up", up,
                   "innd did not come up: {}".format(step.first_line),
                   observed=step.first_line or "no output")
        if not up:
            self.facts["inn server"] = "innd did not start"
            return False
        pid = reported_pid(step.output)
        if pid:
            self.started_pids["innd"] = pid
        else:
            self.gaps.append(
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
                "pgrep -a innfeed || echo NO-INNFEED".format(self.bin("ctlinnd")),
                expect=None)
        nnrpd = self.sh("start nnrpd", """
P={p}
# `nnrpd -D` daemonises, so $! is the shell child that exits: the pid to
# remember is the one nnrpd writes itself, run/nnrpd-<port>.pid.  Killing $!
# left a stray reader daemon on the box on 2026-09-20.
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
            self.check("nnrpd-up", False,
                       "nnrpd did not come up on port {}: {}".format(
                           self.nnrpd_port, nnrpd.first_line),
                       observed=nnrpd.first_line or "no output")
        self.facts["inn server"] = "innd pid {} on port {}, nnrpd on port {}".format(
            pid, self.inn_port, self.nnrpd_port)
        return True

    def inn_stop(self):
        """Only what this run started, and only by the pid it recorded."""
        if "nnrpd" in self.started_pids:
            self.sh("stop nnrpd", "kill {} 2>/dev/null || true; echo stopped".format(
                self.started_pids["nnrpd"]))
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
pgrep -F {p}/run/innfeed.pid >/dev/null 2>&1 && echo INNFEED-ALIVE || echo INNFEED-GONE
""".format(pid=self.started_pids.get("innd")
           or "$(cat {}/run/innd.pid 2>/dev/null || echo -1)".format(self.inn_prefix),
           p=self.inn_prefix), expect=None)
            self.inn_running = False

    # -- the scenarios ----------------------------------------------------
    def scenario_ihave_into_inn(self):
        """INN's inbound path: a transfer, a duplicate and a Path loop."""
        probe = self.drive_inn(
            "ihave",
            "--port {} --group {} --msgid '{}' --loop-msgid '{}' --loop-identity {} "
            "--from-identity {} --absent '{}'".format(
                self.inn_port, GROUPS[0], self.ids["FED_ID"], self.ids["LOOP_ID"], INN_PATH_IDENTITY,
                FN_PATH_IDENTITY, self.ids["ABSENT_ID"]),
            name="IHAVE {} into INN".format(self.ids["FED_ID"]), expect=None)
        result = self.payload(probe)
        self.facts["ihave"] = (
            "MODE STREAM={mode} IHAVE={offer} transfer={transfer} duplicate={dup} "
            "loop={loop} CHECK(new)={cn} CHECK(dup)={cd}".format(
                mode=result.get("mode_stream"), offer=result.get("offer"),
                transfer=result.get("transfer"), dup=result.get("duplicate"),
                loop=result.get("loop_result"), cn=result.get("check_unknown"),
                cd=result.get("check_duplicate")))
        self.derive("INN accepted the transfer with 235", probe,
                    "IHAVE {}, 335, the article, 235: INN's inbound transit path, "
                    "the one fn's feed lane will drive".format(self.ids["FED_ID"]),
                    ok=str(result.get("transfer", "")).startswith("235"))
        self.check("inn-duplicate-435",
                   str(result.get("duplicate", "")).startswith("435"),
                   "the second IHAVE of {} drew '{}', not 435: INN's history did not "
                   "refuse an article it already holds.".format(
                       self.ids["FED_ID"], result.get("duplicate")),
                   observed=str(result.get("duplicate")))
        self.check("inn-loop-437",
                   str(result.get("loop_result", "")).startswith("437"),
                   "an article whose Path names {} drew '{}', not 437: INN's ME "
                   "exclusion list is not refusing the loop, so the loop scenario is "
                   "unfounded.".format(INN_PATH_IDENTITY, result.get("loop_result")),
                   observed=str(result.get("loop_result")))
        self.sh("INN history for {}".format(self.ids["FED_ID"]),
                "{} '{}' 2>&1 | head -3".format(self.bin("grephistory"), self.ids["FED_ID"]),
                expect=None)
        self.sh("news.notice tail", "tail -20 {}/log/news.notice 2>/dev/null || "
                "tail -20 {}/log/innd-stdout.log".format(
                    self.inn_prefix, self.inn_prefix), expect=None)

    def scenario_read_from_inn(self):
        """nnrpd serves back what the transit path stored."""
        if "nnrpd" not in self.started_pids:
            self.skip("read {} back from INN's nnrpd".format(self.ids["FED_ID"]),
                      "inn.py read", "nnrpd did not start, so nothing read it back")
            return
        probe = self.drive_inn(
            "read", "--port {} --group {} --msgid '{}' --absent '{}'".format(
                self.nnrpd_port, GROUPS[0], self.ids["FED_ID"], self.ids["ABSENT_ID"]),
            name="read {} back from INN's nnrpd".format(self.ids["FED_ID"]), expect=None)
        result = self.payload(probe)
        self.facts["read"] = "GROUP={} ARTICLE={} Path={} absent={}".format(
            result.get("group"), result.get("article"), result.get("path"),
            result.get("absent"))
        self.derive("nnrpd served the article the transit path stored", probe,
                    "the Message-ID INN serves is the one that was offered, and an "
                    "unknown Message-ID draws 43x from the same daemon",
                    ok=bool(result.get("ok")))
        self.limitation(
            "reader-is-the-labs-client",
            "the reader here is the lab's raw-socket client, not fn: nothing on this "
            "tree is an NNTP *client*, so this shows INN serving, and shows nothing "
            "about fn's ability to read a peer.")

    def scenario_offer_to_fn(self):
        """INN's innfeed offers to fn, and the same offer by hand."""
        probe = self.drive_inn(
            "offer", "--port {} --group {} --msgid '{}' --from-identity {}".format(
                self.port or self.fn_port, GROUPS[0], self.ids["OFFER_ID"], INN_PATH_IDENTITY),
            name="offer {} to the fn node by hand".format(self.ids["OFFER_ID"]), expect=None)
        result = self.payload(probe)
        self.fn_transit = str(result.get("ihave", ""))
        self.facts["offer"] = (
            "CAPABILITIES lists IHAVE={ih} STREAMING={st}; MODE STREAM='{ms}'; "
            "CHECK='{ck}'; IHAVE='{iv}'".format(
                ih=result.get("ihave_advertised"), st=result.get("streaming_advertised"),
                ms=result.get("mode_stream"), ck=result.get("check"),
                iv=result.get("ihave")))
        # Now INN's own innfeed, driven by innd: offer the article INN holds.
        flush = self.sh("ctlinnd flush fn (innfeed offers to the fn node)",
                        "{} -t 10 flush fn 2>&1 || true; sleep 25; "
                        "echo '--- innfeed.log (this run):'; "
                        "tail -25 {}/log/innfeed.log 2>/dev/null || true; "
                        "echo '--- innfeed.status:'; "
                        "(grep -A6 'Peer fn' {}/log/innfeed.status 2>/dev/null "
                        "|| echo '(no innfeed.status)') | head -20".format(
                            self.bin("ctlinnd"), self.inn_prefix, self.inn_prefix),
                        timeout=180, expect=None)
        self.facts["innfeed"] = flush.first_line or "(no innfeed log line)"
        if "innfeed:" in flush.output:
            self.check("innfeed-logged", True, "", observed=flush.first_line)
        else:
            self.inconclusive(
                "innfeed-logged",
                "INN's innfeed wrote nothing to its log during this run, so what "
                "crossed INN's outbound half is not recorded here: the hand-driven "
                "offer below is the only fn-side evidence, and it is the lab's "
                "client wearing innfeed's clothes, not innfeed.",
                "innfeed.log carried no line for this run",
                observed=flush.first_line or "no innfeed line")
        if not result.get("transit"):
            self.not_built(
                "fn-transit-surface",
                "the fn node answered `IHAVE` with '{}' and `CHECK` with '{}' and "
                "lists no IHAVE in CAPABILITIES, so INN's innfeed has no transit "
                "surface to offer to on this commit.".format(
                    result.get("ihave"), result.get("check")),
                "the fn node serves no IHAVE/CHECK/TAKETHIS on this commit",
                owner="the peering lane")
            self.skip("INN's innfeed transfers an article to fn",
                      "inn.py offer (IHAVE/CHECK/TAKETHIS on the fn listener)",
                      "peering: not available on this tree. The fn node answered "
                      "`IHAVE {}` with '{}' and `CHECK` with '{}', and its CAPABILITIES "
                      "block does not list IHAVE, so the transit commands of "
                      "specs/peering.md 1.1 are not served by this commit. INN's "
                      "innfeed reads an unknown response code as `cxnsleep response "
                      "unknown` (innfeed/connection.c:1953) and sleeps the connection "
                      "with the article still queued, so nothing was lost and nothing "
                      "crossed.".format(self.ids["OFFER_ID"], result.get("ihave"),
                                        result.get("check")))
            self.skip("the article INN fed is served by the fn node",
                      "inn.py read against the fn node",
                      "peering: not available on this tree; there was no transfer to "
                      "read back")
            return
        self.check("fn-transit-surface", True, "",
                   observed="IHAVE -> {}".format(result.get("ihave")))
        self.derive("the fn node took INN's offer", probe,
                    "IHAVE {}, 335, the article, 235 on the fn listener".format(self.ids["OFFER_ID"]),
                    ok=str(result.get("transfer", "")).startswith("235"))

    def scenario_fn_restart(self):
        """SIGKILL the fn node inside a session, recover it, reread."""
        mode = ("ihave" if self.fn_transit.startswith("335")
                else "post" if self.post_enabled else "read")
        if mode == "read":
            self.limitation(
                "fn-kill-not-in-transfer",
                "the fn node offers neither a transit surface nor POST on this commit, "
                "so the kill landed on an open reader connection rather than inside a "
                "transfer.")
        step = self.drive_inn(
            "cut", "--port {} --mode {} --group {} --msgid '{}' --from-identity {} "
            "--pid {}".format(self.port, mode, GROUPS[0], self.ids["FN_CUT_ID"],
                              INN_PATH_IDENTITY, self.fn_pid or 0),
            name="kill -9 the fn node mid-{}".format(mode), timeout=180, expect=None)
        self.facts["fn cut"] = "mode={} {}".format(
            mode, self.payload(step).get("after_kill", ""))
        self.sh("the fn node is gone", "kill -0 {} 2>/dev/null && echo ALIVE || "
                "echo GONE".format(self.fn_pid or 0))
        survivor = self.sh("innd survived the fn node's death",
                           "{} -t 5 mode 2>&1 | head -2".format(self.bin("ctlinnd")),
                           expect=None)
        self.check("innd-survived-fn-kill", "Server running" in survivor.output,
                   "innd was not running after the fn node was killed: {}"
                   .format(survivor.first_line),
                   observed=survivor.first_line or "no output")
        self.sh("fn recover after the kill", self.cd(self.fn(
            "--store {} recover".format(self.store))), timeout=1800)
        self.sh("fn status after recovery", self.cd(self.fn(
            "--store {} status".format(self.store))), timeout=1800)
        self.sh("the fn node still holds {}".format(self.ids["FN_SEED_ID"]), self.cd(self.fn(
            "--store {} inspect --message-id '{}'".format(self.store, self.ids["FN_SEED_ID"]))),
            timeout=900, expect=EXIT_OK)
        self.sh("the fn node does not hold the interrupted {}".format(self.ids["FN_CUT_ID"]),
                self.cd(self.fn("--store {} inspect --message-id '{}'".format(
                    self.store, self.ids["FN_CUT_ID"]))), timeout=900, expect=EXIT_REFUSED)
        if not self.start_fn(tag="after-recovery"):
            self.skip("reread the fn node after recovery", "inn.py read",
                      "the fn node did not restart after the recovery")

    def scenario_innd_restart(self):
        """The control: SIGKILL innd, restart it, and reread what it took."""
        pid = self.started_pids.get("innd")
        if not pid:
            self.skip("kill -9 innd and restart", "kill -9; innd -d",
                      "the lab never started innd, so it will not kill one")
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
        again = self.sh("restart innd after the kill", """
P={p}
nohup $P/bin/innd -d >> $P/log/innd-stdout.log 2>&1 < /dev/null &
for i in $(seq 1 60); do
  if $P/bin/ctlinnd -t 2 mode 2>/dev/null | grep -q 'Server running'; then
    echo "INND-UP pid=$(cat $P/run/innd.pid 2>/dev/null)"; exit 0; fi
  sleep 1
done
echo INND-TIMEOUT; tail -20 $P/log/innd-stdout.log; exit 1
""".format(p=self.inn_prefix), timeout=180, expect=None)
        if again.rc == 0 and "INND-UP" in again.output:
            back = reported_pid(again.output)
            if back:
                self.started_pids["innd"] = back
            else:
                self.gaps.append(
                    "innd restarted but wrote no pid to {}/run/innd.pid, so "
                    "this run will not kill it".format(self.inn_prefix))
            self.inn_running = True
            self.check("innd-restarted", True, "", observed=again.first_line)
        else:
            self.check("innd-restarted", False,
                       "innd did not come back after the SIGKILL: {}".format(
                           again.first_line),
                       observed=again.first_line or "no output")
            self.facts["innd cut"] = "innd did not restart"
            return
        survives = self.drive_inn(
            "ihave", "--port {} --group {} --msgid '{}' --loop-msgid '{}' "
            "--loop-identity {} --from-identity {} --absent '{}'".format(
                self.inn_port, GROUPS[0], self.ids["FED_ID"], self.ids["LOOP2_ID"],
                INN_PATH_IDENTITY, FN_PATH_IDENTITY, self.ids["ABSENT_ID"]),
            name="after innd's restart, {} is still a duplicate".format(self.ids["FED_ID"]),
            expect=None)
        result = self.payload(survives)
        self.facts["innd cut"] = "after restart: IHAVE {} -> {}".format(
            self.ids["FED_ID"], result.get("offer"))
        self.derive("INN's history survived the SIGKILL", survives,
                    "the article INN acknowledged before the kill is still refused as "
                    "a duplicate after it: the control that says this lab's assertions "
                    "can tell a surviving article from a lost one",
                    ok=str(result.get("offer", "")).startswith("435"))

    # -- evidence ---------------------------------------------------------
    def evidence(self, path, started, elapsed):
        seen, unique = set(), []
        for one in self.found:
            mark = (one.id, one.verdict, one.detail)
            if mark in seen:
                continue
            seen.add(mark)
            unique.append(one)
        self.found = unique
        return super().evidence(path, started, elapsed)

    # -- the whole lab ----------------------------------------------------
    def execute(self):
        self.preflight()
        self.inn_preflight()
        self.ship()
        self.certificates()
        self.init_node()
        self.three_outcomes_node()
        self.inn_configure()
        if not self.inn_start():
            raise GateError("innd did not start; see the evidence for its log")
        if not self.start_fn():
            raise GateError("the fn node did not reach LISTENING")
        self.scenario_ihave_into_inn()
        self.scenario_read_from_inn()
        self.scenario_offer_to_fn()
        self.scenario_fn_restart()
        self.scenario_innd_restart()
        self.sh("fn node log tail", "tail -12 {}/server-main.log".format(self.node_dir),
                expect=None)

    def cleanup(self):
        """No process of ours left on the box; the INN install stays."""
        self.stop_server("fn node", run=self.node_dir)
        self.inn_stop()
        self.sh("stray lab processes", "pgrep -f 'fn-deploy/{}' >/dev/null 2>&1 "
                "&& echo STRAY || echo CLEAN".format(self.deploy_id), expect=None)
        if not self.keep:
            self.sh("remove the deploy tree", "rm -rf {}".format(self.deploy))
        self.release_deploy_lock()
        self.sh("the INN install is left in place",
                "ls -d {} && echo INN-KEPT".format(self.inn_prefix), expect=None)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("commit", nargs="?", default="dev",
                        help="the commit-ish to deploy as the fn node")
    parser.add_argument("--host", default=DEFAULT_HOST)
    parser.add_argument("--tree", default="dev", help="gate directory prefix on the host")
    parser.add_argument("--repo", default=None,
                        help="the fn worktree to read the commit from and "
                             "write evidence into (default: the one this "
                             "command was invoked from)")
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--evidence", default=None)
    parser.add_argument("--keep", action="store_true",
                        help="leave the deploy tree on the host")
    parser.add_argument("--dry-run", action="store_true",
                        help="run every script through local bash with HOME redirected")
    parser.add_argument("--home", default=None, help="the fake HOME for --dry-run")
    parser.add_argument("--acl2", default=None,
                        help="the host's ACL2 image; the default is tools/farm.py's entry")
    parser.add_argument("--inn-version", default=DEFAULT_INN_VERSION)
    parser.add_argument("--inn-prefix", default=None,
                        help="the INN install; the default is "
                             "{}/<version>".format(DEFAULT_INN_ROOT))
    parser.add_argument("--inn-port", type=int, default=INN_PORT)
    parser.add_argument("--nnrpd-port", type=int, default=NNRPD_PORT)
    parser.add_argument("--fn-port", type=int, default=FN_PORT)
    parser.add_argument("--gate-root", default=None,
                        help="where the host keeps its gates; hbox uses /tank/fn/gates")
    parser.add_argument("--farm", action="store_true",
                        help="when no gate on the box holds this tree, submit a "
                             "--closure certify to the farm instead of skipping")
    parser.add_argument("--overlay", action="append", default=[],
                        help="a directory copied over the deployed tree before it runs")
    parser.add_argument("--server-command", default=None,
                        help="the fn entry point, with {store}, {run} and {port}")
    args = parser.parse_args(argv)

    repo = Path(args.repo).resolve() if args.repo else repo_root()
    commit, rev = resolve(repo, args.commit)
    if args.dry_run:
        if args.home is None:
            parser.error("--dry-run needs --home")
        host: Host = LocalHost(Path(args.home).resolve())
    else:
        host = SshHost(args.host)
    overlays = [Path(one).resolve() for one in args.overlay]
    gate_root = args.gate_root or ("/tank/fn/gates" if args.host == "hbox"
                                   else deploy_gate.GATE_ROOT)
    lab = InnLab(host, repo, commit, rev, args.tree,
                 overlay=overlays[0] if overlays else None,
                 jobs=args.jobs, keep=args.keep, nntplib_python="none",
                 acl2=args.acl2 or farm.host_settings(args.host)["acl2"],
                 inn_prefix=args.inn_prefix or "{}/{}".format(
                     DEFAULT_INN_ROOT, args.inn_version),
                 inn_version=args.inn_version, inn_port=args.inn_port,
                 nnrpd_port=args.nnrpd_port, fn_port=args.fn_port,
                 gate_root=gate_root, server_template=args.server_command,
                 extra_overlays=overlays[1:])
    lab.farm_allowed = args.farm
    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    failure = None
    try:
        lab.execute()
    except GateError as error:
        failure = str(error)
        lab.limitation("lab-stopped-early",
                       "the lab stopped early: {}".format(error))
    finally:
        try:
            lab.cleanup()
        except Exception as error:      # cleanup must never hide the result
            lab.limitation("cleanup-unfinished",
                           "cleanup did not finish: {}: {}".format(
                               type(error).__name__, error))
    elapsed = time.monotonic() - clock
    lab.finalize_findings()
    date = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
    target = evidence_path(args.evidence, repo,
                           "inn-lab-{}-{}.md".format(rev, date))
    lab.evidence(target, started, elapsed)
    print("evidence: {}".format(target))
    report(lab)
    if failure:
        print("lab error: {}".format(failure))
    return lab.exit_code(failure)


if __name__ == "__main__":
    sys.exit(main())

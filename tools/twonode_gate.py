#!/usr/bin/env python3
"""Two fn nodes on one host, and the question of whether they can reach each other.

tools/deploy_gate.py establishes that one commit serves, dies and recovers.
This is the next thing that is not yet true: two fn nodes, A and B, each with
its own store, its own served groups and its own listener, running at the same
time, with a peer record on each naming the other -- and then the three
questions a pair answers that a single node cannot.

1. **independent** -- what A accepts is A's.  X is on A and Y is on B; each
   node serves its own article and answers `430` for the other's.  Both
   servers stay up.  This is the control: without it, a later "B has X" says
   nothing, because B might have had X all along.
2. **feed** -- X is offered from A to B over a raw socket, RFC 3977 6.3.2:
   `IHAVE`, `335`, the article, `235`; then B is reread and must hold the same
   octets (specs/peering.md section 4, K4).  A second `IHAVE` of X must draw
   `435` from the Message-ID history, and an article whose `Path` already
   names B must be refused after its `335` (RFC 5537 section 3.5 loop
   suppression).  When the transit surface is not on this tree the offer draws
   `500`/`501`, the step is recorded as "peering: not available on this tree",
   and the gate still passes -- so the harness is green today and gains teeth
   the day the peering lane lands.
3. **kill** -- B is SIGKILLed in the middle of a transfer it agreed to take
   (mid-`IHAVE` when transit is there, mid-`POST` otherwise), recovered
   through the real recovery path and reread: everything B acknowledged is
   still there, the interrupted transfer is not, and A never noticed.  The
   three outcomes stay distinct in the exit codes throughout (D13): accepted
   0, refused 1, uncertain 3.

    python3 tools/twonode_gate.py dev --host persvati

Everything below the scenarios -- shipping the commit, installing the host's
own certificates pair by pair, starting a server on a free port, the step
accounting, the evidence renderer -- is tools/deploy_gate.py's, reused by
subclassing `DeployGate`, not copied.  This file owns exactly what is new: a
second node, the peer records, and the three scenarios.

Dry run.  ``--dry-run --home DIR`` runs every script through bash on this
machine with ``HOME`` pointed at DIR and no ssh, exactly as the deploy gate's
does; ``--overlay`` puts fake entry points over the deployed tree and
``--server-command`` names a server entry point that is not one of the three
this tree knows (the peering lane's, when it has one).  tests/test_twonode_gate.py
drives both halves: the fake without a transit surface, which must record the
gap and pass, and the fake with one, which must show all four teeth.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import re
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

import deploy_gate                                            # noqa: E402
from deploy_gate import (DEFAULT_HOST, EXIT_OK, EXIT_REFUSED,  # noqa: E402
                         evidence_path, repo_root,
                         EXIT_UNCERTAIN, GROUPS, GateError, Host, LocalHost,
                         SshHost, Step, resolve)

# One article per node, plus the two the transit scenario needs.
ARTICLE_A = "<alpha@a.example.invalid>"
ARTICLE_B = "<beta@b.example.invalid>"
LOOP_ID = "<loop@a.example.invalid>"
INTERRUPTED_ID = "<interrupted@example.invalid>"
ABSENT_ID = "<absent@example.invalid>"


def article(msgid: str, group: str, subject: str, body: str, path: str = "") -> bytes:
    """An article as octets, CRLF, the shape tools/run_store.py post takes.

    The `Date` is not decoration. RFC 5536 section 3.1.1 makes it mandatory
    and `fn-peer-decide-transfer` refuses an article that carries neither it
    nor an Injection-Date with `437 transfer rejected; no Injection-Date or
    Date`. The local store CLI accepts one without, so the omission is
    invisible until an article crosses -- and then it makes every transfer a
    refusal AND every duplicate row read as an acceptance, because nothing
    crossed for them to be duplicates of. Found by tools/v0_matrix.py
    (lane w10/v0-matrix, board 2026-09-20)."""
    headers = ["Path: {}!not-for-mail".format(path)] if path else []
    headers += ["From: gate@example.invalid",
                "Subject: {}".format(subject),
                "Newsgroups: {}".format(group),
                "Date: {}".format(
                    dt.datetime.now(dt.timezone.utc).strftime(
                        "%a, %d %b %Y %H:%M:%S +0000")),
                "Message-ID: {}".format(msgid)]
    return ("\r\n".join(headers) + "\r\n\r\n" + body + "\r\n").encode()


class NodeSpec:
    """One fn node: its directory, its store, its listener and what it holds."""

    def __init__(self, gate: "TwoNodeGate", name: str):
        self.name = name
        self.dir = "{}/{}".format(gate.deploy, name)
        self.store = "{}/store".format(self.dir)
        self.peers = "{}/peers".format(self.dir)
        self.port = 0
        self.pid = ""
        self.kind = "none"
        self.post_enabled = False
        self.transit = None          # None: not probed.  str: the IHAVE reply.
        # RFC 5537 section 3.2 <path-identity>: what this node prepends and what a
        # peer looks for when it suppresses a loop.
        self.path_identity = "{}.gate.example.invalid".format(name)
        self.accepted = []           # every msgid this node has acknowledged
        self.rejected = []           # every msgid this node must NOT hold
        # The recording port a PEER dials instead of this node's own, and the
        # file the tap writes. 0 means no tap: peers dial the node directly
        # and the gate cannot say which offer command carried an article.
        self.tap_port = 0
        self.tap_log = "{}/tap.log".format(self.dir)

    @property
    def upper(self) -> str:
        return self.name.upper()


# --------------------------------------------------------------------------
# the second driver: the transit half, run on the host beside deploy_gate's

FEED_DRIVER = r'''#!/usr/bin/env python3
"""The two-node phases.  No fn module is imported; Conn is deploy_gate's.

`presence` is the control and the reread: what a node holds and what it must
not.  `relay` is RFC 3977 6.3.2 driven by hand over a socket, with the
duplicate and the loop in the same session.  `cut` kills a node in the middle
of a transfer it agreed to take.
"""
import argparse, json, os, socket, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from drive import Conn                 # tools/deploy_gate.py's driver


def rfc5322_now():
    """RFC 5536 section 3.1.1 makes Date mandatory, and transit enforces it."""
    return time.strftime("%a, %d %b %Y %H:%M:%S +0000", time.gmtime())


def article(msgid, group, subject, body, path=""):
    """The same shape tools/twonode_gate.py builds, on the host side.

    This function was CALLED by `post` and never defined, so every
    owner-feed post raised `NameError` and was recorded as an article that
    did not become durable -- in a scenario that had been written and never
    run."""
    headers = ["Path: {}!not-for-mail".format(path)] if path else []
    headers += ["From: gate@example.invalid",
                "Subject: {}".format(subject),
                "Newsgroups: {}".format(group),
                "Date: {}".format(rfc5322_now()),
                "Message-ID: {}".format(msgid)]
    return ("\r\n".join(headers) + "\r\n\r\n" + body + "\r\n").encode()


def send_block(conn, lines):
    """A multi-line block, dot-stuffed, terminated: RFC 3977 section 3.1.1."""
    payload = b""
    for one in lines:
        raw = one.encode()
        payload += (b"." + raw if raw.startswith(b".") else raw) + b"\r\n"
    conn.sock.sendall(payload + b".\r\n")


def fetch(port, msgid):
    conn = Conn(port)
    status, lines = conn.cmd("ARTICLE " + msgid, multiline=True)
    conn.close()
    return status, lines


def split(text):
    return [one for one in text.split(",") if one]


def post(args):
    """POST one article on the live server (RFC 3977 section 6.3.1).

    The owner's feed is driven by what becomes DURABLE, so the gate posts
    through the server rather than through the CLI: the CLI needs the store
    lock the running owner holds, and an article written behind the owner's
    back would never reach fn-own-outcome and so would never be enqueued.
    """
    body = article(args.msgid, args.group, "owner-feed", "Posted through the server.")
    conn = Conn(args.port)
    out = {"greeting": conn.greeting}
    first, _ = conn.cmd("POST")
    out["post"] = first
    if not first.startswith("340"):
        conn.close()
        out["ok"] = False
        return out
    send_block(conn, body.decode("ascii", "replace").split("\r\n"))
    # `Conn.line`, not `read_line`: deploy_gate's driver has no `read_line`,
    # so every owner-feed POST raised AttributeError AFTER putting the
    # article on the wire. The article became durable, the feed offered it
    # and the peer took it -- and the gate recorded "POST answered
    # 'nothing'" and skipped the wait. The crossing happened and the harness
    # said it had not.
    out["result"] = conn.line()
    conn.close()
    out["ok"] = out["result"].startswith("240")
    return out


def wait(args):
    """Poll one node until it serves a Message-ID, or the deadline passes.

    This is the only place the gate waits: the feed is asynchronous by
    construction (the owner offers on its own tick), so "B has it" is a
    question with a deadline, not an instant.
    """
    deadline = time.time() + args.seconds
    out = {"msgid": args.msgid, "seconds": args.seconds}
    attempts = 0
    while time.time() < deadline:
        attempts += 1
        try:
            status, lines = fetch(args.port, args.msgid)
        except Exception as error:      # noqa: BLE001
            # A node mid-restart is not an answer. Before this the driver
            # raised out of the whole phase on the first refused or closed
            # connection, so a node that had not finished starting read as
            # "the article never arrived": gate `0e5a7f8` step 87 aborted
            # at 16.5 s of a 90 s deadline. The last error is reported
            # beside the result.
            out["last_error"] = "{}: {}".format(type(error).__name__, error)
            status, lines = "", []
        if status.startswith("220"):
            out.update(ok=True, status=status, attempts=attempts,
                       lines=len(lines))
            if args.from_port:
                source, source_lines = fetch(args.from_port, args.msgid)
                out["source"] = source
                out["source_lines"] = len(source_lines)
                out["target_lines"] = len(lines)
                out["identical"] = (lines == source_lines)
                if not out["identical"]:
                    # WHICH lines differ, not just that some do. RFC 5537
                    # 3.6 lets a relaying agent alter Path and Xref and
                    # nothing else, so the answer decides whether this is
                    # conformance or corruption.
                    out["only_on_target"] = [
                        one for one in lines if one not in source_lines][:8]
                    out["only_on_source"] = [
                        one for one in source_lines if one not in lines][:8]
            return out
        time.sleep(0.5)
    out.update(ok=False, status=status if "status" in dir() else "", attempts=attempts)
    return out


def presence(args):
    """Every msgid in --present must be served; every one in --absent must not.

    A connection this phase cannot open is reported as `ok: false` with the
    error named, not raised: a node that is down is a finding about the
    node, and the step that says so should still carry its port.
    """
    try:
        conn = Conn(args.port)
    except Exception as error:          # noqa: BLE001
        return {"ok": False, "port": args.port,
                "error": "{}: {}".format(type(error).__name__, error)}
    out = {"groups": {}, "present": {}, "absent": {}}
    for group in split(args.groups):
        out["groups"][group] = conn.cmd("GROUP " + group)[0]
    for msgid in split(args.present):
        out["present"][msgid] = conn.cmd("ARTICLE " + msgid, multiline=True)[0]
    for msgid in split(args.absent):
        out["absent"][msgid] = conn.cmd("ARTICLE " + msgid, multiline=True)[0]
    conn.close()
    out["ok"] = (all(s.startswith("211") for s in out["groups"].values())
                 and all(s.startswith("220") for s in out["present"].values())
                 and all(s.startswith("43") for s in out["absent"].values()))
    return out


def relay(args):
    """Offer one article from the source node to the target node, by hand."""
    out = {"msgid": args.msgid}
    status, lines = fetch(args.from_port, args.msgid)
    out["source"] = status
    if not status.startswith("220"):
        out["ok"] = False
        out["transit"] = None
        out["reason"] = "the source node does not serve " + args.msgid
        return out
    out["source_lines"] = len(lines)

    conn = Conn(args.to_port)
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    out["capabilities"] = caps
    out["ihave_advertised"] = any(c.split()[:1] == ["IHAVE"] for c in caps if c.strip())
    out["streaming_advertised"] = any(
        c.split()[:1] == ["STREAMING"] for c in caps if c.strip())
    out["mode_stream"] = conn.cmd("MODE STREAM")[0]
    out["offer"] = conn.cmd("IHAVE " + args.msgid)[0]
    out["transit"] = out["offer"][:3] not in ("500", "501", "502")
    if not out["transit"]:
        conn.close()
        out["reason"] = "the target answered IHAVE with '{}'".format(out["offer"])
        out["ok"] = True          # the absence is the finding, not a failure
        return out

    if out["offer"].startswith("335"):
        send_block(conn, lines)
        out["transfer"] = conn.line()
    else:
        out["transfer"] = "(nothing sent: the offer drew " + out["offer"] + ")"

    # The same offer again: the Message-ID history must refuse it (RFC 3977
    # section 6.3.2, 435 "not wanted"), without the article crossing twice.
    out["duplicate"] = conn.cmd("IHAVE " + args.msgid)[0]
    if out["duplicate"].startswith("335"):
        send_block(conn, lines)
        out["duplicate_transfer"] = conn.line()

    # An article whose Path already names the target: the target has relayed
    # it before and MUST NOT take it again (RFC 5537 section 3.5).  The Path is
    # inside the article, so a correct server says 335 and then rejects.
    loop = ["Path: {}!not-for-mail".format(args.loop_identity),
            "From: gate@example.invalid", "Subject: loop", "Newsgroups: " + args.group,
            "Date: " + rfc5322_now(),
            "Message-ID: " + args.loop_msgid, "",
            "This article already names the target node in its Path."]
    out["loop_offer"] = conn.cmd("IHAVE " + args.loop_msgid)[0]
    if out["loop_offer"].startswith("335"):
        send_block(conn, loop)
        out["loop_result"] = conn.line()
    else:
        out["loop_result"] = out["loop_offer"]
    # RFC 4644 streaming, on the same connection and the same article.  The
    # target already holds it, so CHECK is the advisory duplicate (438) and a
    # client that ignores the advice and sends TAKETHIS anyway must draw 439
    # -- never a 2xx, and never a retry code (specs/peering.md 2.2, S4).
    out["check_duplicate"] = conn.cmd("CHECK " + args.msgid)[0]
    conn.sock.sendall(("TAKETHIS " + args.msgid + "\r\n").encode())
    send_block(conn, lines)
    out["takethis_duplicate"] = conn.line()
    # And a Message-ID the target has never seen: CHECK must want it (238) or
    # say why it does not, in the 431/438 classes and nowhere else.
    out["check_fresh"] = conn.cmd("CHECK <fresh.check@gate.example.invalid>")[0]
    conn.close()

    status, got = fetch(args.to_port, args.msgid)
    out["reread"] = status
    out["identical"] = (got == lines)
    out["loop_absent"] = fetch(args.to_port, args.loop_msgid)[0]
    out["streaming_ok"] = (out["check_duplicate"].startswith("438")
                           and out["takethis_duplicate"].startswith("439")
                           and out["check_fresh"][:3] in ("238", "431", "438"))
    out["ok"] = (out["transfer"].startswith("235")
                 and out["duplicate"].startswith("435")
                 and not out["loop_result"].startswith("2")
                 and out["reread"].startswith("220")
                 and out["identical"]
                 and out["streaming_ok"]
                 and out["loop_absent"].startswith("43"))
    return out


def cut(args):
    """SIGKILL the target from inside a transfer it has already agreed to take."""
    conn = Conn(args.to_port)
    out = {"mode": args.mode}
    if args.mode == "transit":
        out["open"] = conn.cmd("IHAVE " + args.msgid)[0]
        opened = out["open"].startswith("335")
    elif args.mode == "post":
        out["open"] = conn.cmd("POST")[0]
        opened = out["open"].startswith("340")
    else:
        out["open"] = conn.cmd("GROUP " + args.group)[0]
        opened = out["open"].startswith("211")
    out["opened"] = opened
    if opened and args.mode in ("transit", "post"):
        conn.sock.sendall(
            ("Path: sender.gate.example.invalid!not-for-mail\r\n"
             "From: gate@example.invalid\r\nSubject: interrupted\r\n"
             "Newsgroups: {}\r\nMessage-ID: {}\r\n\r\nhalf an ".format(
                 args.group, args.msgid)).encode())
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
    # An acknowledgement after the kill would mean the transfer was durable
    # when the process was already gone.
    out["ok"] = opened and not out["after_kill"].startswith(("reply: 235", "reply: 240"))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="phase", required=True)
    for name in ("presence", "relay", "cut", "post", "wait"):
        one = sub.add_parser(name)
        one.add_argument("--port", type=int, default=0)
        one.add_argument("--from-port", type=int, default=0)
        one.add_argument("--to-port", type=int, default=0)
        one.add_argument("--group", default="fn.letters")
        one.add_argument("--groups", default="")
        one.add_argument("--present", default="")
        one.add_argument("--absent", default="")
        one.add_argument("--msgid", default="")
        one.add_argument("--loop-msgid", default="<loop@example.invalid>")
        one.add_argument("--loop-identity", default="peer.example.invalid")
        one.add_argument("--mode", default="post")
        one.add_argument("--pid", type=int, default=0)
        one.add_argument("--seconds", type=float, default=30.0)
    args = parser.parse_args()
    handler = {"presence": presence, "relay": relay, "cut": cut,
               "post": post, "wait": wait}[args.phase]
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
# the wire tap: what a feed actually put on the socket

TAP_DRIVER = r'''#!/usr/bin/env python3
"""A line-recording TCP tap in front of one node.

Neither end of a feed logs the commands it sends, so without this there is no
way to say WHETHER an article crossed by IHAVE or by CHECK/TAKETHIS -- only
that it arrived. The tap forwards bytes between a client and one fixed
server and appends every complete CRLF line to a file with its direction.
It parses nothing, decides nothing and answers nothing: it is a recorder,
and the gate reads its file afterwards.
"""
import argparse, os, socket, threading, time


def pump(name, source, target, log, lock, cut_flag=None):
    """Forward, record, and -- once, when armed -- cut after an article block.

    The cut is how a gate reaches the one crash point a feed cannot otherwise
    reach on purpose: the receiver has the whole article and the sender has
    not yet heard the outcome. Arming it is creating `cut_flag`; the tap
    disarms it by removing the file, so one arming cuts one transfer."""
    pending = b""
    try:
        while True:
            chunk = source.recv(65536)
            if not chunk:
                break
            target.sendall(chunk)
            pending += chunk
            while b"\r\n" in pending:
                line, pending = pending.split(b"\r\n", 1)
                with lock:
                    log.write("{} {}\n".format(
                        name, line.decode("ascii", "replace")[:300]))
                    log.flush()
                if (name == "C>" and line == b"." and cut_flag
                        and os.path.exists(cut_flag)):
                    try:
                        os.unlink(cut_flag)
                    except OSError:
                        pass
                    with lock:
                        log.write("= cut after the article block at {:.3f}\n".format(
                            time.time()))
                        log.flush()
                    return
    except OSError:
        pass
    finally:
        for one in (source, target):
            try:
                one.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass


def serve(client, port, log, lock, cut_flag=None):
    try:
        server = socket.create_connection(("127.0.0.1", port), 5)
    except OSError as error:
        with lock:
            log.write("! no server on {}: {}\n".format(port, error))
            log.flush()
        client.close()
        return
    with lock:
        log.write("= session opened at {:.3f}\n".format(time.time()))
        log.flush()
    for name, source, target in (("C>", client, server), ("S<", server, client)):
        threading.Thread(target=pump,
                         args=(name, source, target, log, lock, cut_flag),
                         daemon=True).start()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--listen", type=int, default=0)
    parser.add_argument("--to", type=int, required=True)
    parser.add_argument("--log", required=True)
    parser.add_argument("--cut-flag", default=None,
                        help="while this file exists, cut the next transfer "
                             "after its article block and remove the file")
    args = parser.parse_args()
    lock = threading.Lock()
    log = open(args.log, "a", buffering=1)
    listener = socket.socket()
    listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listener.bind(("127.0.0.1", args.listen))
    listener.listen(8)
    print("TAPPING {}".format(listener.getsockname()[1]), flush=True)
    while True:
        try:
            client, _ = listener.accept()
        except OSError:
            continue
        serve(client, args.to, log, lock, args.cut_flag)


if __name__ == "__main__":
    main()
'''


# --------------------------------------------------------------------------
# the gate


class TwoNodeGate(deploy_gate.DeployGate):
    """The deploy gate with a second node, peer records and three scenarios."""

    TITLE = "Two-node gate"
    TOOL = "tools/twonode_gate.py"
    PREAMBLE = (
        "Two fn nodes from one commit, on one host, each with its own store, its own",
        "served groups and its own listener, running at the same time. This records",
        "what ran. It establishes nothing about the books, and where the tree has no",
        "transit surface yet it says so in place of the scenario rather than passing",
        "a weaker one under the same name.")
    FACT_KEYS = ("os", "kernel", "python3", "acl2version", "certificates",
                 "node a", "node b", "peer records", "three outcomes a",
                 "three outcomes b", "transit", "feed", "kill", "tcpcl")
    STANDING_GAPS = (
        "Both nodes are on ONE host, over loopback. Nothing here exercises a real\n"
        "  network, a partition, latency, or two machines' clocks disagreeing.",
        "A SIGKILL of a server process is not a power loss, and killing one node is\n"
        "  not a partition: A stays reachable throughout.",
        "One kill point is exercised. The enumerated cut table is\n"
        "  `tests/campaign/cuts.py`; this gate does not replace it.",
        "The peer records are configuration, not authorization: no lane on this tree\n"
        "  authenticates a peer, so a node accepts transit from whoever connects.",
        "No convergence claim. Two articles crossing once is not the merge property\n"
        "  of specs/peering.md section 4 (K4); that needs the certified statement.",
        "No third node, no concurrent load, no RFC conformance audit: the\n"
        "  assertions are this driver's, not a spec's.",
        "The `tcpcl` scenario carries opaque octets, not BPv7 bundles: TCPCLv4 does\n"
        "  not parse what it transfers, and no BP node is wired to the layer yet.",
        "The certificates were not re-established here; see the certificate row.")

    def __init__(self, *args, server_template=None, extra_overlays=(), **kwargs):
        super().__init__(*args, **kwargs)
        self.server_template = server_template
        self.extra_overlays = list(extra_overlays)
        self.a = NodeSpec(self, "a")
        self.b = NodeSpec(self, "b")
        self.nodes = (self.a, self.b)
        self.selected = None            # the server entry point, probed once
        self.commands = {}              # node name -> (kind, command)

    # -- plumbing ---------------------------------------------------------
    def ship(self):
        """The deploy gate's ship, plus any further overlays, in order."""
        super().ship()
        for overlay in self.extra_overlays:
            self.push_tree(overlay)

    def feed(self, phase: str, extra: str, name=None, timeout=300, expect=0) -> Step:
        return self.sh(name or "feed {}".format(phase), self.cd(
            "python3 {}/feed.py {} {}".format(self.run, phase, extra)),
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

    def derive(self, name, source: Step, note="", expect=0) -> Step:
        """A second step over a probe's result: the probe answered, and these
        are the assertions that answer has to satisfy."""
        step = Step(name, source.command, source.rc, source.output, 0.0, note, expect)
        self.steps.append(step)
        return step

    # -- the nodes --------------------------------------------------------
    def init_node(self, node: NodeSpec):
        groups = " ".join("--group {}".format(g) for g in GROUPS)
        self.sh("node {} directories".format(node.upper),
                "mkdir -p {} {}".format(node.dir, node.peers))
        step = self.sh("node {} store init".format(node.upper), self.cd(self.fn(
            "--store {} init {}".format(node.store, groups))), timeout=900)
        if step.rc != 0:
            raise GateError("node {} store init failed: {}".format(
                node.upper, step.output[:400]))
        self.sh("node {} config".format(node.upper),
                self.cd(self.fn("--store {} config".format(node.store))), timeout=900)
        # The node's OWN RFC 5537 <path-identity>. `fn-peer-local-identity`
        # reads this policy slot, and an unset slot reads as the empty
        # string, which `fn-path-names-p` never matches -- so until this
        # runs, a node cannot recognise its own name in a Path and RFC 5537
        # 3.5 loop suppression is inert. Measured on gate run bbd1f47: both
        # nodes accepted an article whose Path named them.
        identity = self.sh(
            "node {} path-identity".format(node.upper),
            self.cd(self.fn("--store {} policy set path-identity {}".format(
                node.store, node.path_identity))), timeout=900, expect=None)
        if identity.rc != 0:
            self.gaps.append(
                "node {} has no <path-identity> of its own ({}): "
                "`fn-peer-local-identity` reads the empty string, so this node "
                "cannot refuse an article whose Path already names it and every "
                "loop row below is about a check that cannot fire."
                .format(node.upper,
                        identity.output.strip().splitlines()[-1]
                        if identity.output.strip() else "no output"))

    def three_outcomes_node(self, node: NodeSpec, msgid: str, subject: str):
        """Accepted 0, refused 1, uncertain 3, on this node's own store (D13)."""
        payload = "{}/seed.article".format(node.dir)
        self.push_file(article(msgid, GROUPS[0], subject,
                               "Written on node {} by the two-node gate.".format(
                                   node.upper)), payload)
        uncertain = "<uncertain-{}@example.invalid>".format(node.name)
        accepted = self.sh("node {} outcome accepted".format(node.upper), self.cd(self.fn(
            "--store {} post --message-id '{}' --payload {} --group {}".format(
                node.store, msgid, payload, GROUPS[0]))), timeout=900, expect=EXIT_OK)
        refused = self.sh("node {} outcome refused".format(node.upper), self.cd(self.fn(
            "--store {} inspect --message-id '{}'".format(node.store, ABSENT_ID))),
            timeout=900, expect=EXIT_REFUSED)
        unsure = self.sh("node {} outcome uncertain".format(node.upper), self.cd(self.fn(
            "--store {} post --message-id '{}' --payload {} --group {} "
            "--inject-fault postpublish".format(
                node.store, uncertain, payload, GROUPS[0]))), timeout=900,
            expect=EXIT_UNCERTAIN)
        observed = (accepted.rc, refused.rc, unsure.rc)
        expected = (EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN)
        self.facts["three outcomes {}".format(node.name)] = (
            "accepted={} refused={} uncertain={} (expected {})".format(*observed, expected))
        if observed != expected:
            self.gaps.append(
                "node {}: the three outcomes did not stay distinct in the exit codes: "
                "observed {}, expected {} (D13)".format(node.upper, observed, expected))
        self.sh("node {} recover after the uncertain publication".format(node.upper),
                self.cd(self.fn("--store {} recover".format(node.store))), timeout=900)
        if accepted.rc == EXIT_OK:
            node.accepted.append(msgid)
        # The uncertain publication's article goes into NEITHER list.  A
        # postpublish fault is indeterminate by construction (D13): the
        # transaction may be durable or not, and a gate that asserted it either
        # way would be asserting a coin toss.  What is recorded is which way it
        # went on this run, as a probe with no expected code.
        probe = self.sh("node {} after recovery: the uncertain {}".format(
            node.upper, uncertain), self.cd(self.fn(
                "--store {} inspect --message-id '{}'".format(node.store, uncertain))),
            timeout=900, expect=None)
        self.gaps.append(
            "node {}: the injected uncertain publication {} is asserted in neither "
            "direction; `inspect` exited {} for it after recovery ({}). An "
            "indeterminate outcome is evidence about the report, not about the "
            "article.".format(node.upper, uncertain, probe.rc,
                              "the article is there" if probe.rc == EXIT_OK
                              else "the article is not there" if probe.rc == EXIT_REFUSED
                              else "neither"))

    def start_node(self, node: NodeSpec, tag="main", port=None) -> bool:
        """Start (or restart) one node, on a PINNED port once it has one.

        A peer record names the other node's listener by number, and the
        owner reads the peer table once, at startup. A restart on a fresh
        ephemeral port would therefore leave both records pointing at a
        closed port and silently end the feed, so every restart after the
        first reuses the port the node already had (the listener sets
        SO_REUSEADDR; tools/run_owner.py, the bind)."""
        if node.name not in self.commands:
            if self.server_template:
                self.commands[node.name] = ("custom", self.server_template.format(
                    store=node.store, run=node.dir, node=node.name))
            else:
                self.commands[node.name] = self.server_command(node.store, node.dir)
        self.selected, command = self.commands[node.name]
        pinned = port or node.port
        if pinned:
            command = command.replace("--port 0", "--port {}".format(pinned))
        started = self.start_server("node {} ({})".format(node.upper, self.selected),
                                    command, "{}-{}".format(node.name, tag), run=node.dir)
        if not started and self.selected != "reader" and not self.server_template:
            # The deploy gate's fallback, per node: an entry point that does not
            # start is a probe the gate fell back from, never a pass.
            fallback = "python3 tools/run_reader.py --store {} --port 0 --post".format(
                node.store)
            self.gaps.append(
                "node {}: the {} entry point did not reach LISTENING on this commit, so "
                "the gate fell back to tools/run_reader.py --post. Every served result "
                "for this node below is the reader's, not the {}'s."
                .format(node.upper, self.selected, self.selected))
            self.commands[node.name] = ("reader", fallback)
            self.selected, command = "reader", fallback
            if pinned:
                command = command.replace("--port 0", "--port {}".format(pinned))
            started = self.start_server("node {} (reader)".format(node.upper), command,
                                        "{}-{}".format(node.name, tag), run=node.dir)
        if not started:
            return False
        node.port = self.port
        node.kind = self.selected
        node.post_enabled = "--post" in command or self.selected.startswith(("owner", "fn"))
        node.pid = self.sh("node {} pid".format(node.upper),
                           "cat {}/server.pid".format(node.dir)).output.strip()
        self.facts["node {}".format(node.name)] = "{} on port {} ({}), store {}".format(
            self.selected, node.port, tag, node.store)
        return True

    def stop_node(self, node: NodeSpec, tag="main"):
        self.stop_server("node {} ({})".format(node.upper, tag), run=node.dir)

    def start_tap(self, node: NodeSpec) -> bool:
        """A recorder in front of one node, on the port its peer will dial."""
        out = "{}/tap-{}.out".format(node.dir, node.name)
        pid = "{}/tap.pid".format(node.dir)
        step = self.sh("wire tap in front of node {}".format(node.upper), self.cd("""
rm -f {out}
nohup python3 {run}/tap.py --to {port} --log {log} --cut-flag {log}.cut > {out} 2>&1 < /dev/null &
echo $! > {pid}
for i in $(seq 1 20); do
  if grep -m1 '^TAPPING' {out}; then exit 0; fi
  if ! kill -0 $(cat {pid}) 2>/dev/null; then echo TAP-DIED; cat {out}; exit 1; fi
  sleep 1
done
echo TAP-TIMEOUT; cat {out}; exit 1
""".format(run=self.run, port=node.port, log=node.tap_log, out=out, pid=pid)),
            timeout=120, expect=None)
        match = re.search(r"^TAPPING (\d+)", step.output, re.M)
        if step.rc != 0 or match is None:
            self.gaps.append(
                "no wire tap could be started in front of node {}: its peer dials it "
                "directly and no row below says which offer command (IHAVE, or RFC "
                "4644 CHECK/TAKETHIS) carried an article -- only that it arrived."
                .format(node.upper))
            return False
        node.tap_port = int(match.group(1))
        return True

    def require_live(self, node: NodeSpec, where: str) -> bool:
        """Is this node still the process that reached LISTENING?

        A server that has died must be said ONCE, with its own last lines,
        so that every row after it is about the death and not about the
        feature. On gate `0e5a7f8` node B stopped answering after its
        restart and two steps read `server closed the connection` with no
        indication that the process was gone.
        """
        step = self.sh("node {} is still serving ({})".format(node.upper, where),
                       "kill -0 {} 2>/dev/null && echo ALIVE || "
                       "{{ echo DEAD; tail -25 {}/server-{}-*.log 2>/dev/null | "
                       "tail -25; }}".format(node.pid or 0, node.dir, node.name),
                       timeout=120, expect=None)
        if "ALIVE" in step.output:
            return True
        self.gaps.append(
            "node {} was NOT running at {}: its server process is gone, so every "
            "row after this one that needed that socket is about the death and "
            "not about the feature. Its last lines: {}".format(
                node.upper, where,
                " | ".join(step.output.strip().splitlines()[-6:]) or "none"))
        return False

    def log_tail(self, node: NodeSpec, why: str) -> Step:
        """The node's own last lines, kept beside the step that needed them.

        `require_live` prints them when a process is GONE. A process that is
        alive and still closing every connection at accept prints nothing,
        and then the evidence carries `server closed the connection` with no
        way to tell what raised -- which is where gate `27cb717` stopped.
        `ACCEPT-FAULT` and `FEED-FAULT` both land in these logs.
        """
        # No second `tail` and no `||`: with `set -o pipefail` that pair
        # answered `NO-SERVER-LOG` on gate `0ec08bb` while the six log files
        # were sitting there readable, so the one run that was supposed to
        # capture the fault captured nothing.
        return self.sh("node {} server log ({})".format(node.upper, why),
                       "tail -n 40 {}/server-{}-*.log 2>&1; true".format(
                           node.dir, node.name),
                       timeout=120, expect=None)

    def tap_mark(self, node: NodeSpec) -> int:
        """Where the tap log stands now, so the next read is this step alone.

        Off the step list: a bookmark is not a result."""
        try:
            done = self.host.sh("wc -l < {} 2>/dev/null || echo 0".format(node.tap_log),
                                60)
            return int(done.stdout.decode("utf-8", "replace").strip().split()[-1])
        except (subprocess.SubprocessError, ValueError, IndexError, OSError):
            return 0

    def read_tap(self, node: NodeSpec, name: str, since=0, expect=0) -> Step:
        """The command and status lines the tap in front of `node` recorded.

        This is the only place the gate can see WHICH command carried an
        article. It greps; it does not decide."""
        return self.sh(
            name,
            "tail -n +{} {} 2>/dev/null | grep -E "
            "'^C> (IHAVE|CHECK|TAKETHIS|MODE STREAM)|^S< [0-9][0-9][0-9] ' "
            "| tail -60".format(since + 1, node.tap_log),
            timeout=120, expect=expect)

    def configure_peering(self, streaming=False, tag="peered"):
        """The peer records, and the restart that makes them live.

        Three facts force this shape and all three are the tree's, not this
        harness's. A record names the OTHER node's listener by port, so both
        ports must be known before either record can be written. `peer add`
        is a configuration transaction on a store an owner must not be
        holding. And the owner reads the peer table exactly once, at
        startup -- for the accept decision (`fn-owner-peer-for-address`,
        specs/peering.md 1.1) and for the feed table
        (`fn-owner-feed-configure`, books/owner-feed.lisp). So the nodes are
        started once to learn their ports, stopped, given their records, and
        started again on the SAME ports.

        There is no live-reconfiguration command on this tree: tools/run_owner.py
        accepts POST, VERSION, CONNECTIONS, ADVANCE, OBSERVE, DECLARE-GROUP and
        QUIT and nothing that re-reads the peer table. When one exists, this
        whole method becomes one control line and the restart goes away.
        """
        for node in self.nodes:
            self.stop_node(node, tag="pre-peer")
        self.peer_records(streaming=streaming)
        for node in self.nodes:
            if not self.start_node(node, tag=tag, port=node.port):
                raise GateError(
                    "node {} did not come back on port {} after its peer record was "
                    "written".format(node.upper, node.port))

    def peer_records(self, streaming=False):
        """A peer record on each node naming the other (specs/peering.md 1.2).

        `streaming` is the OUTBOUND half of RFC 4644: with it the peer's feed
        offers with CHECK/TAKETHIS, without it with IHAVE. The inbound bound
        is left unsaid, because the ceiling belongs to ACL2
        (`fn-store-cfg-peer-record` supplies *fn-record-max-payload*) and a
        number typed here would be a second owner of it -- which is exactly
        how the CLI default of 1048576 came to refuse every `peer add` made
        with the defaults, `:peer-record`, silently, for as long as the CLI
        has existed.
        """
        probe = self.sh("peer record CLI", self.cd("""
if python3 tools/run_store.py --store /nonexistent peer --help >/dev/null 2>&1; then
  echo STORE-PEER
elif [ -x bin/fn ] && ./bin/fn peer --help >/dev/null 2>&1; then echo FN-PEER
else echo NONE; fi
"""))
        kind = probe.output.strip().splitlines()[-1] if probe.output.strip() else "NONE"
        self.facts["peer records"] = kind.lower()
        for node, other in ((self.a, self.b), (self.b, self.a)):
            target = "{}/{}.peer".format(node.peers, other.name)
            if kind in ("STORE-PEER", "FN-PEER"):
                # `peer add' is a configuration record: the store must not be
                # held by an owner, so this runs before the servers start.
                # The auth slot is the loopback address the other node dials
                # from, which is what decides the role at accept
                # (specs/peering.md 1.1, fn-owner-peer-for-address).
                added = self.sh(
                    "node {} peer record for {}".format(node.upper, other.upper),
                    self.cd(self.fn(
                        "--store {} peer add {} --path-identity {} "
                        "--nntp 127.0.0.1:{} --inbound-groups 'fn.*' "
                        "--outbound-groups 'fn.*' {}"
                        "--source-address 127.0.0.1".format(
                            node.store, other.name, other.path_identity,
                            other.tap_port or other.port,
                            "--streaming " if streaming else ""))),
                    timeout=900,
                    note="outbound half: {} (RFC 4644 streaming is the peer "
                         "record's flag, and the owner reads the table once, "
                         "at start-up)".format(
                             "CHECK/TAKETHIS" if streaming else "IHAVE"),
                    expect=None)
                if added.rc != 0:
                    self.gaps.append(
                        "node {} refused the peer record for {} ({}), so this node "
                        "resolves no peer at accept and configures no feed: every "
                        "transit row below is about a reader connection."
                        .format(node.upper, other.upper,
                                added.output.strip().splitlines()[-1]
                                if added.output.strip() else "no output"))
                listing = self.sh(
                    "node {} lists its peers".format(node.upper),
                    self.cd(self.fn("--store {} peer list".format(node.store))),
                    timeout=900)
                if other.name not in listing.output:
                    self.gaps.append(
                        "node {} accepted `peer add {}` but `peer list` does not show "
                        "it: the record did not survive the replay, so the transit "
                        "scenario below is running without the peer table it names."
                        .format(node.upper, other.name))
                continue
            self.push_file(self.peer_stub(node, other), target)
            self.skip("node {} peer record for {}".format(node.upper, other.upper),
                      "peer record CLI (specs/peering.md 1.2, (:set-peer record))",
                      "peer record: not available on this tree. No CLI on this commit "
                      "writes an `fn-cfg-peerp`, and `*fn-cfg-delta-kinds*` has no "
                      "`(:set-peer record)`, so the record that specs/peering.md 1.2 "
                      "defines was written to {} as an inert stub and read by nothing. "
                      "Neither node resolved the other as a peer at :open; the transit "
                      "scenario below therefore connects as an ordinary client."
                      .format(target))

    @staticmethod
    def peer_stub(node: NodeSpec, other: NodeSpec) -> bytes:
        """The record kind of specs/peering.md 1.2, for the day a CLI reads it."""
        return (""";; A peer record for node {them}, held by node {us}.
;; specs/peering.md 1.2: (fn-cfg-peer-make name path-identity transport
;;                                         inbound outbound auth).
;; NOTHING ON THIS TREE READS THIS FILE.  It is written by
;; tools/twonode_gate.py so that the shape the two-node harness expects is on
;; disk and reviewable before the peering lane lands its `(:set-peer record)`
;; delta; when that delta exists the gate calls the CLI instead and this file
;; is not written at all.
(fn-cfg-peer-make
  "{them}"                                  ; name: the local label
  "{identity}"                              ; path-identity, RFC 5537 3.2
  (:nntp "127.0.0.1" {port})                ; transport
  (("fn.*") 1048576 4)                      ; inbound: groups, max octets, max in flight
  (("fn.*") nil 64 1000)                    ; outbound: groups, streaming, queue, backoff ms
  (:source-address "127.0.0.1"))            ; auth, specs/peering.md 6
""".format(them=other.name, us=node.name, identity=other.path_identity,
           port=other.port)).encode()

    # -- the scenarios ----------------------------------------------------
    def scenario_independent(self):
        """Without a feed, what A accepted is A's.  This is the control."""
        for node, other in ((self.a, self.b), (self.b, self.a)):
            step = self.feed("presence", "--port {} --groups {} --present '{}' --absent '{}'"
                             .format(node.port, ",".join(GROUPS),
                                     ",".join(node.accepted),
                                     ",".join(other.accepted + node.rejected)),
                             name="independent: node {} holds its own and not {}'s".format(
                                 node.upper, other.upper))
            if step.rc != 0:
                self.gaps.append(
                    "node {} failed the independence control: it did not serve exactly "
                    "what it accepted. Every later claim that an article reached a node "
                    "rests on this, so treat the feed result below as unfounded."
                    .format(node.upper))
        alive = self.sh("both servers are still up", 'echo "{}"'.format(" ".join(
            "{name}=$(kill -0 {pid} 2>/dev/null && echo ALIVE || echo DEAD)".format(
                pid=node.pid or 0, name=node.upper) for node in self.nodes)))
        if "DEAD" in alive.output:
            self.gaps.append("a server was not running at the end of the independent "
                             "scenario: {}".format(alive.output.strip()))

    def scenario_feed(self):
        """Offer A's article to B by hand, RFC 3977 6.3.2, and reread it on B."""
        probe = self.feed(
            "relay",
            "--from-port {} --to-port {} --msgid '{}' --group {} --loop-msgid '{}' "
            "--loop-identity {}".format(
                self.a.port, self.b.port, ARTICLE_A, GROUPS[0], LOOP_ID,
                self.b.path_identity),
            name="feed: offer {} from A to B".format(ARTICLE_A), expect=None)
        result = self.payload(probe)
        self.b.transit = result.get("offer", "")
        self.facts["transit"] = "IHAVE -> '{}'; CAPABILITIES lists IHAVE: {}".format(
            result.get("offer", "no answer"), result.get("ihave_advertised"))
        if not result.get("transit"):
            self.facts["feed"] = "not exercised"
            self.gaps.append(
                "peering: not available on this tree. Node B answered `IHAVE {}` with "
                "'{}' and its CAPABILITIES block does not list IHAVE, so the transit "
                "commands of specs/peering.md 1.1 (IHAVE, CHECK, TAKETHIS, MODE STREAM) "
                "are not served by this commit. NOTHING below establishes that an "
                "article can cross between two fn nodes: the duplicate-suppression and "
                "loop-suppression teeth were not exercised either, because there was no "
                "transfer to duplicate."
                .format(ARTICLE_A, result.get("offer", "no answer")))
            self.skip("feed: {} reread on B".format(ARTICLE_A),
                      "feed.py relay (IHAVE, 335, article, 235)",
                      "peering: not available on this tree")
            self.skip("feed: a second IHAVE of {} draws 435".format(ARTICLE_A),
                      "feed.py relay (Message-ID history)",
                      "peering: not available on this tree")
            self.skip("feed: an article whose Path names B is refused",
                      "feed.py relay (RFC 5537 3.5 loop suppression)",
                      "peering: not available on this tree")
            return
        self.facts["feed"] = ("offer={offer} transfer={transfer} duplicate={duplicate} "
                              "check={check} takethis={takethis} "
                              "loop={loop} reread={reread} identical={identical}".format(
                                  check=result.get("check_duplicate"),
                                  takethis=result.get("takethis_duplicate"),
                                  offer=result.get("offer"),
                                  transfer=result.get("transfer"),
                                  duplicate=result.get("duplicate"),
                                  loop=result.get("loop_result"),
                                  reread=result.get("reread"),
                                  identical=result.get("identical")))
        self.derive("feed: {} reread on B".format(ARTICLE_A), probe,
                    "IHAVE {}; the octets B serves are compared to the octets A served, "
                    "line for line".format(ARTICLE_A))
        if str(result.get("transfer", "")).startswith("235"):
            self.b.accepted.append(ARTICLE_A)
        if not str(result.get("duplicate", "")).startswith("435"):
            self.gaps.append(
                "the second IHAVE of {} drew '{}', not 435: the Message-ID history did "
                "not refuse an article the node already holds (RFC 3977 6.3.2)."
                .format(ARTICLE_A, result.get("duplicate")))
        if not str(result.get("check_duplicate", "")).startswith("438"):
            self.gaps.append(
                "CHECK of an article B already holds drew '{}', not 438: RFC 4644 "
                "2.4's duplicate answer is not what the streaming peer sees."
                .format(result.get("check_duplicate")))
        if not str(result.get("takethis_duplicate", "")).startswith("439"):
            self.gaps.append(
                "TAKETHIS of an article B already holds drew '{}', not 439: a client "
                "that ignores the advisory CHECK must be refused after the bytes "
                "(RFC 4644 2.5), and a 2xx there would be a second copy."
                .format(result.get("takethis_duplicate")))
        if str(result.get("loop_result", "")).startswith("2"):
            self.gaps.append(
                "an article whose Path already names B was ACCEPTED by B ('{}'): the "
                "loop suppression of RFC 5537 3.5 is not in place."
                .format(result.get("loop_result")))
        self.b.rejected.append(LOOP_ID)

    def deliver_by_feed(self, source: NodeSpec, target: NodeSpec, msgid: str,
                        label: str, expect_command: str, seconds=60) -> bool:
        """One article, posted on `source`, carried to `target` by fn's own feed.

        This is the v0 question. The offering side is the feed TABLE of
        books/owner-feed.lisp, stepped by the owner and driven by
        tools/run_owner.py -- not this harness. Nothing is posted through the
        CLI: the running owner holds the store lock, and an article written
        behind it would never reach `fn-own-outcome` and so would never be
        enqueued. What is asserted is that `target` serves the article and
        serves the SAME octets `source` serves, and that the command the tap
        recorded is the one this peer record asks for.
        """
        mark = self.tap_mark(target)
        posted = self.feed("post", "--port {} --msgid '{}' --group {}".format(
            source.port, msgid, GROUPS[0]),
            name="{}: {} posts {}".format(label, source.upper, msgid), expect=None)
        if not self.payload(posted).get("ok"):
            self.gaps.append(
                "{}: POST of {} on node {} answered '{}', not 240, so the feed had "
                "nothing durable to offer and this direction was not exercised."
                .format(label, msgid, source.upper,
                        self.payload(posted).get("result", "nothing")))
            self.skip("{}: {} receives {} from {}'s feed".format(
                label, target.upper, msgid, source.upper),
                "run_owner.py Feed (books/owner-feed.lisp)",
                "the article never became durable on node {}".format(source.upper))
            return False
        source.accepted.append(msgid)
        arrival = self.feed(
            "wait", "--port {} --from-port {} --msgid '{}' --seconds {}".format(
                target.port, source.port, msgid, seconds),
            name="{}: {} receives {} from {}'s feed".format(
                label, target.upper, msgid, source.upper),
            expect=None)
        result = self.payload(arrival)
        self.facts["{} {}".format(label, msgid)] = (
            "status={} attempts={} octets identical to the source={}".format(
                result.get("status", "none"), result.get("attempts"),
                result.get("identical")))
        if not result.get("ok"):
            self.gaps.append(
                "{}: node {} never served {} within {} s of node {} accepting it, so "
                "the outbound feed did not transfer it. Nothing below about this "
                "direction is about an article that crossed."
                .format(label, target.upper, msgid, seconds, source.upper))
            self.read_tap(target, "{}: what {}'s feed put on the wire".format(
                label, source.upper), since=mark, expect=None)
            self.log_tail(source, "its feed did not deliver")
            self.log_tail(target, "it did not receive")
            return False
        target.accepted.append(msgid)
        self.derive("{}: {} serves {} byte for byte as {} does".format(
            label, target.upper, msgid, source.upper), arrival,
            "the ARTICLE block node {} returns is compared line for line with the "
            "one node {} returns; identical={}".format(
                target.upper, source.upper, result.get("identical")))
        if result.get("identical") is not True:
            self.gaps.append(
                "{}: node {} serves {} but NOT byte for byte as node {} serves it "
                "(identical={}): a relaying agent must alter nothing but Path and "
                "Xref (RFC 5537 3.6).".format(label, target.upper, msgid,
                                              source.upper, result.get("identical")))
        wire = self.read_tap(target, "{}: {}'s feed offered {} with {}".format(
            label, source.upper, msgid, expect_command), since=mark, expect=None)
        offered = [line for line in wire.output.splitlines()
                   if line.startswith("C> " + expect_command)]
        self.facts["{} wire".format(label)] = (
            "; ".join(line[3:] for line in wire.output.splitlines()
                      if line.startswith("C> "))[:400] or "nothing recorded")
        if not offered:
            self.gaps.append(
                "{}: the tap in front of node {} recorded no `{}` from node {}'s "
                "feed, so this run does not establish which offer command carried "
                "{}. What it recorded was: {}".format(
                    label, target.upper, expect_command, source.upper, msgid,
                    "; ".join(wire.output.splitlines()[:8]) or "nothing"))
        return True

    def scenario_owner_feed(self):
        """A posts, A's OWN feed offers it to B by IHAVE, and then the other way.

        This is the outbound half the wave-9 handoff recorded as not
        delivered, and the v0 milestone: an article crossing between two fn
        nodes with fn on both ends of the decision.
        """
        if not (self.a.post_enabled and self.b.post_enabled):
            for direction in ("A to B", "B to A"):
                self.skip("owner feed: {}".format(direction),
                          "run_owner.py Feed (books/owner-feed.lisp)",
                          "owner feed: neither node serves POST on this commit, so "
                          "nothing can become durable for a feed to offer.")
            return
        delivered = {}
        for source, target, tag in ((self.a, self.b, "ab"), (self.b, self.a, "ba")):
            msgid = "<fed-{}@example.invalid>".format(tag)
            delivered[tag] = self.deliver_by_feed(
                source, target, msgid, "owner feed", "IHAVE")
            if not delivered[tag]:
                continue
            # The duplicate path on a SECOND offer of the same article, by
            # hand: the peer's own history is what makes a re-offer safe
            # after a restart (RFC 3977 6.3.2, RFC 4644 2.4).
            again = self.feed(
                "relay",
                "--from-port {} --to-port {} --msgid '{}' --group {} "
                "--loop-msgid '{}' --loop-identity {}".format(
                    source.port, target.port, msgid, GROUPS[0], LOOP_ID,
                    target.path_identity),
                name="owner feed: a second offer of {} draws 435/438".format(msgid),
                expect=None)
            second = self.payload(again)
            self.facts["owner feed {} duplicate".format(tag)] = (
                "ihave={} check={} takethis={}".format(
                    second.get("offer"), second.get("check_duplicate"),
                    second.get("takethis_duplicate")))
            if not str(second.get("offer", "")).startswith("435"):
                self.gaps.append(
                    "owner feed: re-offering {} to node {} drew '{}', not 435: the "
                    "history answer that makes a restart-by-offer safe is not there."
                    .format(msgid, target.upper, second.get("offer")))
            if not str(second.get("check_duplicate", "")).startswith("438"):
                self.gaps.append(
                    "owner feed: CHECK of {} on node {} drew '{}', not 438."
                    .format(msgid, target.upper, second.get("check_duplicate")))
        self.facts["owner feed"] = "A->B {} ; B->A {}".format(
            delivered.get("ab"), delivered.get("ba"))

    def scenario_owner_feed_streaming(self):
        """The same crossing, with RFC 4644 CHECK/TAKETHIS carrying it.

        Streaming is the peer record's OUTBOUND flag and the owner reads the
        peer table once, at startup, so the only way to exercise both offer
        commands in one deploy is to rewrite both records and restart both
        nodes. `peer add` over a name that already exists replaces the
        record (`fn-cfg-set-peer-delta`), so this is one more `peer add`
        each and the ports do not move.
        """
        if not (self.a.post_enabled and self.b.post_enabled):
            self.skip("owner feed: streaming (RFC 4644)",
                      "peer add --streaming, then run_owner.py Feed",
                      "owner feed: neither node serves POST on this commit")
            return
        self.configure_peering(streaming=True, tag="streaming")
        delivered = self.deliver_by_feed(
            self.a, self.b, "<fed-streaming@example.invalid>",
            "owner feed streaming", "CHECK")
        self.facts["owner feed streaming"] = str(delivered)

    def scenario_feed_restart(self):
        """K5: kill -9 A with an offer outstanding; the re-offer delivers once.

        Node B is stopped first, so A's feed has an entry it cannot deliver
        and the (:feed-enqueue ...) record is on disk with no outcome.  A is
        then killed with SIGKILL -- no shutdown path runs -- and both nodes
        are restarted.  fn-own-reopen restarts every feed, which fences the
        in-flight entry back to :queued with its attempt retired, so the next
        command for it is a CHECK or an IHAVE and never a blind TAKETHIS; B's
        own history absorbs the one retransmission a lost reply can cause.
        What this asserts is that B ends with exactly ONE copy.
        """
        if not self.a.post_enabled:
            self.skip("owner feed: restart by offer (K5)",
                      "kill -9 with an offer outstanding",
                      "owner feed: node A does not serve POST on this commit")
            return
        msgid = "<fed-restart@example.invalid>"
        mark = self.tap_mark(self.b)
        # B's OWN STORE, before and after: "exactly one copy" is a count in
        # the receiver, not a status line in the sender. A reread cannot
        # tell one copy from two -- the store would refuse the second and
        # the reread would look identical either way.
        before = self.feed("presence", "--port {} --groups {}".format(
            self.b.port, GROUPS[0]),
            name="owner feed: node B group count before the kill", expect=None)
        start_count = self.group_count(self.payload(before), GROUPS[0])
        self.stop_node(self.b)
        posted = self.feed("post", "--port {} --msgid '{}' --group {}".format(
            self.a.port, msgid, GROUPS[0]),
            name="owner feed: A posts {} while B is down".format(msgid), expect=None)
        if not self.payload(posted).get("ok"):
            self.gaps.append(
                "owner feed: POST of {} on node A answered '{}' while B was down, so "
                "the restart scenario had no queued offer to resolve."
                .format(msgid, self.payload(posted).get("result", "nothing")))
            self.start_node(self.b, tag="restart")
            return
        # Node A accepted this article by POST and holds it. Without this the
        # later "node A is unchanged by node B's death" step counts it as an
        # article only B ever accepted and asserts A does NOT hold it, which
        # is false the moment the feed starts working.
        self.a.accepted.append(msgid)
        journal = self.sh(
            "owner feed: A's FNFD journal for B",
            "ls -l {}/feed/ 2>/dev/null | tail -5 || echo NO-FEED-JOURNAL".format(
                self.a.store), expect=None)
        self.facts["feed journal"] = journal.output.strip().splitlines()[-1] \
            if journal.output.strip() else "none"
        if "NO-FEED-JOURNAL" in journal.output:
            self.gaps.append(
                "owner feed: node A wrote no <store>/feed/*.fnfd file while an offer "
                "was outstanding, so nothing on disk records the decision to offer "
                "and the restart below resolves from memory that did not survive.")
        # The decision to feed THIS article, on disk, before the kill. An
        # FNFD record carries the Message-ID as text, so the file itself
        # answers it. Without this the scenario cannot tell "the restart
        # replayed the entry and re-offered it" from "the entry was never
        # durable and there was nothing to replay" -- which is exactly what
        # gate 15ac399 could not tell: node A replayed eight records, none
        # of them an enqueue, and never offered the article again.
        named = self.sh(
            "owner feed: A's journal names {} before the kill".format(msgid),
            "grep -a -c -- '{}' {}/feed/*.fnfd 2>/dev/null || echo 0".format(
                msgid, self.a.store), expect=None)
        hits = named.output.strip().splitlines()[-1] if named.output.strip() else "0"
        self.facts["feed journal names the queued article"] = hits
        if hits.strip() in ("", "0"):
            self.gaps.append(
                "owner feed: node A's FNFD journal does not name {} while it is "
                "queued and undeliverable, so the decision to feed it is in memory "
                "and nowhere else. specs/peering.md 3.3 writes (:feed-enqueue peer "
                "msgid tick) BEFORE the entry is :queued, and the `kill -9` below "
                "will lose it.".format(msgid))
        self.sh("owner feed: kill -9 node A", "kill -9 {} || true".format(self.a.pid),
                expect=None)
        self.start_node(self.b, tag="restart")
        if not self.start_node(self.a, tag="restart"):
            self.gaps.append("owner feed: node A did not restart after the kill")
            return
        self.require_live(self.b, "the K5 restart, before the arrival")
        self.require_live(self.a, "the K5 restart, before the arrival")
        arrival = self.feed(
            "wait", "--port {} --from-port {} --msgid '{}' --seconds 90".format(
                self.b.port, self.a.port, msgid),
            name="owner feed: B receives {} after A's restart (K5)".format(msgid),
            expect=None)
        result = self.payload(arrival)
        self.facts["owner feed restart"] = "status={} attempts={} identical={}".format(
            result.get("status", "none"), result.get("attempts"),
            result.get("identical"))
        if not result.get("ok"):
            self.gaps.append(
                "owner feed: after `kill -9` of node A and a restart of both nodes, "
                "node B never served {} within 90 s ({}). K5's restart-by-offer is "
                "NOT evidenced by this run.".format(
                    msgid, result.get("last_error", "no error reported")))
            for node in self.nodes:
                self.log_tail(node, "the K5 arrival did not happen")
            self.read_tap(self.b, "owner feed: what crossed after A's restart",
                          since=mark, expect=None)
            return
        self.b.accepted.append(msgid)
        counted = self.feed(
            "presence", "--port {} --groups {} --present '{}'".format(
                self.b.port, GROUPS[0], msgid),
            name="owner feed: B serves {} after the restart".format(msgid),
            expect=None)
        end_count = self.group_count(self.payload(counted), GROUPS[0])
        self.facts["owner feed restart copies"] = (
            "node B {} held {} articles before the kill and holds {} after"
            .format(GROUPS[0], start_count, end_count))
        if start_count is None or end_count is None:
            self.gaps.append(
                "owner feed: node B's GROUP line did not carry a count either side "
                "of node A's kill, so 'exactly one copy' rests on the reread alone, "
                "which cannot tell one copy from two.")
        elif end_count != start_count + 1:
            self.gaps.append(
                "owner feed: node B's {} went from {} articles to {} across node A's "
                "kill and restart. One article crossed, so exactly one is the right "
                "difference: K5 forbids the restart resolving by a second transfer."
                .format(GROUPS[0], start_count, end_count))
        # K5's teeth, and the only place this gate can grow them: the tap in
        # front of B saw every octet A's feed sent across the kill. A re-offer
        # is an IHAVE or a CHECK; a duplicate TRANSFER would be a second
        # accepted outcome for one Message-ID. "Exactly one copy" asserted by
        # rereading the article cannot tell those apart -- the store would
        # refuse the second copy and the reread would look identical.
        wire = self.read_tap(
            self.b, "owner feed: across the kill, B accepted {} exactly once".format(
                msgid), since=mark, expect=None)
        lines = wire.output.splitlines()
        offers = [one for one in lines
                  if one.startswith(("C> IHAVE", "C> CHECK")) and msgid in one]
        accepted = [one for one in lines if one.startswith(("S< 235", "S< 239"))]
        refused = [one for one in lines if one.startswith(("S< 435", "S< 438",
                                                           "S< 439"))]
        # One article block per TAKETHIS (RFC 4644 2.5: the article always
        # follows) and one per IHAVE go-ahead (RFC 3977 6.3.2: 335 is the
        # send). A `238` is the CHECK answer -- permission, not a send --
        # and counting it made one correct transfer read as two.
        transfers = [one for one in lines
                     if one.startswith(("C> TAKETHIS", "S< 335"))]
        self.facts["owner feed restart wire"] = (
            "offers={} article-blocks={} accepted={} "
            "refused-as-duplicate={} | {}".format(
                len(offers), len(transfers), len(accepted), len(refused),
                "; ".join(one[3:] for one in lines
                          if one.startswith("C> "))[:400] or "nothing recorded"))
        if len(accepted) != 1:
            self.gaps.append(
                "owner feed: the tap in front of node B recorded {} accepted "
                "transfers of {} across node A's kill, not exactly one. K5 says a "
                "restart resolves by RE-OFFER and never by a second transfer; the "
                "commands recorded were: {}".format(
                    len(accepted), msgid,
                    "; ".join(one for one in lines)[:400] or "none"))
        if not offers:
            self.gaps.append(
                "owner feed: the tap in front of node B recorded no offer naming {} "
                "after node A restarted, so what delivered it is not established by "
                "this run.".format(msgid))
        # The negative K5 actually claims. One go-ahead means the article
        # block crossed once; a second is a duplicate TRANSFER, which is the
        # thing the restart-by-offer discipline exists to prevent.
        if len(transfers) > 1:
            self.gaps.append(
                "owner feed: the tap in front of node B recorded {} article blocks "
                "for {} across node A's kill. K5 says a restart "
                "resolves by RE-OFFER and the peer's own history absorbs the one "
                "retransmission a lost reply can cause; more than one article block "
                "on the wire is the duplicate transfer it forbids. Recorded: {}"
                .format(len(transfers), msgid, "; ".join(transfers)[:300]))

    def scenario_feed_peer_cut(self):
        """The receiver has the article; the sender has not heard the outcome.

        The one crash point a feed cannot otherwise reach on purpose, and the
        one K5 is really about: the transfer completed on the wire and the
        reply did not come back. Node B is stopped, node A posts (the entry
        is queued and undeliverable), the tap in front of B is ARMED, B is
        started, and A's feed offers and transfers -- at which point the tap
        cuts the connection after the article block and before the status
        line. A therefore has an in-flight entry with no outcome and MUST NOT
        record one.

        What this asserts is the only thing that is true either way: B ends
        holding the article exactly once, and node A observed at most one
        accepted transfer of it. Whether B committed before the cut is
        genuinely indeterminate, and a gate that asserted it either way would
        be asserting a coin toss (D13).
        """
        if not self.a.post_enabled:
            self.skip("owner feed: the reply is lost mid-transfer",
                      "tap --cut-flag, then the feed re-offers",
                      "owner feed: node A does not serve POST on this commit")
            return
        if not self.b.tap_port:
            self.skip("owner feed: the reply is lost mid-transfer",
                      "tap --cut-flag, then the feed re-offers",
                      "no tap in front of node B, so the cut cannot be placed")
            return
        msgid = "<fed-cut@example.invalid>"
        before = self.feed("presence", "--port {} --groups {}".format(
            self.b.port, GROUPS[0]),
            name="owner feed cut: node B group count before", expect=None)
        start_count = self.group_count(self.payload(before), GROUPS[0])
        mark = self.tap_mark(self.b)
        self.stop_node(self.b, tag="pre-cut")
        posted = self.feed("post", "--port {} --msgid '{}' --group {}".format(
            self.a.port, msgid, GROUPS[0]),
            name="owner feed cut: A posts {} while B is down".format(msgid),
            expect=None)
        if not self.payload(posted).get("ok"):
            self.gaps.append(
                "owner feed cut: POST of {} on node A answered '{}' while B was "
                "down, so there was no queued offer to cut.".format(
                    msgid, self.payload(posted).get("result", "nothing")))
            self.start_node(self.b, tag="after-cut")
            return
        self.a.accepted.append(msgid)
        self.sh("owner feed cut: arm the tap in front of node B",
                "touch {}.cut".format(self.b.tap_log), expect=None)
        if not self.start_node(self.b, tag="after-cut"):
            self.gaps.append("owner feed cut: node B did not restart")
            return
        arrival = self.feed(
            "wait", "--port {} --from-port {} --msgid '{}' --seconds 120".format(
                self.b.port, self.a.port, msgid),
            name="owner feed cut: B serves {} after the lost reply".format(msgid),
            expect=None)
        result = self.payload(arrival)
        armed = self.sh("owner feed cut: the arming file was consumed",
                        "test -e {}.cut && echo STILL-ARMED || echo CUT-TAKEN".format(
                            self.b.tap_log), expect=None)
        wire = self.read_tap(self.b, "owner feed cut: what crossed after the cut",
                             since=mark, expect=None)
        lines = wire.output.splitlines()
        accepted = [one for one in lines if one.startswith(("S< 235", "S< 239"))]
        self.facts["owner feed cut"] = (
            "{} ; served={} identical={} accepted-transfers-observed={} | {}".format(
                armed.output.strip().splitlines()[-1] if armed.output.strip() else "?",
                result.get("status", "none"), result.get("identical"), len(accepted),
                "; ".join(one[3:] for one in lines
                          if one.startswith("C> "))[:400] or "nothing recorded"))
        if "CUT-TAKEN" not in armed.output:
            self.gaps.append(
                "owner feed cut: the tap in front of node B never took the cut, so "
                "no reply was lost and this scenario measured an ordinary transfer.")
        if not result.get("ok"):
            self.gaps.append(
                "owner feed cut: node B never served {} within 120 s of the cut. A "
                "lost reply must be resolved by a re-offer (K5); on this run it was "
                "not, so the article is lost between two nodes that are both up."
                .format(msgid))
            return
        self.b.accepted.append(msgid)
        if len(accepted) > 1:
            self.gaps.append(
                "owner feed cut: node A observed {} accepted transfers of {} across "
                "one lost reply, not at most one: the re-offer path transferred the "
                "article twice.".format(len(accepted), msgid))
        after = self.feed("presence", "--port {} --groups {} --present '{}'".format(
            self.b.port, GROUPS[0], msgid),
            name="owner feed cut: node B holds {} exactly once".format(msgid),
            expect=None)
        end_count = self.group_count(self.payload(after), GROUPS[0])
        self.facts["owner feed cut copies"] = (
            "node B {} held {} articles in {} and now holds {}".format(
                GROUPS[0], start_count, GROUPS[0], end_count))
        if start_count is None or end_count is None:
            self.gaps.append(
                "owner feed cut: node B's GROUP line did not carry a count either "
                "side of the cut, so 'exactly one copy' rests on the reread alone.")
        elif end_count != start_count + 1:
            self.gaps.append(
                "owner feed cut: node B's {} went from {} articles to {} across one "
                "lost reply; exactly one article crossed, so exactly one is the "
                "right difference.".format(GROUPS[0], start_count, end_count))

    @staticmethod
    def group_count(payload: dict, group: str):
        """The article count out of a `211 n low high name` line, or None."""
        line = (payload.get("groups") or {}).get(group, "")
        parts = str(line).split()
        if len(parts) >= 2 and parts[0] == "211" and parts[1].isdigit():
            return int(parts[1])
        return None

    def scenario_kill(self):
        """Kill B inside a transfer it agreed to take; recover it; reread both."""
        mode = ("transit" if self.b.transit and self.b.transit.startswith("335")
                else "post" if self.b.post_enabled else "read")
        if mode == "read":
            self.gaps.append(
                "node B offers neither a transit surface nor POST on this commit, so "
                "the kill could not land inside a transfer: it landed on an open reader "
                "connection instead, and 'the unfinished transfer is absent' below is "
                "about an article that was never in flight.")
        step = self.feed("cut", "--to-port {} --mode {} --group {} --msgid '{}' --pid {}"
                         .format(self.b.port, mode, GROUPS[0], INTERRUPTED_ID, self.b.pid),
                         name="kill -9 node B mid-{}".format(mode), timeout=180)
        self.facts["kill"] = "mode={} {}".format(mode, self.payload(step).get("after_kill", ""))
        self.b.rejected.append(INTERRUPTED_ID)
        self.sh("node B is gone", "kill -0 {} 2>/dev/null && echo ALIVE || echo GONE".format(
            self.b.pid or 0))
        survivor = self.sh("node A survived node B's death",
                           "kill -0 {} 2>/dev/null && echo ALIVE || echo DEAD".format(
                               self.a.pid or 0))
        if "ALIVE" not in survivor.output:
            self.gaps.append("node A did not survive node B's SIGKILL; the two nodes are "
                             "not independent processes in the way this gate assumed.")
        self.sh("node B recover after the kill",
                self.cd(self.fn("--store {} recover".format(self.b.store))), timeout=1800)
        self.sh("node B status after recovery",
                self.cd(self.fn("--store {} status".format(self.b.store))), timeout=1800)
        # The three outcomes again, this time as the recovery assertion: what B
        # acknowledged is accepted (0), the interrupted transfer is refused (1).
        for msgid in self.b.accepted:
            self.sh("node B still holds {} after recovery".format(msgid),
                    self.cd(self.fn("--store {} inspect --message-id '{}'".format(
                        self.b.store, msgid))), timeout=900, expect=EXIT_OK)
        self.sh("node B does not hold the interrupted {}".format(INTERRUPTED_ID),
                self.cd(self.fn("--store {} inspect --message-id '{}'".format(
                    self.b.store, INTERRUPTED_ID))), timeout=900, expect=EXIT_REFUSED)
        if not self.start_node(self.b, tag="after-recovery"):
            # B served before the kill; a B that will not come back is this
            # gate's subject failing, not an absent dependency.
            self.broke("reread node B after recovery", "feed.py presence",
                       "node B did not restart after the recovery: {}".format(
                           self.server_failure or "no symptom recorded"))
            return
        self.feed("presence", "--port {} --groups {} --present '{}' --absent '{}'".format(
            self.b.port, ",".join(GROUPS), ",".join(self.b.accepted),
            ",".join(self.b.rejected)),
            name="reread node B after recovery")
        # A must still hold exactly what it accepted, and must still not hold
        # what only B ever accepted: a feed in one direction is not a merge.
        only_b = [m for m in self.b.accepted if m not in self.a.accepted]
        self.feed("presence", "--port {} --groups {} --present '{}' --absent '{}'".format(
            self.a.port, ",".join(GROUPS), ",".join(self.a.accepted),
            ",".join(only_b + self.a.rejected)),
            name="node A is unchanged by node B's death")

    def scenario_tcpcl(self):
        """Two native images exchanging bundles over TCPCLv4 on loopback.

        The convergence layer lives in the ACL2 image, not in `bin/fn`, so
        this scenario needs `build/fn-host` on the box.  When the image does
        not build on this commit the scenario is skipped with the build's own
        last lines: a missing convergence layer is a finding, not a pass.

        Every assertion is over the event digests the images printed, and the
        images computed those with `fn-tcl-host-event-digests`; the lab does
        not know what a segment or an MRU is.  `tools/tcpcl_lab.py` holds the
        scenarios, so the same five run by hand on any box with an image.
        """
        build = self.sh("native image for the tcpcl layer",
                        self.cd("FN_ACL2=${FN_ACL2:-$HOME/fn-tools/acl2-8.7/saved_acl2} "
                                "nice -n 10 sh tools/build_native_host.sh"),
                        timeout=1800, expect=None)
        if not self.certificates_ok:
            # `tools/build_native_host.sh` refuses an uncertified book by
            # design, so a deploy tree with no certificates cannot produce an
            # image at all.  That is an absence of a dependency, not a broken
            # build, and it is the one case here that is not a failure.
            self.facts["tcpcl"] = "no image: the deploy tree holds no certificates"
            self.skip("tcpcl exchange", "tools/tcpcl_lab.py",
                      "the deploy tree holds no certificates, so "
                      "tools/build_native_host.sh cannot build an image: it "
                      "refuses to load an uncertified book")
            return
        if build.rc != 0 or "built build/fn-host" not in build.output:
            self.facts["tcpcl"] = "no image: the layer could not be exercised"
            self.gaps.append(
                "The native image did not build on this commit, so the TCPCLv4\n"
                "  convergence layer was not exercised at all. Its last lines were:\n"
                "  " + " | ".join(build.output.strip().splitlines()[-3:]))
            # The build script ran; it failed.  A build that fails is not
            # an absent convergence layer, it is a broken one, and the last
            # three lines of the build are in the gap above.
            self.broke("tcpcl exchange", "tools/tcpcl_lab.py",
                       "build/fn-host was not produced on this commit: "
                       + (build.first_line or "the build printed nothing"))
            return
        lab = self.sh("tcpcl lab (exchange, refused, keepalive, crash, "
                      "profile, replay)",
                      self.cd("python3 tools/tcpcl_lab.py --image build/fn-host "
                              "--work {}/tcpcl-lab".format(self.deploy)),
                      timeout=900, expect=None)
        rows = {}
        for line in lab.output.splitlines():
            line = line.strip()
            if line.startswith("{"):
                try:
                    row = json.loads(line)
                except ValueError:
                    continue
                rows[row.get("scenario", "?")] = row
        summary = rows.get("summary", {})
        self.facts["tcpcl"] = "passed={} failed={}".format(
            ",".join(summary.get("passed", [])) or "none",
            ",".join(summary.get("failed", [])) or "none")
        for name in ("exchange", "refused", "keepalive", "crash",
                     "profile", "replay"):
            row = rows.get(name)
            if row is None:
                self.broke("tcpcl {}".format(name), "tools/tcpcl_lab.py",
                           "the lab ran and produced no result for this "
                           "scenario, which is a silence, not an absence")
                continue
            note = ", ".join("{}={}".format(k, v) for k, v in sorted(row.items())
                             if k not in ("scenario", "ok"))
            # The lab's own exit code covers every scenario at once; each row
            # carries its own verdict, so each step gets that one.
            self.steps.append(Step("tcpcl {}".format(name), lab.command,
                                   0 if row.get("ok") else 1, lab.output, 0.0,
                                   note[:600], 0))
            if not row.get("ok"):
                self.gaps.append(
                    "The tcpcl `{}` scenario did not hold: {}".format(name, note[:300]))

    # -- evidence ---------------------------------------------------------
    def evidence(self, path, started, elapsed):
        """The deploy gate's evidence, with the tree-wide gaps said once.

        A gap that belongs to the tree rather than to a node (the shape of
        `bin/fn run`, say) is raised once per node by the phase that meets it.
        Saying it twice does not make it twice as true, and a per-node gap
        still names its node, so no gap is merged with a different one."""
        seen, unique = set(), []
        for gap in self.gaps:
            if gap not in seen:
                seen.add(gap)
                unique.append(gap)
        self.gaps = unique
        return super().evidence(path, started, elapsed)

    # -- the whole gate ---------------------------------------------------
    def execute(self):
        self.preflight()
        self.ship()
        self.push_file(FEED_DRIVER, "{}/feed.py".format(self.run), mode="755")
        self.push_file(TAP_DRIVER, "{}/tap.py".format(self.run), mode="755")
        self.certificates()
        for node in self.nodes:
            self.init_node(node)
        self.three_outcomes_node(self.a, ARTICLE_A, "alpha, written on A")
        self.three_outcomes_node(self.b, ARTICLE_B, "beta, written on B")
        for node in self.nodes:
            if not self.start_node(node):
                raise GateError("node {} did not reach LISTENING".format(node.upper))
        if self.a.port == self.b.port:
            raise GateError("both nodes reported the same port; they are one server")
        for node in self.nodes:
            self.start_tap(node)
        self.configure_peering(streaming=False)
        self.scenario_independent()
        self.scenario_feed()
        self.scenario_owner_feed()
        self.scenario_owner_feed_streaming()
        self.scenario_feed_restart()
        self.scenario_feed_peer_cut()
        self.scenario_kill()
        self.scenario_tcpcl()
        for node in self.nodes:
            self.sh("node {} log tail".format(node.upper),
                    "tail -12 {}/server-{}-main.log".format(node.dir, node.name))

    def cleanup(self):
        """No stray process and no tree left on the box, whatever went wrong."""
        for node in self.nodes:
            self.stop_node(node)
            self.sh("stop the tap in front of node {}".format(node.upper), """
if [ -f {dir}/tap.pid ]; then
  pid=$(cat {dir}/tap.pid)
  kill $pid 2>/dev/null || true
  for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done
  kill -9 $pid 2>/dev/null || true
  rm -f {dir}/tap.pid
fi
echo stopped
""".format(dir=node.dir), expect=None)
        self.sh("stray fn processes", "pgrep -f 'fn-deploy/{}' >/dev/null 2>&1 "
                "&& echo STRAY || echo CLEAN".format(self.rev), expect=None)
        if not self.keep:
            self.sh("remove the deploy tree", "rm -rf {}".format(self.deploy))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("commit", help="the commit-ish to deploy on both nodes")
    parser.add_argument("--host", default=DEFAULT_HOST)
    parser.add_argument("--tree", default="dev", help="gate directory prefix on the host")
    parser.add_argument("--repo", default=None,
                        help="the fn worktree to read the commit from and "
                             "write evidence into (default: the one this "
                             "command was invoked from)")
    parser.add_argument("--jobs", type=int, default=16)
    parser.add_argument("--evidence", default=None)
    parser.add_argument("--keep", action="store_true",
                        help="leave the deploy tree on the host")
    parser.add_argument("--dry-run", action="store_true",
                        help="run every script through local bash with HOME redirected")
    parser.add_argument("--home", default=None, help="the fake HOME for --dry-run")
    parser.add_argument("--acl2", default=None,
                        help="the host's ACL2 image; the default is tools/farm.py's entry")
    parser.add_argument("--overlay", action="append", default=[],
                        help="a directory copied over the deployed tree before it runs; "
                             "repeatable, applied in order")
    parser.add_argument("--server-command", default=None,
                        help="the server entry point, with {store}, {run} and {node}; "
                             "the default is the deploy gate's selection")
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
    gate = TwoNodeGate(host, repo, commit, rev, args.tree,
                       overlay=overlays[0] if overlays else None,
                       jobs=args.jobs, keep=args.keep, nntplib_python="none",
                       acl2=args.acl2 or deploy_gate.FARM_HOSTS.get(
                           args.host, {}).get("acl2", "acl2"),
                       server_template=args.server_command,
                       extra_overlays=overlays[1:])
    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    failure = None
    try:
        gate.execute()
    except GateError as error:
        failure = str(error)
        gate.gaps.append("the gate stopped early: {}".format(error))
    finally:
        try:
            gate.cleanup()
        except Exception as error:      # cleanup must never hide the result
            gate.gaps.append("cleanup did not finish: {}: {}".format(
                type(error).__name__, error))
    elapsed = time.monotonic() - clock
    date = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
    target = evidence_path(args.evidence, repo,
                           "twonode-{}-{}.md".format(rev, date))
    gate.evidence(target, started, elapsed)
    print("evidence: {}".format(target))
    bad = [s for s in gate.steps if s.failed]
    print("steps={} failed={} not-exercised={}".format(
        len(gate.steps), len(bad), sum(1 for s in gate.steps if s.rc is None)))
    for step in bad:
        print("  FAILED rc={} {}: {}".format(step.rc, step.name, step.first_line))
    if failure:
        print("gate error: {}".format(failure))
        return 2
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

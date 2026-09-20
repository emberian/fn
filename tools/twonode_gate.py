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
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

import deploy_gate                                            # noqa: E402
from deploy_gate import (DEFAULT_HOST, EXIT_OK, EXIT_REFUSED,  # noqa: E402
                         EXIT_UNCERTAIN, GROUPS, GateError, Host, LocalHost,
                         SshHost, Step, resolve)

# One article per node, plus the two the transit scenario needs.
ARTICLE_A = "<alpha@a.example.invalid>"
ARTICLE_B = "<beta@b.example.invalid>"
LOOP_ID = "<loop@a.example.invalid>"
INTERRUPTED_ID = "<interrupted@example.invalid>"
ABSENT_ID = "<absent@example.invalid>"


def article(msgid: str, group: str, subject: str, body: str, path: str = "") -> bytes:
    """An article as octets, CRLF, the shape tools/run_store.py post takes."""
    headers = ["Path: {}!not-for-mail".format(path)] if path else []
    headers += ["From: gate@example.invalid",
                "Subject: {}".format(subject),
                "Newsgroups: {}".format(group),
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


def presence(args):
    """Every msgid in --present must be served; every one in --absent must not."""
    conn = Conn(args.port)
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
            "Message-ID: " + args.loop_msgid, "",
            "This article already names the target node in its Path."]
    out["loop_offer"] = conn.cmd("IHAVE " + args.loop_msgid)[0]
    if out["loop_offer"].startswith("335"):
        send_block(conn, loop)
        out["loop_result"] = conn.line()
    else:
        out["loop_result"] = out["loop_offer"]
    conn.close()

    status, got = fetch(args.to_port, args.msgid)
    out["reread"] = status
    out["identical"] = (got == lines)
    out["loop_absent"] = fetch(args.to_port, args.loop_msgid)[0]
    out["ok"] = (out["transfer"].startswith("235")
                 and out["duplicate"].startswith("435")
                 and not out["loop_result"].startswith("2")
                 and out["reread"].startswith("220")
                 and out["identical"]
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
    for name in ("presence", "relay", "cut"):
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
    args = parser.parse_args()
    handler = {"presence": presence, "relay": relay, "cut": cut}[args.phase]
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
                 "three outcomes b", "transit", "feed", "kill")
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
        "No BP/DTN transport, no third node, no concurrent load, no RFC conformance\n"
        "  audit: the assertions are this driver's, not a spec's.",
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

    def start_node(self, node: NodeSpec, tag="main") -> bool:
        if node.name not in self.commands:
            if self.server_template:
                self.commands[node.name] = ("custom", self.server_template.format(
                    store=node.store, run=node.dir, node=node.name))
            else:
                self.commands[node.name] = self.server_command(node.store, node.dir)
        self.selected, command = self.commands[node.name]
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
            started = self.start_server("node {} (reader)".format(node.upper), fallback,
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

    def peer_records(self):
        """A peer record on each node naming the other (specs/peering.md 1.2)."""
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
            if kind == "STORE-PEER":
                self.sh("node {} peer record for {}".format(node.upper, other.upper),
                        self.cd(self.fn(
                            "--store {} peer set --name {} --path-identity {} "
                            "--nntp 127.0.0.1:{} --inbound-groups 'fn.*' "
                            "--outbound-groups 'fn.*'".format(
                                node.store, other.name, other.path_identity, other.port))),
                        timeout=900)
                continue
            if kind == "FN-PEER":
                self.sh("node {} peer record for {}".format(node.upper, other.upper),
                        self.cd("./bin/fn peer set {} 127.0.0.1:{} {}".format(
                            other.name, other.port, other.path_identity)), timeout=900)
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
        alive = self.sh("both servers are still up", "; ".join(
            "kill -0 {pid} 2>/dev/null && echo {name}=ALIVE || echo {name}=DEAD".format(
                pid=node.pid or 0, name=node.upper) for node in self.nodes))
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
                              "loop={loop} reread={reread} identical={identical}".format(
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
        if str(result.get("loop_result", "")).startswith("2"):
            self.gaps.append(
                "an article whose Path already names B was ACCEPTED by B ('{}'): the "
                "loop suppression of RFC 5537 3.5 is not in place."
                .format(result.get("loop_result")))
        self.b.rejected.append(LOOP_ID)

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
            self.skip("reread node B after recovery", "feed.py presence",
                      "node B did not restart after the recovery")
            return
        self.feed("presence", "--port {} --groups {} --present '{}' --absent '{}'".format(
            self.b.port, ",".join(GROUPS), ",".join(self.b.accepted),
            ",".join(self.b.rejected)),
            name="reread node B after recovery")
        self.feed("presence", "--port {} --groups {} --present '{}' --absent '{}'".format(
            self.a.port, ",".join(GROUPS), ",".join(self.a.accepted),
            ",".join(self.a.rejected)),
            name="node A is unchanged by node B's death")

    # -- the whole gate ---------------------------------------------------
    def execute(self):
        self.preflight()
        self.ship()
        self.push_file(FEED_DRIVER, "{}/feed.py".format(self.run), mode="755")
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
        self.peer_records()
        self.scenario_independent()
        self.scenario_feed()
        self.scenario_kill()
        for node in self.nodes:
            self.sh("node {} log tail".format(node.upper),
                    "tail -12 {}/server-{}-main.log".format(node.dir, node.name))

    def cleanup(self):
        """No stray process and no tree left on the box, whatever went wrong."""
        for node in self.nodes:
            self.stop_node(node)
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
    parser.add_argument("--repo", default=str(ROOT))
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

    repo = Path(args.repo).resolve()
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
    target = Path(args.evidence) if args.evidence else (
        repo / "planning/evidence/twonode-{}-{}.md".format(rev, date))
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

#!/usr/bin/env python3
"""Drive one deployed fn node from another machine: STARTTLS, login, post, reread.

The deploy gate and the v0 matrix exercise a node on the box that built it.
This is the other witness: a node that is already running somewhere, reached
over the network by an independent client that fn does not control, with the
policy an off-loopback node must carry (RFC 4642 STARTTLS, RFC 4643 AUTHINFO
answered 483 until the layer is up).  Every exchange is recorded as the status
line the node actually sent, and the verdict on each assertion is one of

    held        decided, and the node did what the assertion says
    violated    decided, and it did not
    undecided   not decided: an earlier step failed, so this one never ran

The process exit keeps those apart the way the deploy gate does: 0 when every
assertion was decided and held, 1 when one was decided and violated, 3 when
nothing was violated but something the run meant to decide it could not, 2 for
a usage error.  A probe that could not connect exits 3, never 0.

    FN_PROBE_USER=ember FN_PROBE_PASSWORD=... \\
      python3 tools/node_probe.py 192.168.50.39 1119 --cafile cert.pem --group fn.agents

The password comes from the environment only.  It is never an argument (ps
would show it), never written to the transcript, the JSON or stdout.  The CA
file is the node's own certificate (a self-signed pair is what the hbox
runbook writes); the handshake verifies the chain and the name or address
against it, so a wrong or missing file is a violated handshake, not a warning.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import platform
import secrets
import ssl
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from nntp_session import Disconnected, Session      # noqa: E402  one socket half

HELD, VIOLATED, UNDECIDED = "held", "violated", "undecided"


class Probe:
    def __init__(self, args, user: str, password: str):
        self.args = args
        self.user, self.password = user, password
        self.steps: list[dict] = []
        self.context = ssl.create_default_context(cafile=args.cafile)
        self.msgid = "<node-probe.%s.%s@probe.invalid>" % (
            dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ"), secrets.token_hex(4))
        self.tls_info = None

    def record(self, name: str, expected: str, observed, verdict: str, note: str = "") -> bool:
        self.steps.append({"step": name, "expected": expected, "observed": observed,
                           "verdict": verdict, "note": note})
        return verdict == HELD

    def check(self, name: str, expected_code: str, status: str, note: str = "") -> bool:
        verdict = HELD if status.startswith(expected_code + " ") or status == expected_code else VIOLATED
        return self.record(name, expected_code, status, verdict, note)

    def undecided_after(self, names: list[str], reason: str) -> None:
        for name in names:
            self.record(name, "", None, UNDECIDED, reason)

    # The assertions, in the order a client meets them.
    PROTECTED = ["greeting", "capabilities-offer-starttls", "authinfo-before-tls-refused",
                 "starttls", "capabilities-withdraw-starttls", "login"]
    POSTING = ["group", "post", "reread-fresh-connection"]

    def open_protected(self, phase: str) -> Session | None:
        names = [phase + ":" + n for n in self.PROTECTED]
        try:
            session = Session(self.args.host, self.args.port, self.args.timeout)
        except (OSError, Disconnected) as exc:
            # The greeting is read inside the constructor, so a node that
            # accepts and then closes -- a stopped owner behind an `ssh -L`
            # forwarder -- arrives here as `Disconnected`.  Undecided, not a
            # traceback: this probe's exit is a gate.
            self.undecided_after(names, "connect: %s" % exc)
            return None
        try:
            ok = self.check(names[0], "200", session.greeting)
            status, caps = session.cmd("CAPABILITIES", multiline=True)
            labels = {c.split()[0].upper() for c in caps if c.strip()}
            ok &= self.record(names[1], "STARTTLS in CAPABILITIES", caps,
                              HELD if "STARTTLS" in labels else VIOLATED)
            status = session.cmd("AUTHINFO USER " + self.user)[0]
            ok &= self.check(names[2], "483", status, "RFC 4643 section 2.3.2")
            if status.startswith("381"):
                # The node asked for the password in the clear.  Do not send it.
                session.close()
                self.undecided_after(names[3:], "the node would take the password in the clear")
                return None
            try:
                status = session.starttls(self.context)
                ok &= self.check(names[3], "382", status)
            except ssl.SSLError as exc:
                self.record(names[3], "382 and a verified handshake", str(exc), VIOLATED)
                session.sock.close()
                self.undecided_after(names[4:], "handshake failed")
                return None
            if session.tls is None:
                session.close()
                self.undecided_after(names[4:], "no TLS layer")
                return None
            self.tls_info = session.tls
            status, caps = session.cmd("CAPABILITIES", multiline=True)
            labels = {c.split()[0].upper() for c in caps if c.strip()}
            ok &= self.record(names[4], "STARTTLS withdrawn, AUTHINFO offered", caps,
                              HELD if "STARTTLS" not in labels and "AUTHINFO" in labels else VIOLATED,
                              "RFC 4642 section 2.2.2, RFC 4643 section 2.1")
            status = session.login(self.user, self.password)
            if not self.check(names[5], "281", status):
                session.close()
                return None
            return session
        except (OSError, Disconnected) as exc:
            done = {s["step"] for s in self.steps}
            self.undecided_after([n for n in names if n not in done], str(exc))
            try:
                session.sock.close()
            except OSError:
                pass
            return None

    def run(self) -> int:
        session = self.open_protected("first")
        posting = [n for n in self.POSTING]
        if session is None:
            self.undecided_after(posting, "no authenticated connection")
            return self.exit_code()
        try:
            status = session.cmd("GROUP " + self.args.group)[0]
            if not self.check("group", "211", status):
                session.close()
                self.undecided_after(posting[1:], "group not served")
                return self.exit_code()
            if self.args.no_post:
                session.close()
                self.undecided_after(posting[1:], "--no-post")
                return self.exit_code()
            status = session.cmd("POST")[0]
            if not status.startswith("340"):
                self.check("post", "340 then 240", status)
                session.close()
                self.undecided_after(posting[2:], "post refused")
                return self.exit_code()
            for line in self.article():
                session.send(("." + line) if line.startswith(".") else line)
            session.send(".")
            status = session.line()
            if not self.check("post", "240", status, "message-id " + self.msgid):
                session.close()
                self.undecided_after(posting[2:], "post not accepted")
                return self.exit_code()
            session.close()
        except (OSError, Disconnected) as exc:
            done = {s["step"] for s in self.steps}
            self.undecided_after([n for n in posting if n not in done], str(exc))
            return self.exit_code()
        # The posting connection stays pinned at the version it opened with;
        # a fresh connection sees the version the post advanced to.
        second = self.open_protected("second")
        if second is None:
            self.undecided_after(["reread-fresh-connection"], "no second authenticated connection")
            return self.exit_code()
        try:
            second.cmd("GROUP " + self.args.group)
            status, lines = second.cmd("ARTICLE " + self.msgid, multiline=True)
            marker = self.marker() in "\n".join(lines)
            self.record("reread-fresh-connection", "220 and the posted body", status,
                        HELD if status.startswith("220") and marker else VIOLATED,
                        "body marker %s" % ("found" if marker else "missing"))
        except (OSError, Disconnected) as exc:
            self.undecided_after(["reread-fresh-connection"], str(exc))
        finally:
            second.close()
        return self.exit_code()

    def marker(self) -> str:
        return "node probe %s" % self.msgid

    def article(self) -> list[str]:
        return ["From: %s <%s@probe.invalid>" % (self.user, self.user),
                "Subject: node probe from %s" % platform.node(),
                "Newsgroups: " + self.args.group,
                "Message-ID: " + self.msgid,
                "",
                self.marker(),
                "Sent by tools/node_probe.py at %s." % dt.datetime.now(dt.timezone.utc).isoformat()]

    def exit_code(self) -> int:
        verdicts = {s["verdict"] for s in self.steps}
        if VIOLATED in verdicts:
            return 1
        if UNDECIDED in verdicts:
            return 3
        return 0

    def summary(self) -> dict:
        return {"host": self.args.host, "port": self.args.port, "group": self.args.group,
                "login": self.user, "message_id": self.msgid, "tls": self.tls_info,
                "client": "tools/node_probe.py on %s, Python %s" % (platform.node(), platform.python_version()),
                "when": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
                "steps": self.steps, "exit": self.exit_code()}


def render(summary: dict) -> str:
    out = ["node probe %s:%d as %s" % (summary["host"], summary["port"], summary["login"])]
    for step in summary["steps"]:
        observed = step["observed"]
        if isinstance(observed, list):
            observed = " ".join(observed)
        observed = (observed or "").strip() if isinstance(observed, str) else ""
        line = "  %-9s %-40s %s" % (step["verdict"], step["step"], observed[:100])
        if step["note"]:
            line += "   (%s)" % step["note"]
        out.append(line)
    if summary["tls"]:
        out.append("  tls %s %s" % (summary["tls"]["version"], summary["tls"]["cipher"]))
    out.append("  exit %d" % summary["exit"])
    return "\n".join(out)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("host", help="the listener address as the node binds it")
    parser.add_argument("port", type=int)
    parser.add_argument("--cafile", required=True, help="the node's certificate, or its CA")
    parser.add_argument("--group", default="fn.test")
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--no-post", action="store_true", help="stop after GROUP")
    parser.add_argument("--json", default=None, help="write the recorded steps here")
    args = parser.parse_args(argv)
    user = os.environ.get("FN_PROBE_USER", "")
    password = os.environ.get("FN_PROBE_PASSWORD", "")
    if not user or not password:
        parser.error("FN_PROBE_USER and FN_PROBE_PASSWORD must be set in the environment")
    if not os.path.isfile(args.cafile):
        parser.error("--cafile %s is not a file" % args.cafile)
    probe = Probe(args, user, password)
    code = probe.run()
    summary = probe.summary()
    text = json.dumps(summary, indent=1)
    if password in text:
        raise SystemExit("refusing to write a record that contains the password")
    if args.json:
        with open(args.json, "w") as handle:
            handle.write(text + "\n")
    print(render(summary))
    return code


if __name__ == "__main__":
    sys.exit(main())

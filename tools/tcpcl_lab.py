#!/usr/bin/env python3
"""Two fn native hosts exchanging bundles over TCPCLv4 on loopback.

Everything protocol here is the image's: this file starts two processes, reads
their session logs, and asserts over the event digests ACL2 produced.  It
computes no length, no MRU and no reason code, and it never speaks TCPCL --
the only socket in the lab belongs to the two images.

    python3 tools/tcpcl_lab.py --image build/fn-host --work /tmp/tcpcl-lab

Scenarios, each printing one JSON object and each independent of the others:

`exchange`   contact, SESS_INIT, one two-segment transfer each way, SESS_TERM.
             The listener answers with its own bundle, so both directions run
             inside one session, and both spools must hold the peer's octets.
`refused`    the listener advertises a transfer MRU below the bundle's length.
             `fn-tcl-send' refuses before a segment is written; exit code 1.
`keepalive`  an idle established session: KEEPALIVE flows both ways on the
             negotiated interval and neither side times the other out.
`crash`      SIGKILL the listener inside a transfer, then start a fresh one.
             The bundle it acknowledged before the kill is still in the spool,
             byte for byte; the one that was in flight is not there at all.
`replay`     the trace the listener wrote, folded back through `fn-tcl-drive'
             by the image's own `tcpcl replay' verb.  The two event streams
             must be equal: the socket loop decided nothing the fold did not.

`--scenario all` runs them in that order and prints one object per scenario
plus a summary.  The exit code is 0 when every scenario passed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

LISTENING = re.compile(rb"TCPCL LISTENING (\d+)")
EVENT = re.compile(r"^TCPCL (\S+) (event|aux) (.*)$")
OUTCOME = re.compile(r"^TCPCL (\S+) (accepted|refused|uncertain) (.*)$")

EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN = 0, 1, 3


def bundle(length: int, seed: int) -> bytes:
    """Deterministic octets of an exact length; not a BPv7 bundle.

    TCPCLv4 carries a transfer of opaque octets (RFC 9174 section 5.2): the
    convergence layer neither parses nor bounds the bundle it carries, so the
    payload here is a byte pattern and the lab asserts on its octets.  A real
    BPv7 bundle is the BP node's business, not this layer's.
    """
    out = bytearray()
    while len(out) < length:
        out += hashlib.sha256(bytes([seed]) + len(out).to_bytes(8, "big")).digest()
    return bytes(out[:length])


class Lab:
    def __init__(self, image: str, work: str):
        self.image = str(Path(image).resolve())
        self.work = Path(work)
        self.results = []

    # -- plumbing ---------------------------------------------------------
    def fresh(self, name: str) -> Path:
        path = self.work / name
        if path.exists():
            shutil.rmtree(path)
        path.mkdir(parents=True)
        return path

    def spawn(self, args, log: Path):
        handle = open(log, "wb")
        process = subprocess.Popen([self.image, "--fn"] + [str(a) for a in args],
                                   stdout=handle, stderr=subprocess.STDOUT)
        process.log = log                                      # type: ignore
        process.handle = handle                                # type: ignore
        return process

    @staticmethod
    def port_of(process, timeout=20.0) -> int:
        deadline = time.time() + timeout
        while time.time() < deadline:
            match = LISTENING.search(Path(process.log).read_bytes())
            if match:
                return int(match.group(1))
            if process.poll() is not None:
                raise RuntimeError("listener exited before it listened: {}".format(
                    Path(process.log).read_text(errors="replace")[:600]))
            time.sleep(0.05)
        raise RuntimeError("listener never announced a port")

    @staticmethod
    def events(log: Path, tag=None, source="event"):
        out = []
        for line in Path(log).read_text(errors="replace").splitlines():
            match = EVENT.match(line)
            if match and (tag is None or match.group(1) == tag) \
                    and (source is None or match.group(2) == source):
                out.append(match.group(3))
        return out

    @staticmethod
    def outcomes(log: Path):
        return [(m.group(2), m.group(3))
                for m in (OUTCOME.match(l) for l in
                          Path(log).read_text(errors="replace").splitlines()) if m]

    @staticmethod
    def kinds(events, kind: str) -> int:
        return sum(1 for e in events if e.startswith("(:SEND {} ".format(kind)))

    def record(self, name: str, ok: bool, **facts):
        row = dict(scenario=name, ok=bool(ok), **facts)
        self.results.append(row)
        print(json.dumps(row, sort_keys=True), flush=True)
        return row

    # -- scenarios --------------------------------------------------------
    def scenario_exchange(self):
        """One session, one two-segment transfer each way, terminated cleanly."""
        root = self.fresh("exchange")
        a_spool, b_spool = root / "passive-spool", root / "active-spool"
        to_b = root / "to-b.bundle"
        to_a = root / "to-a.bundle"
        to_b.write_bytes(bundle(1500, 1))
        to_a.write_bytes(bundle(1500, 2))
        trace = root / "passive.trace"
        listener = self.spawn(
            ["tcpcl", "listen", 0, 1, a_spool, "dtn://fn-b/", "-", 4, 1024, 1048576,
             to_a, trace], root / "listen.log")
        try:
            port = self.port_of(listener)
            sender = subprocess.run(
                [self.image, "--fn", "tcpcl", "send", "127.0.0.1", str(port), str(to_b),
                 str(b_spool), "dtn://fn-a/", "-", "4", "1024", "1048576", "1", "-"],
                capture_output=True, timeout=120)
            send_log = root / "send.log"
            send_log.write_bytes(sender.stdout + sender.stderr)
            listener.wait(timeout=60)
        finally:
            if listener.poll() is None:
                listener.kill()
            listener.handle.close()

        passive = self.events(root / "listen.log", "passive")
        active = self.events(send_log, "active")
        p_all = self.events(root / "listen.log", "passive", source=None)
        a_all = self.events(send_log, "active", source=None)
        got_b = a_spool / "passive-0.bundle"
        got_a = b_spool / "active-0.bundle"
        facts = dict(
            listener_rc=listener.returncode, sender_rc=sender.returncode,
            passive_events=len(passive), active_events=len(active),
            contact=self.kinds(p_all, ":CONTACT") and self.kinds(a_all, ":CONTACT"),
            sess_init=self.kinds(p_all, ":SESS-INIT") and self.kinds(a_all, ":SESS-INIT"),
            segments_to_b=self.kinds(a_all, ":XFER-SEGMENT"),
            segments_to_a=self.kinds(p_all, ":XFER-SEGMENT"),
            acks_from_b=self.kinds(p_all, ":XFER-ACK"),
            acks_from_a=self.kinds(a_all, ":XFER-ACK"),
            sess_term=self.kinds(a_all, ":SESS-TERM") and self.kinds(p_all, ":SESS-TERM"),
            b_holds_a_bundle=got_b.exists() and got_b.read_bytes() == to_b.read_bytes(),
            a_holds_b_bundle=got_a.exists() and got_a.read_bytes() == to_a.read_bytes(),
            passive_outcomes=self.outcomes(root / "listen.log"),
            active_outcomes=self.outcomes(send_log),
            trace_bytes=trace.stat().st_size if trace.exists() else 0)
        ok = (facts["listener_rc"] == EXIT_OK and facts["sender_rc"] == EXIT_OK
              and facts["contact"] and facts["sess_init"] and facts["sess_term"]
              and facts["segments_to_b"] == 2 and facts["segments_to_a"] == 2
              and facts["acks_from_b"] == 2 and facts["acks_from_a"] == 2
              and facts["b_holds_a_bundle"] and facts["a_holds_b_bundle"])
        self.record("exchange", ok, **facts)
        return root, trace

    def scenario_refused(self):
        """A transfer the peer's MRU cannot hold: refused, and no segment sent."""
        root = self.fresh("refused")
        payload = root / "big.bundle"
        payload.write_bytes(bundle(4096, 3))
        listener = self.spawn(
            ["tcpcl", "listen", 0, 1, root / "passive-spool", "dtn://fn-b/", "-",
             4, 1024, 512, "-", "-"], root / "listen.log")
        try:
            port = self.port_of(listener)
            sender = subprocess.run(
                [self.image, "--fn", "tcpcl", "send", "127.0.0.1", str(port),
                 str(payload), str(root / "active-spool"), "dtn://fn-a/", "-",
                 "4", "1024", "1048576", "0", "-"],
                capture_output=True, timeout=120)
            (root / "send.log").write_bytes(sender.stdout + sender.stderr)
            listener.wait(timeout=60)
        finally:
            if listener.poll() is None:
                listener.kill()
            listener.handle.close()
        active = self.events(root / "send.log", "active", source=None)
        outcomes = self.outcomes(root / "send.log")
        facts = dict(sender_rc=sender.returncode,
                     segments=self.kinds(active, ":XFER-SEGMENT"),
                     outcomes=outcomes,
                     staged=sorted(p.name for p in (root / "passive-spool").glob("*")))
        ok = (facts["sender_rc"] == EXIT_REFUSED and facts["segments"] == 0
              and any(kind == "refused" and "exceeds-transfer-mtu" in text
                      for kind, text in outcomes)
              and facts["staged"] == [])
        self.record("refused", ok, **facts)

    def scenario_keepalive(self):
        """An idle established session: KEEPALIVE on the negotiated interval."""
        root = self.fresh("keepalive")
        listener = self.spawn(
            ["tcpcl", "listen", 0, 1, root / "passive-spool", "dtn://fn-b/", "-",
             2, 1024, 1048576, "-", "-"], root / "listen.log")
        sender = None
        try:
            port = self.port_of(listener)
            # The active side expects a bundle that never comes, so it holds the
            # session open; both sides then have nothing to say but keepalives.
            sender = self.spawn(
                ["tcpcl", "send", "127.0.0.1", port, "-",
                 root / "active-spool", "dtn://fn-a/", "-", 2, 1024, 1048576, 1, "-"],
                root / "send.log")
            time.sleep(7.0)
            passive = self.events(root / "listen.log", "passive", source=None)
            active = self.events(root / "send.log", "active", source=None)
            facts = dict(passive_keepalives=self.kinds(passive, ":KEEPALIVE"),
                         active_keepalives=self.kinds(active, ":KEEPALIVE"),
                         passive_terms=self.kinds(passive, ":SESS-TERM"),
                         active_terms=self.kinds(active, ":SESS-TERM"),
                         still_up=(listener.poll() is None and sender.poll() is None))
            ok = (facts["passive_keepalives"] >= 2 and facts["active_keepalives"] >= 2
                  and facts["passive_terms"] == 0 and facts["active_terms"] == 0
                  and facts["still_up"])
            self.record("keepalive", ok, **facts)
        finally:
            for process in (listener, sender):
                if process is not None:
                    if process.poll() is None:
                        process.kill()
                    process.handle.close()

    def scenario_crash(self):
        """SIGKILL the receiver mid-transfer; what it acknowledged survives."""
        root = self.fresh("crash")
        spool = root / "passive-spool"
        small = root / "small.bundle"
        big = root / "big.bundle"
        small.write_bytes(bundle(900, 4))
        # Large enough that the kill lands between segments and small enough
        # that the run finishes: `fn-tcl-drive`'s guard is `fn-tcl-sessionp`,
        # a whole-session recognizer whose `fn-tcl-octet-listsp` walks every
        # octet staged so far, so a transfer of n octets costs O(n^2/chunk) in
        # guard checking alone.  That is the books' served path, not this
        # lab's; see the evidence record.
        big.write_bytes(bundle(120000, 5))

        # First, a transfer that completes and is acknowledged.
        first = self.spawn(["tcpcl", "listen", 0, 1, spool, "dtn://fn-b/", "-",
                            4, 1024, 1048576, "-", "-"], root / "listen-1.log")
        try:
            port = self.port_of(first)
            done = subprocess.run(
                [self.image, "--fn", "tcpcl", "send", "127.0.0.1", str(port), str(small),
                 str(root / "active-spool"), "dtn://fn-a/", "-", "4", "1024",
                 "1048576", "0", "-"], capture_output=True, timeout=120)
            first.wait(timeout=60)
        finally:
            if first.poll() is None:
                first.kill()
            first.handle.close()
        acknowledged = spool / "passive-0.bundle"
        durable_before = acknowledged.exists() and acknowledged.read_bytes() == small.read_bytes()

        # Then a transfer that is cut: the receiver dies between segments.
        second = self.spawn(["tcpcl", "listen", 0, 1, spool, "dtn://fn-b/", "-",
                             4, 1024, 1048576, "-", "-"], root / "listen-2.log")
        sender = None
        killed_after = 0
        try:
            port = self.port_of(second)
            sender = self.spawn(["tcpcl", "send", "127.0.0.1", port, big,
                                 root / "active-spool", "dtn://fn-a/", "-", 4, 1024,
                                 1048576, 0, "-"], root / "send-2.log")
            deadline = time.time() + 30
            while time.time() < deadline:
                seen = self.kinds(self.events(root / "listen-2.log", "passive",
                                              source=None), ":XFER-ACK")
                if seen >= 3:
                    killed_after = seen
                    break
                if second.poll() is not None:
                    break
                time.sleep(0.02)
            os.kill(second.pid, signal.SIGKILL)
            second.wait(timeout=30)
        finally:
            for process in (second, sender):
                if process is not None:
                    if process.poll() is None:
                        process.kill()
                    process.handle.close()

        # A fresh receiver on the same spool: the interrupted transfer is not
        # there, the acknowledged one still is, and a new transfer still lands.
        third = self.spawn(["tcpcl", "listen", 0, 1, spool, "dtn://fn-b/", "-",
                            4, 1024, 1048576, "-", "-"], root / "listen-3.log")
        try:
            port = self.port_of(third)
            again = subprocess.run(
                [self.image, "--fn", "tcpcl", "send", "127.0.0.1", str(port), str(small),
                 str(root / "active-spool"), "dtn://fn-a/", "-", "4", "1024",
                 "1048576", "0", "-"], capture_output=True, timeout=120)
            third.wait(timeout=60)
        finally:
            if third.poll() is None:
                third.kill()
            third.handle.close()

        staged = sorted(p.name for p in spool.glob("*"))
        big_digest = hashlib.sha256(big.read_bytes()).hexdigest()
        holds_big = any(hashlib.sha256((spool / n).read_bytes()).hexdigest() == big_digest
                        for n in staged)
        facts = dict(first_rc=done.returncode, reconnect_rc=again.returncode,
                     acks_before_kill=killed_after,
                     durable_before=durable_before,
                     durable_after=(acknowledged.exists()
                                    and acknowledged.read_bytes() == small.read_bytes()),
                     interrupted_absent=not holds_big,
                     no_partials=[n for n in staged if n.startswith(".")] == [],
                     staged=staged)
        ok = (facts["first_rc"] == EXIT_OK and facts["reconnect_rc"] == EXIT_OK
              and facts["acks_before_kill"] >= 3 and facts["durable_before"]
              and facts["durable_after"] and facts["interrupted_absent"]
              and facts["no_partials"])
        self.record("crash", ok, **facts)

    def scenario_replay(self, root: Path, trace: Path):
        """The listener's octets, folded back through `fn-tcl-drive' alone."""
        if not trace.exists():
            return self.record("replay", False, reason="no trace from `exchange'")
        replayed = subprocess.run(
            [self.image, "--fn", "tcpcl", "replay", str(trace), "passive",
             "dtn://fn-b/", "-", "4", "1024", "1048576"],
            capture_output=True, timeout=300)
        out = (root / "replay.log")
        out.write_bytes(replayed.stdout + replayed.stderr)
        model = [line.split(" ", 3)[3] for line in
                 out.read_text(errors="replace").splitlines()
                 if line.startswith("TCPCL replay event ")]
        loop = self.events(root / "listen.log", "passive")
        facts = dict(rc=replayed.returncode, loop_events=len(loop),
                     model_events=len(model), equal=(loop == model))
        if loop != model:
            facts["first_difference"] = next(
                ("{!r} != {!r}".format(a, b) for a, b in zip(loop, model) if a != b),
                "lengths differ")
        self.record("replay", facts["rc"] == EXIT_OK and facts["equal"], **facts)

    # -- the whole lab ----------------------------------------------------
    def run(self, which: str) -> int:
        self.work.mkdir(parents=True, exist_ok=True)
        root, trace = (None, None)
        if which in ("all", "exchange", "replay"):
            root, trace = self.scenario_exchange()
        if which in ("all", "refused"):
            self.scenario_refused()
        if which in ("all", "keepalive"):
            self.scenario_keepalive()
        if which in ("all", "crash"):
            self.scenario_crash()
        if which in ("all", "replay"):
            self.scenario_replay(root, trace)
        summary = dict(scenario="summary",
                       passed=[r["scenario"] for r in self.results if r["ok"]],
                       failed=[r["scenario"] for r in self.results if not r["ok"]])
        summary["ok"] = not summary["failed"]
        print(json.dumps(summary, sort_keys=True), flush=True)
        return 0 if summary["ok"] else 1


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--image", default="build/fn-host")
    parser.add_argument("--work", default="/tmp/tcpcl-lab")
    parser.add_argument("--scenario", default="all",
                        choices=["all", "exchange", "refused", "keepalive",
                                 "crash", "replay"])
    args = parser.parse_args(argv)
    if not Path(args.image).exists():
        print(json.dumps({"scenario": "summary", "ok": False,
                          "reason": "no image at {}".format(args.image)}))
        return 2
    return Lab(args.image, args.work).run(args.scenario)


if __name__ == "__main__":
    sys.exit(main())

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
`adu`        the BP node, not the convergence layer: A authors a whole BPv7
             bundle with `bp send' and B decodes it with `bp receive'.  The
             ADU B journals must be A's ADU byte for byte, and B's reply
             bundle must arrive at A the same way.  Nothing in this scenario
             hands either side octets it did not author.
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

sys.path.insert(0, str(Path(__file__).resolve().parent))
from deploy_gate import repo_root                              # noqa: E402

LISTENING = re.compile(rb"(?:TCPCL|BP) LISTENING (\d+)")
BP_ACCEPTED = re.compile(r"^BP accepted xfer=(\d+) adu=(\d+) path=(.*)$")
BP_AUTHORED = re.compile(r"^BP authored creation=(\d+) sequence=(\d+) "
                         r"lifetime=(\d+) payload=(\d+) octets=(\d+)$")
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

    def spawn(self, args, log: Path, env=None):
        handle = open(log, "wb")
        process = subprocess.Popen([self.image, "--fn"] + [str(a) for a in args],
                                   stdout=handle, stderr=subprocess.STDOUT, env=env)
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
        # Large enough that the kill lands between segments.  This used to
        # have to stay small as well, because `fn-tcl-drive`'s guard named
        # `fn-tcl-sessionp`, whose `fn-tcl-octet-listsp` walked every octet
        # staged so far, and the host checks that guard once per socket chunk.
        # The guard is now `fn-tcl-session-cheapp`, which reads carried
        # scalars only; `profile` below is the measurement.
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
        cut_env = dict(os.environ)
        cut_env["FN_TCPCL_TEST_PAUSE_AFTER_STAGE_DATA"] = "1"
        second = self.spawn(["tcpcl", "listen", 0, 1, spool, "dtn://fn-b/", "-",
                             4, 1024, 1048576, "-", "-"], root / "listen-2.log",
                            env=cut_env)
        sender = None
        killed_after = 0
        sender_acks = 0
        try:
            port = self.port_of(second)
            sender = self.spawn(["tcpcl", "send", "127.0.0.1", port, big,
                                 root / "active-spool", "dtn://fn-a/", "-", 4, 1024,
                                 1048576, 0, "-"], root / "send-2.log")
            # The host pauses at the modeled cut: staged data is durable, its
            # final name is not published, and the final XFER_ACK remains in
            # the held queue.  This makes the process-death point independent
            # of scheduler speed while preserving the original expectation.
            deadline = time.time() + 30
            while time.time() < deadline:
                seen = self.kinds(self.events(root / "listen-2.log", "passive",
                                              source=None), ":XFER-ACK")
                paused = "TCPCL TEST STAGE-DATA " in (root / "listen-2.log").read_text(
                    errors="replace")
                if paused:
                    killed_after = seen
                    sender_acks = self.kinds(self.events(root / "send-2.log", "active",
                                                         source=None), ":XFER-ACK")
                    break
                if second.poll() is not None:
                    break
                time.sleep(0.005)
            if not killed_after:
                raise RuntimeError("receiver did not reach the staged-data crash cut")
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
                     acks_observed_by_sender=sender_acks,
                     final_ack_withheld=sender_acks < killed_after,
                     durable_before=durable_before,
                     durable_after=(acknowledged.exists()
                                    and acknowledged.read_bytes() == small.read_bytes()),
                     interrupted_absent=not holds_big,
                     no_partials=[n for n in staged
                                  if n.startswith(".incoming-")] == [],
                     staged=staged)
        ok = (facts["first_rc"] == EXIT_OK and facts["reconnect_rc"] == EXIT_OK
              and facts["acks_before_kill"] >= 3 and facts["durable_before"]
              and facts["final_ack_withheld"]
              and facts["durable_after"] and facts["interrupted_absent"]
              and facts["no_partials"])
        self.record("crash", ok, **facts)

    def scenario_profile(self):
        """The per-chunk guard is not quadratic in the transfer.

        `fn-tcl-drive` is reached through its executable counterpart once per
        socket chunk, and that counterpart checks the callee's guard.  While
        the guard named `fn-tcl-sessionp` it walked every octet staged so far,
        so quadrupling a transfer quadrupled the chunks *and* the walk: about
        sixteen times the guard work.  With `fn-tcl-session-cheapp` the walk
        is gone and the cost is linear in the transfer.

        The verdict is the ratio, not the seconds: a box under load moves both
        measurements together.  The bar is deliberately loose (below 8x for a
        4x transfer) so that this fails on a quadratic guard and passes on a
        linear one without becoming a timing flake.
        """
        root = self.fresh("profile")
        small_n, large_n = 64 * 1024, 256 * 1024
        times = {}
        staged = {}
        for name, size, seed in (("small", small_n, 6), ("large", large_n, 7)):
            spool = root / ("spool-" + name)
            payload = root / (name + ".bundle")
            payload.write_bytes(bundle(size, seed))
            listener = self.spawn(
                ["tcpcl", "listen", 0, 1, spool, "dtn://fn-b/", "-",
                 4, 4096, 1048576, "-", "-"], root / ("listen-" + name + ".log"))
            try:
                port = self.port_of(listener)
                started = time.time()
                sent = subprocess.run(
                    [self.image, "--fn", "tcpcl", "send", "127.0.0.1", str(port),
                     str(payload), str(root / ("active-" + name)), "dtn://fn-a/",
                     "-", "4", "4096", "1048576", "0", "-"],
                    capture_output=True, timeout=900)
                times[name] = time.time() - started
                listener.wait(timeout=120)
            finally:
                if listener.poll() is None:
                    listener.kill()
                listener.handle.close()
            landed = spool / "passive-0.bundle"
            staged[name] = dict(
                rc=sent.returncode,
                intact=landed.exists() and landed.read_bytes() == payload.read_bytes())
        ratio = (times["large"] / times["small"]) if times["small"] > 0 else None
        facts = dict(small_octets=small_n, large_octets=large_n,
                     small_seconds=round(times["small"], 3),
                     large_seconds=round(times["large"], 3),
                     ratio=(round(ratio, 2) if ratio is not None else None),
                     size_ratio=large_n // small_n,
                     small=staged["small"], large=staged["large"])
        ok = (staged["small"]["rc"] == EXIT_OK and staged["large"]["rc"] == EXIT_OK
              and staged["small"]["intact"] and staged["large"]["intact"]
              and ratio is not None and ratio < 8.0)
        self.record("profile", ok, **facts)

    def scenario_adu(self):
        """A fn-authored BPv7 bundle each way, and the ADU out equals the ADU in.

        The distinction the scenario exists to hold: neither side is given a
        file of bundle octets.  Each is given an ADU, and the image builds the
        bundle around it by calling `fn-bpn-send'; each decodes what arrives by
        calling `fn-bpn-receive', which is the only thing that recovers an ADU.
        A `bp send' that wrapped `tcpcl send' would fail here at the first
        assertion, because there would be no ADU in either journal.
        """
        root = self.fresh("adu")
        b_journal, a_journal = root / "b-journal", root / "a-journal"
        adu_a, adu_b = root / "adu-a.bin", root / "adu-b.bin"
        adu_a.write_bytes(bundle(1500, 3))
        adu_b.write_bytes(bundle(700, 4))
        listener = self.spawn(
            ["bp", "receive", 0, 1, b_journal, "dtn://fn-b/", "-", 3600000, 2, 32,
             1048576, adu_b, "dtn://fn-a/"],
            root / "receive.log")
        try:
            port = self.port_of(listener)
            sender = subprocess.run(
                [self.image, "--fn", "bp", "send", "127.0.0.1", str(port),
                 str(adu_a), str(a_journal), "dtn://fn-a/", "dtn://fn-b/",
                 "3600000", "2", "32", "1048576", "1"],
                capture_output=True, timeout=120)
            send_log = root / "send.log"
            send_log.write_bytes(sender.stdout + sender.stderr)
            listener.wait(timeout=60)
        finally:
            if listener.poll() is None:
                listener.kill()
            listener.handle.close()

        recv_text = (root / "receive.log").read_text(errors="replace")
        send_text = send_log.read_text(errors="replace")
        b_got = b_journal / "passive-0.adu"
        a_got = a_journal / "active-0.adu"
        authored = [BP_AUTHORED.match(l) for l in send_text.splitlines()]
        authored = [m for m in authored if m]
        facts = dict(
            listener_rc=listener.returncode, sender_rc=sender.returncode,
            a_authored=bool(authored),
            a_bundle_octets=int(authored[0].group(5)) if authored else 0,
            a_payload_octets=int(authored[0].group(4)) if authored else 0,
            b_accepted=len([l for l in recv_text.splitlines()
                            if BP_ACCEPTED.match(l)]),
            a_accepted=len([l for l in send_text.splitlines()
                            if BP_ACCEPTED.match(l)]),
            b_adu_is_a_adu=b_got.exists() and b_got.read_bytes() == adu_a.read_bytes(),
            a_adu_is_b_adu=a_got.exists() and a_got.read_bytes() == adu_b.read_bytes(),
            refusals=len([l for l in (recv_text + send_text).splitlines()
                          if l.startswith("BP refused")]),
            uncertain=len([l for l in (recv_text + send_text).splitlines()
                           if l.startswith("BP uncertain")]))
        # The bundle on the wire is strictly larger than the ADU inside it:
        # a `bp send' that forwarded the ADU unwrapped would show equality.
        facts["bundle_wraps_adu"] = (facts["a_bundle_octets"]
                                     > facts["a_payload_octets"] > 0)
        ok = (facts["listener_rc"] == EXIT_OK and facts["sender_rc"] == EXIT_OK
              and facts["a_authored"] and facts["bundle_wraps_adu"]
              and facts["b_accepted"] == 1 and facts["a_accepted"] == 1
              and facts["b_adu_is_a_adu"] and facts["a_adu_is_b_adu"]
              and facts["refusals"] == 0 and facts["uncertain"] == 0)
        self.record("adu", ok, **facts)

    def scenario_replay(self):
        """The listener's octets, folded back through `fn-tcl-drive' alone.

        Receive-only, and that is the point.  `tcpcl replay` folds
        `fn-tcl-drive` over the trace and calls nothing else, so it models a
        session that consumes octets and never originates a transfer.  A node
        that also *sends* reaches `fn-tcl-send` and `fn-tcl-pump` from the
        host, not from the wire, so the replay's state has no outbound
        transfer when the peer's XFER_ACK arrives and the machine is right to
        answer MSG_REJECT Unexpected where the loop said `:outbound-sent`.

        The lab's first run, 2026-09-20, replayed `exchange`'s trace, and
        `exchange`'s listener carries a reply bundle: the differential failed
        at exactly that divergence.  The trace was wrong for the differential,
        not the machine, so this scenario now drives its own listener with no
        reply.  Extending the differential to a sending node means putting the
        host's aux calls in the trace; that is not done, and `specs/tcpcl.md`
        records the limit.
        """
        root = self.fresh("replay")
        spool = root / "passive-spool"
        trace = root / "passive.trace"
        payload = root / "to-b.bundle"
        payload.write_bytes(bundle(1500, 8))
        listener = self.spawn(
            ["tcpcl", "listen", 0, 1, spool, "dtn://fn-b/", "-", 4, 1024, 1048576,
             "-", trace], root / "listen.log")
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
        if not trace.exists():
            return self.record("replay", False, reason="the listener wrote no trace")
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
        facts = dict(rc=replayed.returncode, sender_rc=sender.returncode,
                     loop_events=len(loop), model_events=len(model),
                     received=sorted(p.name for p in spool.glob("*.bundle")),
                     equal=(loop == model))
        if loop != model:
            facts["first_difference"] = next(
                ("{!r} != {!r}".format(a, b) for a, b in zip(loop, model) if a != b),
                "lengths differ")
        self.record("replay", facts["rc"] == EXIT_OK and facts["equal"]
                    and facts["loop_events"] > 0, **facts)

    # -- the whole lab ----------------------------------------------------
    def run(self, which: str) -> int:
        self.work.mkdir(parents=True, exist_ok=True)
        if which in ("all", "exchange"):
            self.scenario_exchange()
        if which in ("all", "refused"):
            self.scenario_refused()
        if which in ("all", "keepalive"):
            self.scenario_keepalive()
        if which in ("all", "crash"):
            self.scenario_crash()
        if which in ("all", "profile"):
            self.scenario_profile()
        if which in ("all", "adu"):
            self.scenario_adu()
        if which in ("all", "replay"):
            self.scenario_replay()
        summary = dict(scenario="summary",
                       passed=[r["scenario"] for r in self.results if r["ok"]],
                       failed=[r["scenario"] for r in self.results if not r["ok"]])
        summary["ok"] = not summary["failed"]
        print(json.dumps(summary, sort_keys=True), flush=True)
        return 0 if summary["ok"] else 1


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--image", default=None,
                        help="the fn native image (default: `build/fn-host` "
                             "under the worktree this was invoked from)")
    parser.add_argument("--work", default="/tmp/tcpcl-lab")
    parser.add_argument("--scenario", default="all",
                        choices=["all", "exchange", "refused", "keepalive",
                                 "crash", "profile", "adu", "replay"])
    args = parser.parse_args(argv)
    # An image path is read from the tree this command was invoked from, not
    # from the process's working directory and not from the tree this file
    # happens to live in: a lane running the main checkout's copy of the lab
    # must measure the lane's image.
    image = Path(args.image).expanduser() if args.image else (
        repo_root() / "build" / "fn-host")
    if not image.is_absolute():
        image = repo_root() / image
    if not image.exists():
        print(json.dumps({"scenario": "summary", "ok": False,
                          "reason": "no image at {}".format(image)}))
        return 2
    return Lab(str(image), args.work).run(args.scenario)


if __name__ == "__main__":
    sys.exit(main())

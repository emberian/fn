#!/usr/bin/env python3
"""An fn application request and its receipt across pinned dtn7-rs relays.

Topology, all on loopback, every process started and stopped by PID:

    fn A (`bp-service`, then `bp-node serve`)
        --[hold relay]--> dtn7 relay 1 [--> dtn7 relay 2] --> fn B (`bp-node serve`)

`--relays 1` is the two-node application exchange; `--relays 2` is the
four-node lab's pinned-BPA mode (home, relay-a, relay-b, destination).
`--relays 0` is the control: the same steps with fn B as A's direct TCPCL
peer, so a refusal through dtn7 can be told apart from a lab defect.

Steps, each reported with the three outcomes kept apart (accepted, refused,
uncertain) and never inferred from a later step:

  1. A's request.  A holds a durable forwarding obligation for an article in
     its Store and FNWF workflow (`bp-obligation undertake`).  The request ADU
     is ACL2's `fn-bpa-make-request` over that article, evaluated by the
     certified books through the lab's ACL2 bridge exactly as
     tests/test_bp_node_native.py does (no native verb authors it from the
     workflow; see the evidence record).  `bp-service run` enqueues it in A's
     FNBS and offers it to the first hop through a byte relay that stops
     forwarding mid-transfer.  The first hop (dtn7 relay 1, or fn B in the
     control) is SIGKILLed by PID while the transfer is held.
  2. restart and resume.  The first hop restarts (dtn7: the same sled store);
     `bp-service resume` re-offers A's durable job.
  3. B's node.  `bp-node serve` admits the session from the observed channel
     against its enrolled boundary, takes kind-5 custody and dispatches the
     delivery to the application (request accepted / duplicate / refused).
  4. the receipt.  B's owed receipt (if any) is queued and forwarded toward
     A by `bp-contact tick`; A's `bp-node serve` matches it against the
     request's obligation (`receipt-accepted`, pin released) or not.

`--native` (M4 native request, 2026-09-24) replaces step 1's bridge-authored
ADU and `bp-service run` with `bp-obligation request`: A's own workflow
publishes ACL2's attempt, takes the :submit and hands ACL2's request ADU to
its FNBS carrier (books/bp-request-plan.lisp).  It adds a second, never
requested control obligation on A whose pin must stay `yes`, and step 5:
A is SIGKILLed by PID inside two request publications (after the :submit,
before the carrier; after the attempt, before its outcome) and the work must
stay outstanding and visible, never dropped.

Counts come from the processes' own ACL2-decided lines and from the FNBS and
FNWF state, never from a socket write.  No power-loss claim follows.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import select
import shutil
import socket
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from run_fn_bp_interop import DTN_EPOCH_UNIX, free_port  # noqa: E402
from run_fn_dtn7_interrupted_contact import Dtnd  # noqa: E402

SENDER, RECEIVER = "dtn://sender/", "dtn://receiver/"
MSGID = b"<m4-app-receipt@example.invalid>"
WORK = "work-bp-node"
BP_LINE = re.compile(r"^(BP |TCPCL |bp-node|bp-service|fn: ).*$")


class HoldRelay:
    """Forward bytes both ways; optionally stop forwarding the client's bytes
    after `hold_after` of them and report that the transfer is held.  It never
    answers a protocol message and never fabricates an acknowledgement."""

    def __init__(self, target):
        self.listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(4)
        self.listener.settimeout(0.2)
        self.port = self.listener.getsockname()[1]
        self.target, self.hold_after = target, None
        self.held = threading.Event()
        self.forwarded = []
        self.stopped = threading.Event()
        threading.Thread(target=self._accept, daemon=True).start()

    def arm(self, hold_after):
        self.hold_after = hold_after
        self.held.clear()

    def _accept(self):
        while not self.stopped.is_set():
            try:
                client, _ = self.listener.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            hold, self.hold_after = self.hold_after, None
            threading.Thread(target=self._exchange, args=(client, hold),
                             daemon=True).start()

    def _exchange(self, client, hold):
        sent = 0
        with client:
            try:
                upstream = socket.create_connection(("127.0.0.1", self.target), 5)
            except OSError:
                return
            with upstream:
                pair = (client, upstream)
                deadline = time.monotonic() + 60
                while time.monotonic() < deadline and not self.stopped.is_set():
                    readable, _, _ = select.select(pair, (), (), 0.2)
                    for source in readable:
                        try:
                            data = source.recv(65536)
                        except OSError:
                            self.forwarded.append(sent)
                            return
                        if not data:
                            self.forwarded.append(sent)
                            return
                        if source is client:
                            if hold is not None and sent + len(data) > hold:
                                data = data[:max(0, hold - sent)]
                                try:
                                    upstream.sendall(data)
                                except OSError:
                                    pass
                                sent += len(data)
                                self.held.set()
                                # Held: the rest of the transfer never leaves.
                                # Wait for the upstream to die, then sever.
                                upstream.settimeout(30)
                                try:
                                    while upstream.recv(65536):
                                        pass
                                except OSError:
                                    pass
                                self.forwarded.append(sent)
                                return
                            sent += len(data)
                            try:
                                upstream.sendall(data)
                            except OSError:
                                self.forwarded.append(sent)
                                return
                        else:
                            try:
                                client.sendall(data)
                            except OSError:
                                self.forwarded.append(sent)
                                return

    def close(self):
        self.stopped.set()
        self.listener.close()


def sha16(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()[:16]


def lines_of(path):
    text = Path(path).read_text(errors="replace") if Path(path).exists() else ""
    return [l.strip() for l in text.splitlines() if BP_LINE.match(l.strip())]


def outcome_of(rc):
    return {0: "accepted", 1: "refused", 3: "uncertain"}.get(rc, "other rc={}".format(rc))


class Lab:
    def __init__(self, args):
        self.image = Path(args.image).resolve()
        self.work = args.work
        self.work.mkdir(parents=True, exist_ok=False)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.wall = str(int((time.time() - DTN_EPOCH_UNIX) * 1000))
        self.procs = []
        self.logs = {}

    def path(self, name):
        return self.work / name

    def fn(self, tag, *args, timeout=180):
        log = self.path("{}.log".format(tag))
        out = subprocess.run([str(self.image), "--fn", *map(str, args)],
                             capture_output=True, text=True, timeout=timeout,
                             env=self.env, cwd=str(ROOT))
        log.write_text("$ fn {}\n{}{}\n# rc={}\n".format(
            " ".join(map(str, args)), out.stdout, out.stderr, out.returncode))
        self.logs[tag] = log
        return out

    def spawn(self, tag, *args):
        log = self.path("{}.log".format(tag))
        handle = log.open("wb")
        handle.write(("$ fn {}\n".format(" ".join(map(str, args)))).encode())
        handle.flush()
        proc = subprocess.Popen([str(self.image), "--fn", *map(str, args)],
                                stdout=handle, stderr=subprocess.STDOUT,
                                env=self.env, cwd=str(ROOT))
        self.procs.append(dict(tag=tag, pid=proc.pid, proc=proc))
        self.logs[tag] = log
        return proc, log

    def wait_log(self, log, pattern, timeout):
        deadline = time.time() + timeout
        rx = re.compile(pattern)
        while time.time() < deadline:
            m = rx.search(log.read_text(errors="replace"))
            if m:
                return m
            time.sleep(0.2)
        return None

    def stop(self, proc, how="SIGTERM"):
        entry = next(p for p in self.procs if p["proc"] is proc)
        if proc.poll() is None:
            if how == "SIGKILL":
                proc.kill()
            else:
                proc.terminate()
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=10)
                how += " then SIGKILL"
            entry["stopped"] = "{} rc={}".format(how, proc.returncode)
        else:
            entry["stopped"] = "exited rc={}".format(proc.returncode)


def author_request(article):
    from tools import run_bp_ingress, run_store
    bridge = run_bp_ingress.Acl2BpIngress()
    try:
        bridge.call('(include-book "books/bp-adu")')
        if bridge.extract_message_id(article) != MSGID:
            raise SystemExit("ACL2 extracted another Message-ID")
        _archive, subject, _prov = run_store.metadata(MSGID, article)

        def text(value):
            return "(fn-store-octets->string '" + bridge.literal(value) + ")"

        fields = [WORK.encode(), subject, SENDER.encode(), RECEIVER.encode(),
                  b"native-policy", b"origin-native", b"wire-auth", b"terms-native"]
        form = ("(fn-bpa-encode (fn-bpa-make-request "
                + " ".join(text(v) for v in fields)
                + " '" + bridge.literal(article) + "))")
        return run_store.acl2_octets(bridge.call(form))
    finally:
        bridge.close()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--image", required=True)
    ap.add_argument("--dtn7-repo", type=Path)
    ap.add_argument("--work", required=True, type=Path)
    ap.add_argument("--relays", type=int, default=1, choices=(0, 1, 2))
    ap.add_argument("--settle", type=float, default=40.0)
    ap.add_argument("--native", action="store_true",
                    help="A authors the request with `bp-obligation request'")
    ap.add_argument("--b-trusts", choices=("carried", "neighbour", "source"),
                    default="carried",
                    help="the EID B's boundary enrols: the TCPCL neighbour's "
                         "(dtn7's node ID) or the request's source (fn A's); "
                         "`carried' (D23, the default) enrols the neighbour with "
                         "`carries' naming the far fn node, and the far node "
                         "under its own EID, on each side")
    args = ap.parse_args(argv)
    if args.relays and not args.dtn7_repo:
        ap.error("--dtn7-repo is required unless --relays 0")
    lab = Lab(args)
    report = dict(image=str(lab.image), relays=args.relays, dtn_time_ms=lab.wall, native=args.native,
                  topology=["fn-a"] + ["dtn7-r{}".format(i + 1)
                                       for i in range(args.relays)] + ["fn-b"])
    if args.relays:
        repo = args.dtn7_repo.resolve()
        report["dtn7_revision"] = subprocess.run(
            ["git", "-C", str(repo), "rev-parse", "HEAD"],
            capture_output=True, text=True).stdout.strip()
    body = b"".join(b"line %04d of the m4 application receipt article\r\n" % i
                    for i in range(120))
    article = (b"Path: sender.bp.gate.invalid!not-for-mail\r\n"
               b"From: sender@example.invalid\r\nNewsgroups: fn.test\r\n"
               b"Subject: m4 application receipt across dtn7\r\n"
               b"Date: Thu, 24 Sep 2026 20:00:00 +0000\r\n"
               b"Message-ID: " + MSGID + b"\r\n\r\n" + body)
    a_store, b_store = lab.path("a-store"), lab.path("b-store")
    a_fnbs, b_fnbs = lab.path("a-fnbs"), lab.path("b-fnbs")
    a_wf, b_wf = lab.path("a-fnwf"), lab.path("b-fnwf")
    a_rj, b_rj = lab.path("a-fnrj"), lab.path("b-fnrj")
    a_port, b_port = free_port(), free_port()
    extra_works = []   # (work, msgid) posted, enqueued and undertaken on A
    if args.native:
        for tag in ("control", "cut-submit", "cut-attempt"):
            extra_works.append(("work-" + tag, "<m4-native-{}@example.invalid>".format(tag)))
    relays, hold = [], None
    b_serve = a_serve = None
    steps = []

    def step(name, rc_or_outcome, tags, **extra):
        row = dict(step=name, outcome=(outcome_of(rc_or_outcome)
                                       if isinstance(rc_or_outcome, int)
                                       else rc_or_outcome), **extra)
        row["logs"] = {t: dict(file=lab.logs[t].name, sha256_16=sha16(lab.logs[t]),
                               lines=lines_of(lab.logs[t])) for t in tags}
        steps.append(row)
        return row

    try:
        # --- setup: stores, A's obligation, enrolment on both sides -------
        setup = []
        for store in (a_store, b_store):
            setup.append(lab.fn("setup-init-" + store.name, "store", store, "init", "fn.test").returncode)
        (lab.path("article")).write_bytes(article)
        for tag, argv in (
            ("setup-post", ("store", a_store, "post", MSGID.decode(), lab.path("article"),
                            "-", "-", "fn.test")),
            ("setup-wf-init", ("app-journal", "workflow-init", a_store, a_wf, SENDER,
                               RECEIVER, "native-policy", RECEIVER, 3600000,
                               "origin-native", "wire-auth")),
            ("setup-wf-enqueue", ("app-journal", "workflow-enqueue", a_store, a_wf, 1, 0,
                                  WORK, MSGID.decode(), "forward-bp-node", RECEIVER,
                                  "native-policy", "terms-native")),
            ("setup-undertake", ("bp-obligation", "undertake", a_store, a_wf, WORK, 3))):
            setup.append(lab.fn(tag, *argv).returncode)
        for i, (work, msgid) in enumerate(extra_works):
            extra = article.replace(MSGID, msgid.encode()).replace(
                b"m4 application receipt across dtn7", work.encode())
            lab.path(work + ".article").write_bytes(extra)
            for tag, argv in (
                ("setup-post-" + work, ("store", a_store, "post", msgid,
                                        lab.path(work + ".article"), "-", "-", "fn.test")),
                ("setup-enqueue-" + work, ("app-journal", "workflow-enqueue", a_store, a_wf,
                                           2 + i, 0, work, msgid, "forward-" + work,
                                           RECEIVER, "native-policy", "terms-native")),
                ("setup-undertake-" + work, ("bp-obligation", "undertake", a_store, a_wf,
                                             work, 3))):
                setup.append(lab.fn(tag, *argv).returncode)
        # The last hop each side sees: dtn7's node ID, or the fn peer directly.
        b_neighbour = ("dtn://dtn7-r{}/".format(args.relays)
                       if args.relays and args.b_trusts in ("neighbour", "carried")
                       else SENDER)
        report["b_trusts"] = dict(mode=args.b_trusts, eid=b_neighbour)
        a_neighbour = "dtn://dtn7-r1/" if args.relays else RECEIVER
        carried = bool(args.relays) and args.b_trusts == "carried"
        b_scope = ["fn.test", "32768", "16"]
        # D23: the neighbour's boundary carries the far fn node's EID; the far
        # node is enrolled under its own EID (on a port nothing listens on),
        # and its request is judged under that enrolment and its scope.
        for side, store, path_id, name, remote, eid, port, scope, far in (
                ("a", a_store, "sender.bp.gate.invalid", "return-boundary",
                 "r1.bp.gate.invalid" if args.relays else "receiver.bp.gate.invalid",
                 a_neighbour, a_port, [],
                 ("receiver-author", "receiver.bp.gate.invalid", RECEIVER, [])),
                ("b", b_store, "receiver.bp.gate.invalid", "ingress-boundary",
                 "rn.bp.gate.invalid" if args.relays else "sender.bp.gate.invalid",
                 b_neighbour, b_port, [] if carried else b_scope,
                 ("sender-author", "sender.bp.gate.invalid", SENDER, b_scope))):
            config = lab.path("{}.toml".format(side))
            config.write_text('[store]\npath = "{}"\n'.format(store), encoding="ascii")
            setup.append(lab.fn("setup-{}-path".format(side), "operator", config, "policy",
                                "set", "path-identity", path_id).returncode)
            carries = ["carries", far[2]] if carried else []
            setup.append(lab.fn("setup-{}-boundary".format(side), "operator", config,
                                "bp-boundary", "add", name, remote, eid, port,
                                *scope, *carries).returncode)
            if carried:
                setup.append(lab.fn("setup-{}-author".format(side), "operator", config,
                                    "bp-boundary", "add", far[0], far[1], far[2],
                                    free_port(), *far[3]).returncode)
        report["b_trusts"]["carried"] = carried
        report["setup_rcs"] = setup
        report["a_pinned_before"] = lab.fn("a-status-0", "bp-obligation", "status",
                                           a_store, a_wf, WORK).stdout.strip()
        request = lab.path("request.adu")
        if not args.native:
            request.write_bytes(author_request(article))
            report["request_adu"] = dict(octets=request.stat().st_size, sha256=sha16(request))

        # --- relays and B --------------------------------------------------
        if args.relays:
            ports = [(free_port(), free_port()) for _ in range(args.relays)]
            for i in range(args.relays):
                name = "dtn7-r{}".format(i + 1)
                nxt = ("tcp://127.0.0.1:{}/dtn7-r{}".format(ports[i + 1][0], i + 2)
                       if i + 1 < args.relays else
                       "tcp://127.0.0.1:{}/receiver".format(b_port))
                prev = ("tcp://127.0.0.1:{}/dtn7-r{}".format(ports[i - 1][0], i)
                        if i else "tcp://127.0.0.1:{}/sender".format(a_port))
                d = Dtnd.__new__(Dtnd)
                d.bin = repo / "target/release/dtnd"
                d.work = lab.work / name
                d.work.mkdir(parents=True, exist_ok=True)
                d.name, d.endpoint, d.db = name, None, "sled"
                d.cla_port, d.web_port = ports[i]
                d.proc, d.starts, d.peers = None, [], [nxt, prev]
                relays.append(d)
            # relay 2 (four-node) opens its window only after relay-a's restart.
            relays[0].start(relays[0].peers)
            first_hop = relays[0].cla_port
            last_hop = relays[-1].cla_port
        else:
            first_hop, last_hop = b_port, a_port

        def start_b(tag):
            proc, log = lab.spawn(
                tag, "bp-node", "serve", b_port, b_fnbs, b_store, b_rj, b_wf,
                RECEIVER, SENDER, RECEIVER, "native-policy", RECEIVER,
                "127.0.0.1", last_hop, "0", 3600000, 2, 32, 1048576, lab.wall, 60000)
            lab.wait_log(log, r"BP NODE LISTENING", 60)
            return proc, log

        hold = HoldRelay(first_hop)
        b_serve, b_log = start_b("b-serve" if args.relays else "b-serve-0")
        # --- 1. A's request, held mid-transfer, first hop SIGKILLed ---------
        hold.arm(600)
        send_argv = (["bp-obligation", "request", str(a_store), str(a_wf), WORK,
                      WORK + "-attempt", str(a_fnbs), SENDER, "127.0.0.1", str(hold.port),
                      "3600000", "2", "32", "1048576", lab.wall, "60000"]
                     if args.native else
                     ["bp-service", "run", "127.0.0.1", str(hold.port),
                      str(request), str(a_fnbs), SENDER, RECEIVER, WORK, WORK + "-attempt", "0",
                      "3600000", "2", "32", "1048576", lab.wall, "60000"])
        a_send = subprocess.Popen(
            [str(lab.image), "--fn", *send_argv],
            stdout=lab.path("a-1-send.log").open("wb"), stderr=subprocess.STDOUT,
            env=lab.env, cwd=str(ROOT))
        lab.logs["a-1-send"] = lab.path("a-1-send.log")
        held = hold.held.wait(60)
        killed = None
        if args.relays:
            relays[0].kill()
            killed = dict(first_hop="dtn7-r1", pid=relays[0].starts[-1]["pid"])
        else:
            lab.stop(b_serve, "SIGKILL")
            killed = dict(first_hop="fn-b", pid=b_serve.pid)
        a_send.wait(timeout=120)
        s1 = step("1 A request, held mid-transfer, first hop SIGKILLed", a_send.returncode,
                  ["a-1-send"], held=held, bytes_forwarded_before_hold=list(hold.forwarded),
                  sigkill=killed)
        # --- 2. restart the first hop, resume A's durable job --------------
        if args.relays:
            relays[0].start(relays[0].peers)
        else:
            b_serve, b_log = start_b("b-serve-1")
        r = lab.fn("a-2-resume", "bp-service", "resume", a_fnbs, SENDER, 3600000, 2, 32,
                   1048576, lab.wall, 60000)
        step("2 first hop restarted, A resumes its durable job", r.returncode, ["a-2-resume"],
             restarted=(relays[0].starts[-1]["pid"] if args.relays else b_serve.pid))
        if args.relays == 2:
            time.sleep(3.0)
            relays[1].start(relays[1].peers)   # the relay-b window opens now
        # --- 3. B's node: custody, then the application --------------------
        verdict = lab.wait_log(b_log, r"BP node delivery (request-\S+)", args.settle)
        time.sleep(2.0)
        blines = lines_of(b_log)
        kind5 = sorted(p.name for p in (b_fnbs / "lifecycle").glob("*.fnb")) \
            if (b_fnbs / "lifecycle").exists() else []
        step("3 B admits, takes custody, dispatches to its application",
             verdict.group(1) if verdict else "no-verdict", [b_log.stem],
             transport_accepted=sum(1 for l in blines if l.startswith("BP accepted")),
             channel_refusals=[l for l in blines if "admission refused" in l],
             application=[l for l in blines if l.startswith("BP node delivery")],
             source_decisions=[l for l in blines if l.startswith("BP node source")],
             receipts_queued=[l for l in blines if "receipt queued" in l],
             b_fnbs_lifecycle_frames=len(kind5), b_fnbs_frame_names=kind5)
        # --- 4. the receipt toward A ---------------------------------------
        lab.stop(b_serve)
        a_serve, a_log = lab.spawn(
            "a-serve", "bp-node", "serve", a_port, a_fnbs, a_store, a_rj, a_wf,
            SENDER, RECEIVER, SENDER, "native-policy", SENDER,
            "127.0.0.1", first_hop, "0", 3600000, 2, 32, 1048576, lab.wall, 60000)
        lab.wait_log(a_log, r"BP NODE LISTENING", 60)
        tick = lab.fn("b-4-tick", "bp-contact", "tick", b_fnbs, RECEIVER, SENDER,
                      0, 60000, 3600000, 2, 32, 1048576, lab.wall, 60000)
        matched = lab.wait_log(a_log, r"BP node delivery (receipt-\S+)", args.settle)
        time.sleep(1.0)
        lab.stop(a_serve)
        status = lab.fn("a-status-4", "bp-obligation", "status", a_store, a_wf, WORK)
        alines = lines_of(a_log)
        step("4 B's receipt carried back and matched at A",
             matched.group(1) if matched else "no-receipt", ["b-4-tick", "a-serve"],
             tick_outcome=outcome_of(tick.returncode),
             a_receipt_lines=[l for l in alines if l.startswith("BP node delivery")],
             a_source_decisions=[l for l in alines if l.startswith("BP node source")],
             a_inbound_custody=[l for l in alines if l.startswith(
                 ("BP accepted", "BP received carrier"))],
             a_obligation=status.stdout.strip())
        report["a_pinned_after"] = status.stdout.strip()
        if args.native:
            control = lab.fn("a-status-control", "bp-obligation", "status", a_store, a_wf,
                             "work-control")
            step("4b the control obligation, never requested", control.stdout.strip(),
                 ["a-status-control"], a_obligation=control.stdout.strip())
            dead = free_port()

            def cut(work, selector, marker):
                tag = "a-5-" + work
                log = lab.path(tag + ".log")
                handle = log.open("wb")
                argv = ["bp-obligation", "request", str(a_store), str(a_wf), work,
                        work + "-a1", str(a_fnbs), SENDER, "127.0.0.1", str(dead),
                        "3600000", "2", "32", "1048576", lab.wall, "60000"]
                handle.write(("$ {}=1 fn {}\n".format(selector, " ".join(argv))).encode())
                handle.flush()
                env = dict(lab.env)
                env[selector] = "1"
                proc = subprocess.Popen([str(lab.image), "--fn", *argv], stdout=handle,
                                        stderr=subprocess.STDOUT, env=env, cwd=str(ROOT))
                lab.procs.append(dict(tag=tag, pid=proc.pid, proc=proc))
                lab.logs[tag] = log
                reached = lab.wait_log(log, marker, 90)
                lab.stop(proc, "SIGKILL")
                after = lab.fn(tag + "-status", "bp-obligation", "status", a_store, a_wf, work)
                again = lab.fn(tag + "-again", "bp-obligation", "request", a_store, a_wf,
                               work, work + "-a2", a_fnbs, SENDER, "127.0.0.1", dead,
                               3600000, 2, 32, 1048576, lab.wall, 60000)
                later = lab.fn(tag + "-status-2", "bp-obligation", "status", a_store, a_wf,
                               work)
                step("5 A SIGKILLed at {}".format(marker), after.stdout.strip(),
                     [tag, tag + "-status", tag + "-again", tag + "-status-2"],
                     marker_reached=bool(reached), sigkill=dict(pid=proc.pid),
                     status_after_kill=after.stdout.strip(),
                     request_again=outcome_of(again.returncode),
                     request_again_lines=[l for l in (again.stdout + again.stderr).splitlines()
                                          if l.startswith(("BP obligation", "fn: "))],
                     status_after_again=later.stdout.strip())
            cut("work-cut-submit", "FN_BP_OBLIGATION_TEST_PAUSE_AFTER_SUBMIT",
                "BP OBLIGATION SUBMIT TAKEN")
            cut("work-cut-attempt", "FN_BP_OBLIGATION_TEST_PAUSE_AFTER_ATTEMPT",
                "BP OBLIGATION ATTEMPT DURABLE")
            final = {w: lab.fn("a-6-status-" + w, "bp-obligation", "status", a_store, a_wf,
                               w).stdout.strip()
                     for w in [WORK] + [w for w, _ in extra_works]}
            report["a_final_status"] = final
        if args.relays:
            delivered = {}
            for d in relays:
                for s in d.starts:
                    text = Path(s["log"]).read_text(errors="replace")
                    delivered[Path(s["log"]).parent.name + "/" + Path(s["log"]).name] = dict(
                        received=len(re.findall(r"Received new bundle|received bundle|Received bundle", text)),
                        forwarded=len(re.findall(r"[Ss]ending bundle|[Ff]orwarding|sent bundle", text)))
            report["dtn7_log_counts"] = delivered
    finally:
        if hold:
            hold.close()
        for p in lab.procs:
            if p["proc"].poll() is None:
                lab.stop(p["proc"])
            p.setdefault("stopped", "exited rc={}".format(p["proc"].returncode))
        for d in relays:
            d.stop()
        report["processes"] = [dict(tag=p["tag"], pid=p["pid"], stopped=p["stopped"])
                               for p in lab.procs]
        report["dtnd_processes"] = {d.name: d.starts for d in relays}
    report["steps"] = steps
    out = lab.path("report.json")
    out.write_text(json.dumps(report, indent=2, sort_keys=True))
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""The receipt-observed schedule point on a real BP node (design §5, row
"receipt observed"; W7c-2a).  The recipe `bp-node`: a sender Store with one
undertaken obligation, a receiver node serving TCPCL on the developer image
with FN_APP_JOURNAL_TEST_HOLD_RECEIPT=decided (host/native/bp-app.lisp
fnn-bpapp-pause-after-decision: the receipt path blocks after the decision
is recorded and before the ADU/completion, until the file
FN_APP_JOURNAL_TEST_HOLD_RECEIPT_RELEASE names appears).  At the hold the
nemesis runs the scenario's interleave:

  duplicate        a second carrier of the same request arrives (its own
                   outbound journal) before the first's completion;
  reorder          the operator removes the route the receipt would take
                   (`bp-route remove'); the decision was recorded under the
                   policy before the change, the receipt's forwarding follows
                   the policy after it (bp-node.lisp reads the route table
                   each pass);
  lose-completion  the receiver dies at the hold (the process-death form of
                   the same point): its completion is lost, the sender sees
                   an interrupted transfer, `bp-node dispatch' replays.

Healing is the scenario's: a replay or a dispatch pass, the route restored,
the receipt observed at the sender's node (`BP node delivery
receipt-accepted', then `bp-obligation status' pinned=no) and the probe
(the receiver Store's article count and the identity's presence).  Every
observation goes into the journal (client: the sender's transfer outcome,
the operator's policy changes and passes, the sender's status, the probe;
environment: the hold reached, the death; internal: the receiver's own
disposition lines, never narrowing) and the verdict is `checker.check'
under the contract rules `receipt-once' and `receipt-policy-order'.

    python3 -m tools.resilience.adapters.bp_node --image build/fn-host-developer \
        [--variant duplicate|reorder|lose-completion|all] [--out DIR] [--no-fault]
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tests.native_harness import (  # noqa: E402
    Acl2Session, EXIT, environment, free_port, run, start)
from tests.test_bp_contact_relay_native import ByteRelay  # noqa: E402
from tools.resilience.scenario import Scenario  # noqa: E402
from tools.resilience.journal import Journal  # noqa: E402
from tools.resilience import checker  # noqa: E402

HOLD = "FN_APP_JOURNAL_TEST_HOLD_RECEIPT"
RELEASE = "FN_APP_JOURNAL_TEST_HOLD_RECEIPT_RELEASE"
HOLD_LINE = b"BP APP RECEIPT-OBSERVED HOLD release="
RELEASED_LINE = b"BP APP RECEIPT-OBSERVED RELEASED"
QUEUED_LINE = b"BP node receipt queued"
DELIVERED_LINE = b"BP node delivery receipt-accepted"
DISPOSITION = re.compile(rb"BP application handoff durable disposition=([a-z-]+)")
# Lines the receipt path prints only past the hold point (bp-node.lisp's
# outbox `receipt queued', bp-service.lisp's durable disposition): seen
# before the hold's own line they are the evidence the image lacks the hold.
PROCEEDED = (QUEUED_LINE, b"BP application handoff durable disposition=")
BOUNDARY = "receipt-observed"


def _first_line_of(markers):
    """A `wait_for' predicate: the end of the earliest whole line holding any
    of MARKERS (bytes), else None."""
    def find(text):
        ends = []
        for marker in markers:
            at = text.find(marker)
            if at >= 0:
                newline = text.find(b"\n", at)
                if newline >= 0:
                    ends.append(newline + 1)
        return min(ends) if ends else None
    return find
GROUP = "fn.test"
MSGID = b"<schedule-receipt@example.invalid>"
IDENTITY = "bundle-1"
SENDER, RECEIVER = "dtn://sender/", "dtn://receiver/"
WORK = "work-receipt"
ROUTE = (SENDER + "*", "sender-boundary")     # the receipt's route out of the receiver
BP_ARGS = ("3600000", "2", "32", "1048576", "0", "0")
ARTICLE = (
    b"Path: sender.bp.gate.invalid!not-for-mail\r\n"
    b"From: sender@example.invalid\r\n"
    b"Newsgroups: fn.test\r\n"
    b"Subject: schedule point receipt-observed\r\n"
    b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
    b"Message-ID: " + MSGID + b"\r\n"
    b"\r\nreceipt-observed body\r\n"
)


class HarnessFailure(Exception):
    pass


class BpRun:
    """One receipt-observed scenario on IMAGE under WORK."""

    def __init__(self, scenario: Scenario, image: Path, work: Path, fault_hook: bool = True):
        self.s, self.image, self.work = scenario, Path(image).resolve(), Path(work).resolve()
        self.hook = fault_hook
        self.j = Journal(scenario.id)
        self.j.bind(IDENTITY, MSGID.decode("ascii"))
        self.receiver_store = self.work / "receiver-store"
        self.receiver_journal = self.work / "receiver-fnbs"
        self.receiver_receipts = self.work / "receiver-fnrj"
        self.receiver_workflow = self.work / "receiver-fnwf"
        self.sender_store = self.work / "sender-store"
        self.sender_journal = self.work / "sender-fnbs"
        self.sender_workflow = self.work / "sender-fnwf"
        self.request = self.work / "request.adu"
        self.release = self.work / "release-receipt"
        self.configs = {True: self.work / "receiver-fn.toml", False: self.work / "sender-fn.toml"}
        self.relay = None
        self.procs = []
        self.route_present = True

    # -- the fixture (tests/test_bp_node_native.py's, without its asserts)
    def invoke(self, *args, env=None, timeout=120):
        return run([str(self.image), "--fn", *map(str, args)], cwd=ROOT,
                   env=environment(env), timeout=timeout)

    def must(self, what, *args, env=None, timeout=120):
        r = self.invoke(*args, env=env, timeout=timeout)
        if r.returncode != EXIT.OK:
            raise HarnessFailure("{}:rc={}:{}".format(
                what, r.returncode, (r.stderr or r.stdout).decode("utf-8", "replace")[-160:]))
        return r

    def setup(self):
        self.relay = ByteRelay()
        for store in (self.receiver_store, self.sender_store):
            self.must("store-init", "store", store, "init", GROUP)
        with Acl2Session(self.image) as bridge:
            fields = [WORK.encode(), bridge.subject(MSGID, ARTICLE), SENDER.encode(),
                      RECEIVER.encode(), b"native-policy", b"origin-native", b"wire-auth",
                      b"terms-native"]
            self.request.write_bytes(bridge.bp_request(fields, ARTICLE))
        article = self.work / "sender-article"
        article.write_bytes(ARTICLE)
        self.must("sender-post", "store", self.sender_store, "post", MSGID.decode(), article,
                  "-", "-", GROUP)
        self.must("workflow-init", "app-journal", "workflow-init", self.sender_store,
                  self.sender_workflow, SENDER, RECEIVER, "native-policy", RECEIVER, 3600000,
                  "origin-native", "wire-auth")
        self.must("workflow-enqueue", "app-journal", "workflow-enqueue", self.sender_store,
                  self.sender_workflow, 1, 0, WORK, MSGID.decode(), "forward-receipt", RECEIVER,
                  "native-policy", "terms-native")
        self.must("undertake", "bp-obligation", "undertake", self.sender_store,
                  self.sender_workflow, WORK, 3)

    def trust(self, receiver: bool, listen_port: int):
        node = RECEIVER if receiver else SENDER
        peer = SENDER if receiver else RECEIVER
        store = self.receiver_store if receiver else self.sender_store
        config = self.configs[receiver]
        config.write_text('[store]\npath = "{}"\n'.format(store), encoding="ascii")
        name = "sender-boundary" if receiver else "receiver-boundary"
        local = "receiver.bp.gate.invalid" if receiver else "sender.bp.gate.invalid"
        remote = "sender.bp.gate.invalid" if receiver else "receiver.bp.gate.invalid"
        self.must("policy-set", "operator", config, "policy", "set", "path-identity", local)
        self.must("boundary-add", "operator", config, "bp-boundary", "add", name, remote, peer,
                  listen_port, GROUP, "32768", "16", "contact", self.relay.port)
        self.must("route-add", "operator", config, "bp-route", "add", peer + "*", name)

    def node(self, receiver: bool, once: bool, extra_env=None):
        node = RECEIVER if receiver else SENDER
        peer = SENDER if receiver else RECEIVER
        listen_port = free_port()
        self.trust(receiver, listen_port)
        argv = [str(self.image), "--fn", "bp-node", "serve", str(listen_port),
                str(self.receiver_journal if receiver else self.sender_journal),
                str(self.receiver_store if receiver else self.sender_store),
                str(self.receiver_receipts if receiver else self.work / "sender-fnrj"),
                str(self.receiver_workflow if receiver else self.sender_workflow),
                node, peer, node, "native-policy", node, "127.0.0.1", str(self.relay.port),
                "1" if once else "0", *BP_ARGS]
        process = start(argv, cwd=ROOT, env=environment(extra_env))
        self.procs.append(process)
        try:
            line = process.announcement(b"BP NODE LISTENING ", timeout=60)
        except Exception as e:      # the harness's fail: a deadline or an exit
            raise HarnessFailure("node-not-listening:{}".format(str(e)[:120]))
        return process, int(line.rsplit(b" ", 1)[1])

    def send(self, port: int, op_id: str):
        """`bp-service run' of the request toward PORT from its own outbound
        journal (the sender node holds the lifecycle lock), in the background:
        it blocks while the receiver holds."""
        argv = [str(self.image), "--fn", "bp-service", "run", "127.0.0.1", str(port),
                str(self.request), str(self.work / ("outbound-" + op_id)), SENDER, RECEIVER,
                op_id, op_id + "-attempt", "0", *BP_ARGS]
        process = start(argv, cwd=ROOT, env=environment())
        self.procs.append(process)
        return process

    def reply(self, op_id: str, process, **extra):
        try:
            out, err = process.communicate(timeout=180)
        except Exception as e:
            process.kill()
            raise HarnessFailure("sender-hung:{}:{}".format(op_id, str(e)[:80]))
        rc = process.returncode
        outcome = "accepted" if rc == EXIT.OK else "lost"
        self.j.client("reply", operation=op_id, outcome=outcome, route="bp-transit",
                      returncode=rc, **extra)
        return rc

    def dispositions(self, text: bytes, op_id: str, source: str):
        for m in DISPOSITION.finditer(text):
            self.j.internal("claim", claim="durable", operation=op_id,
                            disposition=m.group(1).decode("ascii"), source=source)
        if QUEUED_LINE in text:
            self.j.internal("claim", claim="receipt-queued", operation=op_id, source=source)

    def dispatch(self, op_id: str):
        """One `bp-node dispatch' pass of the receiver (the operator's verb):
        the replay of a durable decision and the receipt's forwarding."""
        started = time.monotonic()
        r = self.invoke("bp-node", "dispatch", self.receiver_journal, self.receiver_store,
                        self.receiver_receipts, self.receiver_workflow, RECEIVER, SENDER,
                        RECEIVER, "native-policy", RECEIVER, "127.0.0.1", self.relay.port,
                        "1", *BP_ARGS, "0", timeout=240)
        out = r.stdout or b""
        forward = ("no-route" if b"BP forwarding no-route" in out else
                   "sent" if (b"status=sent" in out or b"status=forwarded" in out) else
                   "none")
        self.dispositions(out, "receipt-1", "dispatch")
        self.j.client("restart", operation=op_id,
                      outcome="completed" if r.returncode == EXIT.OK else "failed",
                      returncode=r.returncode, forward=forward,
                      route_present=self.route_present,
                      seconds=round(time.monotonic() - started, 3))
        return r

    def policy(self, op_id: str, present: bool):
        verb = "add" if present else "remove"
        r = self.invoke("operator", self.configs[True], "bp-route", verb, *ROUTE)
        if r.returncode != EXIT.OK:
            # The operator's own words go into the cause.  On 444fb9f41 (run
            # rf4-444f-2) `bp-route remove` at the hold is `refused store-held
            # (a process holds the store lock and no control socket is there
            # to reach it ...)`: the receiver is a `bp-node serve` process,
            # which opens no control socket, and the owner service (`operator
            # run`, host/native/owner.lisp) does not embed the BP node, so no
            # live reconfiguration path (host/native/control.lisp :admin ->
            # fnn-owner-live-admin-serialized) reaches it.  That is the image
            # naming the missing form: pending by name, never a stopped node
            # standing in for the running one.
            words = " ".join(((r.stdout or b"") + b" " + (r.stderr or b""))
                             .decode("ascii", "replace").split())
            if "store-held" in words:
                raise HarnessFailure(
                    "live-route-unavailable:bp-route {} under a running `bp-node serve' "
                    "(no control socket; the owner service does not embed the BP node): "
                    "{}".format(verb, words[:160]))
            raise HarnessFailure("bp-route-{}:rc={}:{}".format(verb, r.returncode, words[:160]))
        self.route_present = present
        self.j.client("policy-change", operation=op_id, what="receipt-policy",
                      change="route-restored" if present else "route-removed",
                      route_present=present, returncode=r.returncode)

    def deliver(self, op_id: str, sender_node):
        try:
            sender_node.output_until(DELIVERED_LINE, timeout=120)
            seen = True
        except Exception:
            seen = False
        r = self.invoke("bp-obligation", "status", self.sender_store, self.sender_workflow, WORK)
        pinned = ("no" if b"pinned=no" in r.stdout else
                  "yes" if b"pinned=yes" in r.stdout else "unknown")
        self.j.client("status", operation=op_id, receipt="accepted" if seen else "absent",
                      pinned=pinned, returncode=r.returncode)

    def probe(self, op_id: str):
        # `operator CONFIG status --replay': the counts over the replayed log
        # (transactions= articles=); the plain stopped report (operability-2
        # cbe0c1d7d) is the header only, and the store verb's `--replay'
        # (operability-9) is not on 444fb9f41 (rf4-444f-2: store-status:rc=0).
        # The receiver node is stopped by now (both variants).
        status = self.invoke("operator", self.configs[True], "status", "--replay", timeout=300)
        counts = re.findall(rb"^transactions=[0-9]+ articles=([0-9]+) ", status.stdout,
                            re.MULTILINE)
        if status.returncode != EXIT.OK or len(counts) != 1:
            raise HarnessFailure("store-status:rc={}".format(status.returncode))
        inspected = self.invoke("store", self.receiver_store, "inspect", MSGID.decode(),
                                timeout=300)
        present = inspected.returncode == EXIT.OK
        self.j.client("probe", operation=op_id, identity=IDENTITY, articles=int(counts[0]),
                      present=present,
                      bytes="relayed" if present and inspected.stdout != ARTICLE else
                      ("as-sent" if present else "absent"))

    # -- the scenario
    def variant(self) -> str:
        return self.s.id.rsplit("-", 1)[1] if "lose" not in self.s.id else "lose-completion"

    def workload(self):
        j = self.j
        fault = self.s.fault_on("receipt-1") if self.hook else None
        sender_node, sender_port = self.node(False, once=False)
        self.relay.route(sender_port)
        env = {HOLD: "decided", RELEASE: str(self.release)} if fault else None
        receiver, port = self.node(True, once=False, extra_env=env)
        first = self.send(port, "receipt-1")
        if fault is None:
            try:
                receiver.output_until(QUEUED_LINE, timeout=120)
            except Exception:
                pass
            self.reply("receipt-1", first)
            receiver.stop(grace=10)
            return sender_node
        held, end = receiver.stdout.wait_for(_first_line_of((HOLD_LINE,) + PROCEEDED),
                                             receiver.cursor, time.monotonic() + 120)
        if end is None:
            first.kill()
            raise HarnessFailure("hold-not-reached:neither {!r} nor a receipt-path line "
                                 "after the hold point within 120 s".format(HOLD_LINE))
        receiver.cursor = end
        evidence = held.strip().splitlines()[-1].decode("ascii", "replace")
        if HOLD_LINE.decode("ascii") not in evidence:
            # The receipt path went past the decision without holding: this
            # image does not carry fnn-bpapp-pause-after-decision (dev
            # f2e929ced), so the point is PENDING BY NAME on it, not a
            # verdict (the mode: a hold that is not in the image = pending).
            first.kill()
            raise HarnessFailure("hold-unavailable:{}=decided set and the receipt path "
                                 "proceeded past the hold point on image {}: {}".format(
                                     HOLD, self.image.name, evidence[:120]))
        dup = None
        for step in fault.interleave:
            o = self.s.operation(step)
            if o.op == "receipt":
                dup = (o.id, self.send(port, o.id))
                time.sleep(0.5)        # its connection is queued on the listener
            elif o.op == "policy-change":
                self.policy(o.id, present=False)
            else:
                raise HarnessFailure("interleave-unsupported:" + o.op)
        if fault.action == "interleave":
            j.environment("fault-fired", operation="receipt-1", boundary=BOUNDARY,
                          action="interleave", route=fault.route, evidence=evidence)
            self.release.write_text("released\n")
            try:
                receiver.output_until(RELEASED_LINE, timeout=60)
            except Exception:
                raise HarnessFailure("release-not-observed")
            self.reply("receipt-1", first)
            if dup is not None:
                self.reply(dup[0], dup[1], duplicate_of="receipt-1")
            time.sleep(1.0)            # the pass's own forwarding attempt, if any
            receiver.stop(grace=10)
            self.dispositions(receiver.stdout.tail(200000), "receipt-1", "receiver")
        else:                          # withhold-completion: the death form
            receiver.kill()
            receiver.wait(timeout=15)
            j.environment("fault-fired", operation="receipt-1", boundary=BOUNDARY,
                          action=fault.action, route=fault.route,
                          evidence=evidence + "; receiver rc={}".format(receiver.returncode))
            self.reply("receipt-1", first)
        return sender_node

    def healing(self, sender_node):
        for step in self.s.healing:
            o = self.s.operation(step)
            if o.op == "restart":
                self.dispatch(o.id)
            elif o.op == "policy-change":
                self.policy(o.id, present=True)
            elif o.op == "status":
                self.deliver(o.id, sender_node)
            elif o.op == "probe":
                self.probe(o.id)
            else:
                raise HarnessFailure("healing-unsupported:" + o.op)

    def finish(self, cause: str | None = None):
        path = self.j.write(self.work / "journal.jsonl")
        reread = Journal.read(path)
        verdict = (checker.harness_failure(self.s, reread, cause) if cause
                   else checker.check(self.s, reread))
        (self.work / "verdict.json").write_text(
            json.dumps(verdict.to_json(), indent=1, sort_keys=True))
        return reread, verdict

    def run(self) -> tuple:
        j = self.j
        j.stage("workload", "begun")
        try:
            try:
                self.setup()
                sender_node = self.workload()
            finally:
                j.stage("workload", "ended")
            j.stage("healing", "begun")
            started = time.monotonic()
            self.healing(sender_node)
            j.stage("healing", "ended", elapsed=round(time.monotonic() - started, 3))
        except HarnessFailure as e:
            return self.finish(str(e))
        finally:
            for p in self.procs:
                try:
                    p.stop(grace=5)
                except Exception:
                    pass
            if self.relay is not None:
                self.relay.close()
        return self.finish()


def run_scenario(scenario: Scenario, image: Path, work: Path, fault_hook: bool = True) -> tuple:
    Path(work).mkdir(parents=True, exist_ok=True)
    return BpRun(scenario, image, work, fault_hook).run()


def main(argv=None) -> int:
    from tools.resilience import schedule_points
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--image", required=True)
    ap.add_argument("--variant", default="all")
    ap.add_argument("--out")
    ap.add_argument("--no-fault", action="store_true")
    a = ap.parse_args(argv)
    image = Path(a.image)
    if not (image.is_file() and os.access(image, os.X_OK)):
        print("not an executable image: " + str(image)); return 2
    out = Path(a.out) if a.out else Path(tempfile.mkdtemp(prefix="fn-receipt-"))
    worst = 0
    for s in schedule_points.scenarios():
        if s.initial.get("recipe") != "bp-node":
            continue
        if a.variant != "all" and not s.id.endswith("-" + a.variant):
            continue
        work = out / s.id
        work.mkdir(parents=True, exist_ok=True)
        s.dump(work / "scenario.json")
        _, v = run_scenario(s, image, work, fault_hook=not a.no_fault)
        print("{} {} {} witnesses={} healing={}".format(
            s.id, v.kind, v.cause or "", ",".join(v.witnesses_observed) or "-",
            "{}s".format(v.healing["elapsed"]) if v.healing else "-"))
        if not v.green:
            worst = 1
    print("journals under " + str(out))
    return worst


if __name__ == "__main__":
    raise SystemExit(main())

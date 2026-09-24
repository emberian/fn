#!/usr/bin/env python3
"""Four-node delay-tolerant lab: home -> relay-a -> relay-b -> destination.

Non-overlapping contact windows (one pair at a time), one carried-media hop
(relay-a to relay-b), and these events: relay-a is SIGKILLed mid-forward, a
receipt is lost and regenerated, an attempt expires and is retried under the
next window, and a duplicate and a reordered pair reach the destination.

Every acceptance, receipt, charge, retention obligation and local number is
ACL2's, through the existing host entry points (`run_store.command_post`,
`run_bp_receive.receive_bpa_request`, `WorkflowJournal`, `tools/media.py`).
This driver only schedules contacts, carries bytes and reads journals.

A relay here is receiver-then-sender through two *separate* host paths: the
receiver accepts and archives, and a sender work is then enqueued for the same
committed article.  That is the manually reenqueued archival relay.  The host
emits no relay receipt *kind*, so this lab asserts the archival behaviour and
records the forwarding undertaking of `books/relay.lisp` as a proposal only --
never as a passed assertion.

With `--dtn7-repo` unset the transport is `mock_bpa.py`: a laboratory scheduler,
not BPv7.  Results are about fn's behaviour across contacts, not interoperation.
With `--dtn7-repo` (and `--image`, the DTN developer image) home and
destination are native fn nodes and relay-a/relay-b are dtn7-rs daemons: see
`run_dtn7` and run_fn_dtn7_app_receipt.py.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path
import platform
import select
import signal
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from mock_bpa import MockNetwork, lab_bundle_octets  # noqa: E402
from tools import media, run_bp_ingress, run_bp_receive, run_store, workflow_journal  # noqa: E402
from tools.workflow_bridge import Acl2WorkflowReplay  # noqa: E402

LAB_PATH = Path(__file__).resolve()
CHILD_READY_SECONDS = 240.0

# `run_bp_receive` carries one destination/policy/issuer for the whole lab, so
# every node presents the same *application* endpoint while the transport
# identities differ per hop.  Per-node receiver configuration is open work.
DESTINATION_EID = run_bp_receive.DESTINATION
POLICY_ID = run_bp_receive.POLICY_ID
GROUP = "fn.letters"
LIFETIME = 300
# The lowest transaction identity a lab node allocates; every later one
# comes from the durable journal (`Outbound.next_txid`), not a counter.
TXID_BASE = 100
# Bundle sequence numbers for the carried-media hop, kept clear of the mock
# BPA's own per-node submission counter so a carried bundle and a forwarded
# one are never the same bundle.
MEDIA_SEQUENCE_BASE = 1000

ARTICLES = {
    "a1": (b"<four-node-1@fn.example>",
           b"Message-ID: <four-node-1@fn.example>\r\nNewsgroups: fn.letters\r\n"
           b"Subject: The first letter across four nodes\r\n"
           b"From: home <home@fn.example>\r\n\r\n"
           b"Carried by contact, by media, and by contact again.\r\n"),
    "a2": (b"<four-node-2@fn.example>",
           b"Message-ID: <four-node-2@fn.example>\r\nNewsgroups: fn.letters\r\n"
           b"Subject: The second letter, delivered out of order\r\n"
           b"From: home <home@fn.example>\r\n\r\n"
           b"Its number at the destination is the destination's own.\r\n"),
}
NODES = ("home", "relay-a", "relay-b", "destination")


# --------------------------------------------------------------------------
# Node plumbing
# --------------------------------------------------------------------------

@dataclass
class Node:
    name: str
    root: Path
    bpa: object = None

    @property
    def store(self) -> Path: return self.root / "store"
    @property
    def workflow(self) -> Path: return self.root / "workflow"
    @property
    def inbox(self) -> Path: return self.root / "inbox"
    @property
    def receipts(self) -> Path: return self.root / "receipts"
    @property
    def consumed(self) -> Path: return self.root / "consumed"

    def config(self) -> dict:
        return {"local-eid": f"dtn://{self.name}/receipts", "peer-eid": DESTINATION_EID,
                "policy-id": POLICY_ID, "receipt-authority": run_bp_receive.ISSUER,
                "bp-lifetime": LIFETIME, "incarnation": f"origin-{self.name}-1",
                "authorization-context": "trusted-lab-1"}

    def work_id(self, key: str) -> str:
        return f"work:{key}:{self.name}"


def initialize(node: Node) -> None:
    node.root.mkdir(mode=0o700, parents=True, exist_ok=True)
    run_store.Store(node.store, True).initialize()


def post(node: Node, key: str) -> None:
    """Publish an article locally through the actual CLI post path."""
    msgid, article = ARTICLES[key]
    payload = node.root / f"{key}.article"
    payload.write_bytes(article)
    code = run_store.command_post(SimpleNamespace(
        store=node.store, message_id=msgid.decode("ascii"), payload=payload,
        group=[GROUP], charge=None, inject_fault=None))
    if code != run_store.EXIT_OK:
        raise RuntimeError(f"{node.name} refused its own post of {key}")


def receive(node: Node, bid: str, **kwargs) -> run_bp_receive.ReceiveResult:
    # `bundle` is the raw octets ACL2 derives the staging identity and the
    # expiry decision from; the BID is only the agent's handle for download
    # and delete.  A receiver that was handed the BID alone would be staging
    # under the agent's naming rather than under the bundle's own identity.
    return run_bp_receive.receive_bpa_request(
        store_root=node.store, inbox_root=node.inbox, receipt_root=node.receipts,
        bid=bid, source_eid=f"dtn://{node.name}/upstream",
        inventory=node.bpa.inventory, download=node.bpa.download,
        bundle=node.bpa.bundle,
        delete=node.bpa.delete, local_policy_authorized=True, **kwargs)


def snapshot(node: Node) -> dict:
    """One read-only ACL2 session per node: counts, frontier and exact bytes."""
    store, bridge, records = run_bp_ingress.open_live_bp_store(node.store, False)
    try:
        held = {key: bridge.lookup(msgid) == article
                for key, (msgid, article) in ARTICLES.items()
                if bridge.lookup_found(msgid)}
        return {"records": len(records), "articles": bridge.article_count(),
                "pins": bridge.pin_count(),
                "group_next": {str(code): bridge.group_next(code) for code in range(4)},
                "exact_articles": held}
    finally:
        bridge.close()
        store.close()


def receipt_digests(node: Node) -> dict:
    root = node.receipts / "records"
    if not root.is_dir():
        return {}
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.iterdir())}


def journal_records(root: Path) -> list[str]:
    records = Path(root) / "records"
    if not records.is_dir():
        return []
    return sorted(p.name for p in records.iterdir())


class Outbound:
    """One live sender session over a node's own store and workflow journal.

    Every value published here is checked by ACL2 before publication
    (`history_preflight`/`preflight`), and the projected request ADU comes from
    `fn-bpo-host-request-adu`.  No work, attempt or receipt is decided here.
    """

    def __init__(self, node: Node, faults=run_store.NO_FAULTS):
        self.node = node
        self.store, self.acl2, self.records = run_store.open_live_store(node.store, True)
        try:
            self.bridge = Acl2WorkflowReplay(self.acl2)
            self.journal = workflow_journal.WorkflowJournal(node.workflow, self.bridge,
                                                            faults=faults)
            self.journal.open()
            self.acl2.call('(ld "host/bp-outbound-host.lisp" :ld-error-action :return '
                           ':ld-error-triples t)')
        except BaseException:
            self.close()
            raise

    def close(self):
        for attribute in ("journal", "acl2", "store"):
            owned = getattr(self, attribute, None)
            if owned is not None:
                owned.close()

    def __enter__(self): return self
    def __exit__(self, *args): self.close()

    def initialize(self):
        if not list(self.journal.records.iterdir()):
            self.journal.initialize(self.node.config())

    def next_txid(self) -> int:
        """Allocate above the DURABLE history, never from an in-memory counter.

        A process-death cut publishes records this process never saw, so a
        counter living in this process reissues a transaction identity the
        journal already holds -- and ACL2's history preflight refuses it,
        rightly: a reused transaction id is a reused decision.  Reading the
        journal decides nothing; the allocation is above what is durable.
        """
        highest = TXID_BASE
        for path in sorted(self.journal.records.iterdir()):
            _kind, values = workflow_journal.decode_record(path.read_bytes())
            candidate = values.get("txid")
            if isinstance(candidate, int) and candidate > highest:
                highest = candidate
        return highest + 1

    def enqueue(self, key: str):
        msgid, article = ARTICLES[key]
        archive, subject, _evidence = run_store.metadata(msgid, article)
        values = {"txid": self.next_txid(), "tx-generation": 0,
                  "work-id": self.node.work_id(key), "msgid": msgid.decode("ascii"),
                  "immutable-subject": subject.decode(),
                  "archive-obligation-id": archive.decode(),
                  "forward-obligation-id": f"forward:{key}:{self.node.name}",
                  "peer-eid": DESTINATION_EID, "policy-id": POLICY_ID,
                  "terms-id": "keep-until-authorized-release:lab-v0"}
        self.journal.persist_enqueue(values, lambda _values: True)
        return values

    def submit(self, key: str, *, generation: int, label: str, lifetime=LIFETIME,
               carrier=None):
        """Persist the attempt, then hand the projected ADU to one carrier.

        `carrier` defaults to the node's BPA.  A carried-media hop passes its
        own carrier, so the media hop records its submission intent durably
        before any byte leaves, exactly as a BPA hop does.
        """
        work_id = self.node.work_id(key)
        values = {"txid": self.next_txid(), "tx-generation": 0, "work-id": work_id,
                  "attempt-id": f"attempt:{key}:{generation}",
                  "attempt-generation": generation,
                  "local-eid": self.node.config()["local-eid"],
                  "peer-eid": DESTINATION_EID, "policy-id": POLICY_ID,
                  "bp-lifetime": lifetime}
        projected = []

        def external_action():
            adu = self.request_adu(work_id)
            projected.append(adu)
            if carrier is not None:
                return carrier(adu, label)
            return self.node.bpa.submit(adu, DESTINATION_EID, label, lifetime)

        bid = self.journal.persist_attempt_then_call(values, external_action)
        self.journal.publish("transport", {
            "work-id": work_id, "attempt-id": values["attempt-id"],
            "attempt-generation": generation, "status": "bpa-submit-replied"})
        return bid, projected[0]

    def request_adu(self, work_id: str) -> bytes:
        form = ("(fn-bpo-host-request-adu (fn-store-octets->string '"
                + self.acl2.literal(work_id.encode("utf-8")) + ") state)")
        adu = run_store.acl2_octets(self.acl2.call(form))
        if not adu:
            raise RuntimeError(f"ACL2 refused the durable work projection: {work_id}")
        return adu

    def request_retry(self, key: str, previous_generation: int):
        self.journal.publish("retry-request", {
            "work-id": self.node.work_id(key),
            "attempt-id": f"attempt:{key}:{previous_generation}",
            "attempt-generation": previous_generation, "policy-id": POLICY_ID})

    def status(self, key: str) -> str:
        return self.bridge.work_status(self.node.work_id(key))

    def origin(self, key: str) -> str:
        """Where this work came from, which the status word cannot say.

        `recovered` is a work the reopen found in the journal; `enqueued` is
        one this session put there.  Both read `outstanding`.
        """
        return self.bridge.work_origin(self.node.work_id(key))


# --------------------------------------------------------------------------
# The mid-forward kill and its recovery
# --------------------------------------------------------------------------

class PauseAt(run_store.FaultPoints):
    """Report readiness at one named point and block until the parent kills us."""
    __slots__ = ("point", "ready_fd", "control_fd", "fired")

    def __init__(self, point, ready_fd, control_fd):
        self.point, self.ready_fd, self.control_fd = point, ready_fd, control_fd
        self.fired = False

    def at(self, point):
        if point != self.point or self.fired:
            return None
        self.fired = True
        os.write(self.ready_fd, b"READY\n")
        # The parent SIGKILLs this process group while this read blocks, so
        # nothing after the named durable boundary runs.
        os.read(self.control_fd, 1)
        return None


def child_main(argv) -> int:
    """Run relay-a's onward enqueue up to one named cut, then block."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--child", action="store_true")
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--name", required=True)
    parser.add_argument("--key", required=True)
    parser.add_argument("--point", required=True)
    parser.add_argument("--ready-fd", required=True, type=int)
    parser.add_argument("--control-fd", required=True, type=int)
    args = parser.parse_args(argv)
    node = Node(args.name, args.root.absolute())
    with Outbound(node) as outbound:
        # The journal's own CONFIG record is published without the injector, so
        # the cut lands on the onward obligation and on nothing before it.
        outbound.initialize()
        outbound.journal.faults = PauseAt(args.point, args.ready_fd, args.control_fd)
        outbound.enqueue(args.key)
    return 0


def kill_mid_forward(node: Node, key: str, point: str) -> dict:
    """SIGKILL relay-a's own process group at one durable publication cut."""
    ready_read, ready_write = os.pipe()
    control_read, control_write = os.pipe()
    command = [sys.executable, str(LAB_PATH), "--child", "--root", str(node.root),
               "--name", node.name, "--key", key, "--point", point,
               "--ready-fd", str(ready_write), "--control-fd", str(control_read)]
    child = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             pass_fds=(ready_write, control_read),
                             start_new_session=True)
    os.close(ready_write)
    os.close(control_read)
    line = b""
    try:
        deadline = time.monotonic() + CHILD_READY_SECONDS
        while time.monotonic() < deadline:
            ready, _, _ = select.select([ready_read], [], [], 0.5)
            if ready:
                line = os.read(ready_read, 64)
                break
            if child.poll() is not None:
                break
    finally:
        # Only the group this lab created is signalled.
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except PermissionError:
            child.kill()
        try:
            child.wait(timeout=30)
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait(timeout=30)
        os.close(ready_read)
        os.close(control_write)
        stderr = child.stderr.read().decode("utf-8", "replace")[-2000:]
        child.stdout.close()
        child.stderr.close()
    if line != b"READY\n":
        raise RuntimeError(f"mid-forward cut {point} was never reached: {stderr}")
    return {"point": point, "signal": "SIGKILL", "returncode": child.returncode,
            "records_after_kill": journal_records(node.workflow)}


# --------------------------------------------------------------------------
# The lab
# --------------------------------------------------------------------------

@dataclass
class Lab:
    run: Path
    transport: str
    report: dict = field(default_factory=dict)

    def check(self, name: str, value: bool) -> None:
        self.report.setdefault("assertions", {})[name] = bool(value)
        if not value:
            raise AssertionError(name)

    def event(self, name: str, **fields) -> None:
        self.report.setdefault("events", []).append({"event": name, **fields})


def source_snapshot() -> dict:
    paths = list((ROOT / "books").glob("*.lisp")) + list((ROOT / "host").glob("*.lisp"))
    paths += list((ROOT / "tools").glob("*.py")) + list((ROOT / "tests/bp-dtn7").glob("*.py"))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


class NoRevision(RuntimeError):
    """The lab cannot say which revision it ran, so it will not run."""


def lab_revision(named: str | None = None) -> str:
    """The revision this run is evidence about.

    `git rev-parse HEAD` was called here unguarded until 2026-09-21, and a
    gate tree is a `git archive` extract with no repository, so it raised
    before the lab did anything: all eight four-node reds of one gate had
    that single cause, reproducible in 0.085 s.  A gate therefore passes
    `--revision`, or sets `FN_GATE_REVISION`, and the rev-parse is only the
    fallback for a worktree that has one.

    A missing revision REFUSES rather than substituting "unknown".  This lab
    writes an evidence file, and an evidence file that cannot name what it is
    evidence about is worse than no run: the four-node record was read as
    current for a day while it described a tree that could no longer start
    the lab.
    """
    for candidate in (named, os.environ.get("FN_GATE_REVISION")):
        if candidate and candidate.strip():
            return candidate.strip()
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                       text=True,
                                       stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.CalledProcessError) as error:
        raise NoRevision(
            "this tree is not a git repository ({} is a `git archive` extract "
            "in a gate), so the lab cannot name the revision its evidence is "
            "about; pass --revision <rev> or set FN_GATE_REVISION. It will "
            "not write \"unknown\".".format(ROOT)) from error


def run_dtn7(lab: Lab, run: Path, started: float, dtn7_repo: Path, image: Path) -> dict:
    """The pinned-BPA mode: home and destination are native fn nodes
    (`bp-node serve` on the DTN image), relay-a and relay-b are dtn7-rs 0.21.0
    daemons on sled stores.  relay-a is SIGKILLed by PID mid-transfer and
    restarted; relay-b's window opens only after that.  The steps and their
    three-outcome rows are run_fn_dtn7_app_receipt.py's, with two relays."""
    import contextlib
    import io
    import run_fn_dtn7_app_receipt as exchange
    report = lab.report
    report["topology"] = "home (fn) -> relay-a (dtn7) -> relay-b (dtn7) -> destination (fn)"
    report["image"] = str(image)
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            exchange.main(["--image", str(image), "--dtn7-repo", str(dtn7_repo),
                           "--relays", "2", "--work", str(run / "dtn7")])
        inner = json.loads((run / "dtn7" / "report.json").read_text())
        report["exchange"] = inner
        steps = {row["step"][0]: row for row in inner["steps"]}
        lab.check("relay-a cut mid-transfer leaves home uncertain",
                  steps["1"]["outcome"] == "uncertain")
        lab.check("home's durable job is accepted by relay-a after its restart",
                  steps["2"]["outcome"] == "accepted")
        lab.check("destination takes custody of the request exactly once",
                  steps["3"]["transport_accepted"] == 1)
        lab.check("destination's application decides exactly once",
                  len(steps["3"]["application"]) == 1)
        accepted = steps["3"]["outcome"] == "request-accepted"
        lab.check("no receipt is inferred from transport delivery",
                  accepted or (steps["4"]["outcome"] == "no-receipt"
                               and "pinned=yes" in inner["a_pinned_after"]))
        # D23 (the exchange's default trust mode): each carrier's boundary
        # lists the far fn node, so the request and its receipt are accepted.
        lab.check("an accepted request is receipted at home and unpins it",
                  not accepted or (steps["4"]["outcome"] == "receipt-accepted"
                                   and "pinned=no" in inner["a_pinned_after"]))
        report["observed"] = {
            "application": steps["3"]["outcome"],
            "receipt_at_home": steps["4"]["outcome"],
            "home_obligation": inner["a_pinned_after"]}
        report["status"] = "passed"
    except Exception as error:  # the evidence says what failed
        report.update(status="failed", error=repr(error))
    finally:
        report["seconds"] = round(time.monotonic() - started, 1)
        report["limitations"] = [
            "relay-a and relay-b are dtn7-rs (epidemic routing, static peers); "
            "home and destination are native fn nodes. No relay receipt kind.",
            "The request ADU is ACL2's fn-bpa-make-request evaluated through "
            "the lab's ACL2 bridge; no native verb authors it from the workflow.",
            "Real local process death (SIGKILL by PID); no power-loss claim.",
        ]
        (run / "evidence.json").write_text(
            json.dumps(report, indent=1, sort_keys=True) + "\n")
    return report


def run_lab(run: Path, *, dtn7_repo=None, revision=None, image=None) -> dict:
    started = time.monotonic()
    lab = Lab(run, "mock_bpa" if dtn7_repo is None else "pinned dtn7-rs")
    report = lab.report
    report.update({
        "schema": 1, "status": "running", "run": str(run), "transport": lab.transport,
        "invocation": [sys.executable, *sys.argv],
        "topology": "home -> relay-a -> relay-b -> destination",
        "a_policy": "explicitly trusted local lab; no signatures, no authenticated peer",
        "revision": lab_revision(revision),
        "versions": {"python": sys.version, "platform": platform.platform()},
        "source_sha256": source_snapshot(), "assertions": {}, "events": [],
    })
    if dtn7_repo is not None:
        if image is None:
            raise SystemExit("--dtn7-repo needs --image (or FN_NATIVE_BP_NODE_HOST): "
                             "home and destination are native fn nodes")
        return run_dtn7(lab, run, started, Path(dtn7_repo).resolve(),
                        Path(image).resolve())

    network = MockNetwork(run / "net")
    nodes = {}
    for name in NODES:
        node = Node(name, run / name)
        node.bpa = network.add(name, f"dtn://{name}", DESTINATION_EID)
        initialize(node)
        nodes[name] = node
    home, relay_a, relay_b, destination = (nodes[n] for n in NODES)

    try:
        # -- home posts both letters and enqueues them for relay-a ---------
        post(home, "a1")
        post(home, "a2")
        with Outbound(home) as outbound:
            outbound.initialize()
            outbound.enqueue("a1")
            outbound.enqueue("a2")
            first_bid, a1_adu = outbound.submit("a1", generation=0, label="home-a1")
            second_bid, a2_adu = outbound.submit("a2", generation=0, label="home-a2")
        lab.event("home-enqueued", bids=[first_bid, second_bid])

        # -- window 1: home -> relay-a (the only open contact) -------------
        delivered = network.contact("home", "relay-a")
        lab.check("window_1_delivers_both_letters", len(delivered) == 2)
        accepted = [receive(relay_a, item["bid"]).outcome for item in delivered]
        lab.check("relay_a_accepts_both_letters", accepted == ["accepted", "accepted"])
        relay_a_receipts = receipt_digests(relay_a)
        lab.event("relay-a-accepted", outcomes=accepted)

        # -- restart relay-a mid-forward -----------------------------------
        # The upstream promise is already committed; the onward obligation is
        # cut in the middle of its durable publication.
        media_items = []
        cut = kill_mid_forward(relay_a, "a1", "postlink")
        lab.check("relay_a_archival_receipts_survive_kill",
                  receipt_digests(relay_a) == relay_a_receipts)
        with Outbound(relay_a) as outbound:
            outbound.initialize()
            # Either the intent became durable and the journal is fenced until
            # its outcome is inspected, or it never landed.  Both are complete;
            # neither is a half-published obligation.
            if outbound.bridge.fenced():
                history = [workflow_journal.decode_record(
                    (outbound.journal.records / name).read_bytes())
                    for name in journal_records(relay_a.workflow)]
                pending = [values for kind, values in history if kind == "enqueue"][-1]
                outbound.journal.recover_intent(pending, "committed")
                cut["resolution"] = "durable-intent-recovered-committed"
            else:
                outbound.enqueue("a1")
                cut["resolution"] = "intent-absent-obligation-reestablished"
            lab.check("relay_a_journal_is_usable_after_recovery",
                      not outbound.bridge.fenced())
            outbound.enqueue("a2")
            cut["work_status_a1"] = outbound.status("a1")
            cut["work_status_a2"] = outbound.status("a2")
            # In the session that RESOLVED the cut the obligation is this
            # session's, whichever branch resolved it: a recovery outcome and
            # a fresh enqueue both put the work into the live image after the
            # open, so ACL2 answers `enqueued` and not `recovered`.
            cut["work_origin_a1_at_recovery"] = outbound.origin("a1")
            cut["records_after_recovery"] = journal_records(relay_a.workflow)
        # The resolving session ends here.  A NEW process is the question the
        # assertion actually asks: does the onward obligation come back out of
        # the journal, or did it only ever exist in the session that repaired
        # the cut?  `recovered` is an answer only replay can produce, and
        # `outstanding` beside it says the work carries no attempt yet.
        with Outbound(relay_a) as outbound:
            outbound.initialize()
            cut["work_origin_a1_after_reopen"] = outbound.origin("a1")
            cut["work_status_a1_after_reopen"] = outbound.status("a1")
            cut["work_origin_a2_after_reopen"] = outbound.origin("a2")
            lab.check("relay_a_onward_obligation_recoverable_after_kill",
                      cut["work_origin_a1_at_recovery"] == "enqueued"
                      and cut["work_origin_a1_after_reopen"] == "recovered"
                      and cut["work_status_a1_after_reopen"] == "outstanding")
            # The carried hop is a submission like any other: the attempt is
            # durable before a byte is written to the volume.  The carried
            # item takes the bundle octets too, so the importing node derives
            # the identity from the same evidence a network receiver would.
            for index, key in enumerate(("a1", "a2"), start=1):
                identity, adu = outbound.submit(
                    key, generation=0, label=f"media-{key}",
                    carrier=lambda _adu, _label, key=key:
                        f"media:volume-1:{relay_a.work_id(key)}")
                media_items.append((identity, adu,
                                    lab_bundle_octets(f"{relay_a.name}/media",
                                                      MEDIA_SEQUENCE_BASE + index)))
        lab.event("relay-a-killed-mid-forward", **cut)
        lab.check("relay_a_archival_receipts_unchanged_by_recovery",
                  receipt_digests(relay_a) == relay_a_receipts)

        # -- the carried-media hop: relay-a -> relay-b ---------------------
        # No contact window is open for this hop at all.
        media_root = run / "media" / "volume-1"
        exported = media.export_media(media_root=media_root, media_id="volume-1",
                                      items=media_items)
        before = media.media_digest(media_root)
        lab.event("media-exported", media_id=exported.media_id,
                  manifest_sha256=exported.manifest_sha256,
                  items=[{"bid": i.bid, "octets": i.octets, "sha256": i.sha256}
                         for i in exported.items])
        imported = media.import_media(
            media_root=media_root, store_root=relay_b.store, inbox_root=relay_b.inbox,
            receipt_root=relay_b.receipts, consumed_root=relay_b.consumed,
            source_eid="dtn://relay-a/media")
        lab.check("media_hop_accepts_both_letters",
                  [o.outcome for o in imported] == ["accepted", "accepted"])
        lab.check("carried_media_is_not_modified_by_import",
                  media.media_digest(media_root) == before)
        relay_b_receipts = receipt_digests(relay_b)
        lab.event("media-imported", outcomes=[o.outcome for o in imported],
                  consumed=media.consumed_identities(relay_b.consumed))

        # -- lose a receipt and regenerate it ------------------------------
        # The first import's receipt bytes are deliberately dropped; the same
        # read-only media is re-imported and must regenerate them exactly.
        lost = imported[0].receipt_sha256
        again = media.import_media(
            media_root=media_root, store_root=relay_b.store, inbox_root=relay_b.inbox,
            receipt_root=relay_b.receipts, consumed_root=relay_b.consumed,
            source_eid="dtn://relay-a/media")
        lab.check("media_reimport_is_duplicate_not_a_second_acceptance",
                  [o.outcome for o in again] == ["duplicate", "duplicate"])
        lab.check("lost_receipt_regenerates_byte_identically",
                  again[0].receipt_sha256 == lost and lost != "")
        lab.check("reimport_adds_no_receipt_record",
                  receipt_digests(relay_b) == relay_b_receipts)
        lab.event("receipt-lost-and-regenerated", receipt_sha256=lost)

        # -- expire an attempt, retry under the next window ----------------
        with Outbound(relay_b) as outbound:
            outbound.initialize()
            outbound.enqueue("a1")
            outbound.enqueue("a2")
            # The attempt carries the CONFIGURED lifetime: fn-bp-record-contextp
            # requires the attempt record's bp-lifetime to equal the config's,
            # so a submission cannot quietly shorten its own expiry.  The
            # window is closed for longer than that lifetime instead.
            expiring_bid, _ = outbound.submit("a1", generation=0,
                                              label="relay-b-a1-expiring")
        dropped = relay_b.bpa.advance(LIFETIME + 1)
        lab.check("attempt_expires_while_no_contact_is_open", dropped == [expiring_bid])
        with Outbound(relay_b) as outbound:
            lab.check("expired_attempt_leaves_the_work_outstanding",
                      outbound.status("a1") not in ("", "absent", "unknown"))
            outbound.request_retry("a1", previous_generation=0)
            retry_bid, retry_adu = outbound.submit("a1", generation=1, label="relay-b-a1-retry")
            other_bid, _ = outbound.submit("a2", generation=0, label="relay-b-a2")
        lab.check("retry_uses_a_distinct_transport_identity", retry_bid != expiring_bid)
        lab.event("attempt-expired-and-retried", expired=expiring_bid, retry=retry_bid)

        # -- window 2: relay-b -> destination, reordered, with a duplicate --
        origin_article = {retry_bid: "a1", other_bid: "a2"}
        delivered = network.contact("relay-b", "destination", reorder=True, duplicate=True)
        lab.check("window_2_delivers_a_reordered_pair_and_a_duplicate",
                  len(delivered) == 4)
        order = [origin_article[item["from_bid"]] for item in delivered]
        lab.check("the_pair_reaches_the_destination_in_the_reverse_of_its_submission_order",
                  order[0] == "a2" and order[-1] == "a1")
        outcomes, midpoint = [], None
        for item in delivered:
            outcomes.append(receive(destination, item["bid"]).outcome)
            if midpoint is None:
                # The destination's allocation frontier right after its first
                # acceptance: that acceptance took the number below it.
                midpoint = snapshot(destination)["group_next"]
        lab.check("destination_accepts_each_letter_once_and_calls_the_rest_duplicates",
                  outcomes.count("accepted") == 2 and outcomes.count("duplicate") == 2)
        report["destination_frontier_after_first_acceptance"] = midpoint
        lab.event("destination-received", order=order, outcomes=outcomes)

        # -- what every node holds -----------------------------------------
        states = {name: snapshot(node) for name, node in nodes.items()}
        report["node_states"] = states
        letters = {name: state["group_next"] for name, state in states.items()}
        lab.check("destination_holds_exactly_one_acceptance_per_article",
                  states["destination"]["articles"] == 2
                  and states["destination"]["records"] == 2)
        lab.check("destination_holds_exactly_one_archive_pin_per_article",
                  states["destination"]["pins"] == 2)
        lab.check("every_node_holds_the_exact_article_bytes",
                  all(all(state["exact_articles"].values()) for state in states.values()))
        # Local numbers stay local.  Each node's allocation frontier advanced
        # only by its own acceptances, and the frontier at each acceptance is
        # the number that acceptance took.  home posted a1 first, so a1 is
        # home's number 1; the destination accepted a2 first, so at the
        # destination a2 is number 1 and a1 is number 2.  No node imported a
        # number from the node that sent it the letter.
        frontier = {name: max(int(v) for v in letters[name].values()) for name in NODES}
        lab.check("each_node_advanced_only_by_its_own_acceptances",
                  all(frontier[name] == states[name]["articles"] + 1 for name in NODES))
        lab.check("the_same_letter_carries_a_different_local_number_at_home_and_destination",
                  order[0] == "a2" and max(int(v) for v in midpoint.values()) == 2
                  and frontier["destination"] == 3)
        report["local_number_frontiers"] = frontier

        # -- relay kinds: archival asserted, forwarding proposed ------------
        report["relay_kinds"] = {
            "archived": {
                "status": "asserted",
                "what": "each relay committed a receipt for content it durably "
                        "holds, regenerated it byte-identically after a lost "
                        "receipt, and kept its archive pin across a SIGKILL",
            },
            "forwarding": {
                "status": "proposal",
                "what": "books/relay.lisp's :forwarding kind, its "
                        "fn-relay-record-undertaking ledger and the proposed "
                        "FNWF (:relay-undertaking upstream onward) record have "
                        "no host wiring and no byte grammar, so this lab "
                        "enqueues the onward work through the ordinary sender "
                        "path and asserts nothing about an accepted forwarding "
                        "responsibility",
            },
        }
        report["bpa_events"] = network.events()
        report["contact_log"] = network.log
        report["receipts"] = {name: receipt_digests(node) for name, node in nodes.items()}
        report["journals"] = {name: journal_records(node.workflow) for name, node in nodes.items()}
        report["status"] = "passed"
    except BaseException as error:
        report.update(status="failed", error=repr(error))
        raise
    finally:
        report["seconds"] = round(time.monotonic() - started, 1)
        report["source_after_sha256"] = source_snapshot()
        report["sources_unchanged"] = report["source_sha256"] == report["source_after_sha256"]
        if not report["sources_unchanged"]:
            report.update(status="failed", error="sources changed during the lab run")
        report["limitations"] = [
            "The mock BPA is a laboratory contact scheduler, not BPv7: no "
            "convergence layer, routing or status reports, and every bundle "
            "carries a primary block and nothing else. The primary block is "
            "real -- ACL2 encodes it and ACL2 derives the staging identity "
            "from it -- so the duplicate and redelivery behaviour here is "
            "fn's; the scheduling around it is not an interoperability "
            "result, and the pinned-dtn7-rs run is separate.",
            "A relay is receiver-then-sender through two host paths. No relay "
            "receipt kind is emitted, so no accepted forwarding responsibility "
            "(SCN-001) is demonstrated; the forwarding undertaking is a proposal.",
            "run_bp_receive carries one destination EID, policy and issuer, so "
            "all four nodes present the same application endpoint identity.",
            "Trusted local A-POLICY: unsigned receipts, no authenticated peer.",
            "Real local process death (SIGKILL of a created process group) and "
            "real filesystem recovery; no power-loss or media-hardware claim.",
            "Contact windows are explicit and never overlap by construction; "
            "this is not a scheduler, liveness or fairness result.",
        ]
        (run / "evidence.json").write_text(
            json.dumps(report, indent=1, sort_keys=True) + "\n")
    return report


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if "--child" in argv:
        return child_main(argv)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-base", type=Path, default=ROOT / "build/bp-four-node")
    parser.add_argument("--dtn7-repo", type=Path, default=None,
                        help="optional pinned checkout; unset uses the mock BPA")
    parser.add_argument("--revision", default=None,
                        help="the revision this run is evidence about; a gate "
                             "tree has no git repository to ask, and the lab "
                             "refuses rather than writing \"unknown\". "
                             "FN_GATE_REVISION does the same thing.")
    parser.add_argument("--image", type=Path,
                        default=os.environ.get("FN_NATIVE_BP_NODE_HOST"),
                        help="the DTN developer image for --dtn7-repo mode")
    args = parser.parse_args(argv)
    args.run_base.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix="four-node-", dir=args.run_base)).resolve()
    report = run_lab(run, dtn7_repo=args.dtn7_repo, revision=args.revision,
                     image=args.image)
    print(json.dumps({"status": report["status"], "seconds": report["seconds"],
                      "evidence": str(run / "evidence.json")}))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

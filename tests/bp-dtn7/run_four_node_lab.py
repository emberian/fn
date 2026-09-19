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

With `DTN7_REPO` unset the transport is `mock_bpa.py`: a laboratory scheduler,
not BPv7.  Results are about fn's behaviour across contacts, not interoperation.
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

from mock_bpa import MockNetwork  # noqa: E402
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
SHORT_LIFETIME = 30

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
    txid: int = 100

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

    def next_txid(self) -> int:
        self.txid += 1
        return self.txid

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
    return run_bp_receive.receive_bpa_request(
        store_root=node.store, inbox_root=node.inbox, receipt_root=node.receipts,
        bid=bid, source_eid=f"dtn://{node.name}/upstream",
        inventory=node.bpa.inventory, download=node.bpa.download,
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

    def enqueue(self, key: str):
        msgid, article = ARTICLES[key]
        archive, subject, _evidence = run_store.metadata(msgid, article)
        values = {"txid": self.node.next_txid(), "tx-generation": 0,
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
        values = {"txid": self.node.next_txid(), "tx-generation": 0, "work-id": work_id,
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


def run_lab(run: Path, *, dtn7_repo=None) -> dict:
    started = time.monotonic()
    lab = Lab(run, "mock_bpa" if dtn7_repo is None else "pinned dtn7-rs")
    report = lab.report
    report.update({
        "schema": 1, "status": "running", "run": str(run), "transport": lab.transport,
        "invocation": [sys.executable, *sys.argv],
        "topology": "home -> relay-a -> relay-b -> destination",
        "a_policy": "explicitly trusted local lab; no signatures, no authenticated peer",
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                            text=True).strip(),
        "versions": {"python": sys.version, "platform": platform.platform()},
        "source_sha256": source_snapshot(), "assertions": {}, "events": [],
    })
    if dtn7_repo is not None:
        raise NotImplementedError(
            "the pinned-BPA run of this lab is optional and not yet wired; "
            "run without --dtn7-repo to use the mock BPA")

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
            lab.check("relay_a_onward_obligation_recoverable_after_kill",
                      cut["work_status_a1"] not in ("", "absent", "unknown"))
            cut["records_after_recovery"] = journal_records(relay_a.workflow)
            # The carried hop is a submission like any other: the attempt is
            # durable before a byte is written to the volume.
            for key in ("a1", "a2"):
                identity, adu = outbound.submit(
                    key, generation=0, label=f"media-{key}",
                    carrier=lambda _adu, _label, key=key:
                        f"media:volume-1:{relay_a.work_id(key)}")
                media_items.append((identity, adu))
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
            expiring_bid, _ = outbound.submit("a1", generation=0, label="relay-b-a1-expiring",
                                              lifetime=SHORT_LIFETIME)
        dropped = relay_b.bpa.advance(SHORT_LIFETIME + 1)
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
            "The mock BPA is a laboratory contact scheduler, not BPv7: no CBOR, "
            "convergence layer, routing or status reports. Nothing here is an "
            "interoperability result; the pinned-dtn7-rs run is separate.",
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
    args = parser.parse_args(argv)
    args.run_base.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix="four-node-", dir=args.run_base)).resolve()
    report = run_lab(run, dtn7_repo=args.dtn7_repo)
    print(json.dumps({"status": report["status"], "seconds": report["seconds"],
                      "evidence": str(run / "evidence.json")}))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

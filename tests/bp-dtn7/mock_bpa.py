#!/usr/bin/env python3
"""A file-backed store-and-forward BPA stand-in for the four-node lab.

It offers exactly the surface the fn host uses -- `inventory`, `download`,
`delete` -- plus `submit`, an explicit contact window, a bundle lifetime and a
restart that re-reads its spool from disk.  It decides nothing about articles,
acceptance, receipts, retention or local numbers; those all stay in ACL2 behind
`run_bp_receive` and `run_store`, exactly as with the pinned dtn7-rs BPA.

This is a laboratory scheduling harness, not a BPv7 implementation: there is no
CBOR, no convergence layer, no routing and no status report.  Use it only when
`DTN7_REPO` is unset; a run under it establishes fn-side behaviour across
contacts, not interoperability.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import run_store, workflow_journal  # noqa: E402

MAX_ADU_OCTETS = 65538


class MockBpaError(RuntimeError):
    pass


@dataclass(frozen=True)
class Bundle:
    bid: str
    destination: str
    lifetime: int
    age: int
    payload_sha256: str
    # Spool arrival order.  A store-and-forward queue is first in, first out;
    # the slot name is a digest of the BID, so the directory listing is not.
    sequence: int = 0

    @staticmethod
    def from_document(document: dict) -> "Bundle":
        return Bundle(document["bid"], document["destination"],
                      document["lifetime"], document["age"],
                      document["payload_sha256"], document.get("sequence", 0))


def _durable_write(path: Path, data: bytes) -> None:
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        os.write(fd, data)
        run_store.durable_barrier(fd)
    finally:
        os.close(fd)
    os.replace(temporary, path)
    workflow_journal.fsync_dir(path.parent)


def _slot(bid: str) -> str:
    return hashlib.sha256(bid.encode("ascii", "strict")).hexdigest()


class MockBpa:
    """One node's BPA: a queue it forwards on contact and a local delivery set."""

    def __init__(self, root: Path, name: str, node_eid: str, endpoint: str):
        self.root = Path(root)
        self.name = name
        self.node_eid = node_eid
        self.endpoint = endpoint
        self.queue = self.root / "queue"
        self.local = self.root / "local"
        self.expired = self.root / "expired"
        for directory in (self.root, self.queue, self.local, self.expired):
            directory.mkdir(mode=0o700, parents=True, exist_ok=True)
        self.counter = 0
        self.spool = 0
        self.starts = 1
        self.events: list[dict] = []

    # -- transport bookkeeping -------------------------------------------
    def _note(self, event: str, **fields) -> None:
        self.events.append({"bpa": self.name, "event": event, **fields})

    def restart(self) -> None:
        """Drop every in-memory cache; the spool on disk is the only state."""
        self.starts += 1
        self._note("restart", starts=self.starts)

    def _write(self, directory: Path, bid: str, adu: bytes, destination: str,
               lifetime: int, age: int = 0, sequence: int | None = None) -> None:
        if sequence is None:
            self.spool += 1
            sequence = self.spool
        document = {"bid": bid, "destination": destination, "lifetime": lifetime,
                    "age": age, "payload_sha256": hashlib.sha256(adu).hexdigest(),
                    "sequence": sequence}
        slot = directory / _slot(bid)
        slot.mkdir(mode=0o700, exist_ok=True)
        _durable_write(slot / "payload.adu", adu)
        _durable_write(slot / "bundle.json",
                       json.dumps(document, sort_keys=True).encode("ascii") + b"\n")

    def _read(self, directory: Path, slot: str) -> tuple[Bundle, bytes]:
        document = json.loads((directory / slot / "bundle.json").read_text())
        payload = (directory / slot / "payload.adu").read_bytes()
        bundle = Bundle.from_document(document)
        if hashlib.sha256(payload).hexdigest() != bundle.payload_sha256:
            raise MockBpaError(f"spooled bundle {bundle.bid} is damaged")
        return bundle, payload

    def _entries(self, directory: Path) -> list[tuple[Bundle, bytes, str]]:
        result = []
        for slot in sorted(p.name for p in directory.iterdir() if p.is_dir()):
            bundle, payload = self._read(directory, slot)
            result.append((bundle, payload, slot))
        result.sort(key=lambda entry: (entry[0].sequence, entry[2]))
        return result

    # -- the surface fn uses ---------------------------------------------
    def submit(self, adu: bytes, destination: str, label: str = "",
               lifetime: int = 300) -> str:
        if not isinstance(adu, bytes) or not 0 < len(adu) <= MAX_ADU_OCTETS:
            raise MockBpaError("outbound ADU outside the lab profile")
        self.counter += 1
        bid = f"dtn://{self.name}/-{self.counter}"
        self._write(self.queue, bid, adu, destination, lifetime)
        self._note("submit", bid=bid, destination=destination, label=label,
                   lifetime=lifetime, octets=len(adu))
        return bid

    def inventory(self) -> list[str]:
        return sorted(bundle.bid for bundle, _payload, _slot in self._entries(self.local))

    def download(self, bid: str) -> bytes:
        for bundle, payload, _slot in self._entries(self.local):
            if bundle.bid == bid:
                return payload
        raise MockBpaError(f"no local bundle {bid}")

    def delete(self, bid: str) -> None:
        for _bundle, _payload, slot in self._entries(self.local):
            if _bundle.bid == bid:
                for child in (self.local / slot).iterdir():
                    child.unlink()
                (self.local / slot).rmdir()
                workflow_journal.fsync_dir(self.local)
                self._note("delete", bid=bid)
                return
        raise MockBpaError(f"no local bundle {bid}")

    # -- laboratory scheduling -------------------------------------------
    def queued(self) -> list[str]:
        return sorted(bundle.bid for bundle, _payload, _slot in self._entries(self.queue))

    def _drop_queued(self, slot: str) -> None:
        for child in (self.queue / slot).iterdir():
            child.unlink()
        (self.queue / slot).rmdir()
        workflow_journal.fsync_dir(self.queue)

    def advance(self, seconds: int) -> list[str]:
        """Age every queued bundle; an over-age bundle is dropped, not delivered."""
        dropped = []
        for bundle, payload, slot in self._entries(self.queue):
            age = bundle.age + seconds
            if age > bundle.lifetime:
                self._write(self.expired, bundle.bid, payload, bundle.destination,
                            bundle.lifetime, age, bundle.sequence)
                self._drop_queued(slot)
                dropped.append(bundle.bid)
                self._note("expired", bid=bundle.bid, age=age, lifetime=bundle.lifetime)
            else:
                self._write(self.queue, bundle.bid, payload, bundle.destination,
                            bundle.lifetime, age, bundle.sequence)
        return dropped

    def deliver_into(self, peer: "MockBpa", bundle: Bundle, payload: bytes,
                     bid: str | None = None) -> str:
        peer.counter += 1
        forwarded = bid or f"dtn://{peer.name}/-in-{peer.counter}"
        peer._write(peer.local, forwarded, payload, bundle.destination, bundle.lifetime)
        peer._note("delivered", bid=forwarded, from_bid=bundle.bid, via=self.name)
        return forwarded


class MockNetwork:
    """Contact windows between mock BPAs; only one window is open at a time."""

    def __init__(self, root: Path):
        self.root = Path(root)
        self.root.mkdir(mode=0o700, parents=True, exist_ok=True)
        self.nodes: dict[str, MockBpa] = {}
        self.open_contact: tuple[str, str] | None = None
        self.log: list[dict] = []

    def add(self, name: str, node_eid: str, endpoint: str) -> MockBpa:
        bpa = MockBpa(self.root / f"{name}-bpa", name, node_eid, endpoint)
        self.nodes[name] = bpa
        return bpa

    def contact(self, source: str, target: str, *, duplicate: bool = False,
                reorder: bool = False) -> list[str]:
        """Open one window, forward every queued bundle, then close it.

        Windows never overlap: opening one while another is open is an error,
        so a bundle can only move during its own node pair's window.
        """
        if self.open_contact is not None:
            raise MockBpaError("contact windows must not overlap")
        self.open_contact = (source, target)
        try:
            sender, receiver = self.nodes[source], self.nodes[target]
            entries = sender._entries(sender.queue)
            if reorder:
                entries = list(reversed(entries))
            delivered = []
            for bundle, payload, slot in entries:
                delivered.append({"bid": sender.deliver_into(receiver, bundle, payload),
                                  "from_bid": bundle.bid})
                if duplicate:
                    # A second forwarded copy of the same application bytes
                    # under a fresh transport identity: what fn must recognise.
                    delivered.append({"bid": sender.deliver_into(receiver, bundle, payload),
                                      "from_bid": bundle.bid})
                sender._drop_queued(slot)
            self.log.append({"contact": [source, target], "delivered": delivered,
                             "duplicate": duplicate, "reorder": reorder})
            return delivered
        finally:
            self.open_contact = None

    def events(self) -> list[dict]:
        result: list[dict] = []
        for node in self.nodes.values():
            result.extend(node.events)
        return result

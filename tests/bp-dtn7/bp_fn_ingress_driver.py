#!/usr/bin/env python3
"""Drive one real BPA bundle through the isolated ACL2 ingress host twice.

The bounded local HTTP client downloads a raw bundle non-destructively. A small
helper uses the pinned upstream BP decoder to extract its ADU. Article
interpretation and Store admission remain in run_bp_ingress's ACL2 path.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


MAX_BID_OCTETS = 512
MAX_ADU_BYTES = 32768


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_ingress(path: Path):
    tools = str(path / "tools")
    if tools not in sys.path:
        sys.path.insert(0, tools)
    import run_bp_ingress
    return run_bp_ingress


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ingress-root", required=True, type=Path)
    parser.add_argument("--workflow-journal", required=True, type=Path)
    parser.add_argument("--store", required=True, type=Path)
    parser.add_argument("--journal", required=True, type=Path)
    parser.add_argument("--bpa-bin", required=True, type=Path)
    parser.add_argument("--bpa-tools", required=True, type=Path)
    parser.add_argument("--bpa-extractor", required=True, type=Path)
    parser.add_argument("--bpa-port", required=True, type=int)
    parser.add_argument("--bid", required=True)
    parser.add_argument("--expected-adu", required=True, type=Path)
    parser.add_argument("--expected-msgid", required=True)
    parser.add_argument("--destination", required=True)
    parser.add_argument("--source-eid", required=True)
    parser.add_argument("--lifetime", required=True, type=int)
    parser.add_argument("--artifact-dir", required=True, type=Path)
    parser.add_argument("--phase", required=True, choices=("accept", "duplicate"))
    parser.add_argument("--baseline", type=Path,
                        help="accepted-state JSON required for duplicate comparison")
    args = parser.parse_args()

    if len(args.bid.encode("ascii", "strict")) > MAX_BID_OCTETS:
        raise ValueError("BPA BID exceeds lab boundary")
    if not args.expected_adu.is_file():
        raise ValueError("missing legacy ADU input")
    expected = args.expected_adu.read_bytes()
    if not expected or len(expected) > MAX_ADU_BYTES:
        raise ValueError("legacy article ADU exceeds lab boundary")
    sys.path.insert(0, str(args.bpa_tools.resolve()))
    import bpa_dtn7
    ingress = load_ingress(args.ingress_root.resolve())
    # The ingress bridge recovers an existing concrete Store image.  This lab
    # owns only the initial empty-image setup; every subsequent open, recovery,
    # allocation, and acceptance decision is the existing Store/ACL2 path.
    if not args.store.exists():
        ingress.run_store.Store(args.store, writable=True).initialize()
    args.artifact_dir.mkdir(parents=True, exist_ok=True)

    client = bpa_dtn7.BpaDtn7Client(args.bpa_port, max_bundle_bytes=64 * 1024)

    def inventory() -> list[str]:
        return list(client.inventory())

    def download(bid: str) -> bytes:
        # Network response is bounded before allocation by bpa_dtn7.  The
        # pinned helper then uses the same upstream bp7 parser as dtnrecv on
        # an already bounded local raw file; it does not implement a codec.
        with tempfile.TemporaryDirectory(prefix="fn-bp-download-", dir=args.artifact_dir) as temporary:
            root = Path(temporary); raw_path = root / "bundle.cbor"; adu_path = root / "adu.bin"
            raw_path.write_bytes(client.download_bundle(bid))
            completed = subprocess.run([str(args.bpa_extractor), "--input", str(raw_path),
                                        "--output", str(adu_path), "--max-payload", "32768"],
                                       stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=10)
            if completed.returncode != 0:
                raise RuntimeError("pinned BP payload extractor refused downloaded bundle")
            value = adu_path.read_bytes()
            if not value or len(value) > 32768:
                raise RuntimeError("extracted ADU violates ingress bound")
            return value

    def delete(bid: str) -> None:
        client.delete(bid)

    def state_snapshot(label: str) -> dict[str, object]:
        store, bridge, records = ingress.open_live_bp_store(args.store, writable=False)
        try:
            payload = bridge.lookup(args.expected_msgid.encode("ascii", "strict"))
            snapshot = {
                "label": label,
                "records": len(records),
                "articles": bridge.article_count(),
                "pins": bridge.pin_count(),
                "payload_sha256": hashlib.sha256(payload).hexdigest(),
                "payload_matches": payload == expected,
            }
        finally:
            bridge.close()
            store.close()
        if snapshot["records"] != 1 or snapshot["articles"] != 1 or not snapshot["payload_matches"]:
            raise RuntimeError(f"unexpected Store state after {label}: {snapshot}")
        return snapshot

    if args.bid not in inventory():
        raise RuntimeError("BPA BID absent before ingress")
    result = ingress.ingest_bpa_adu(
        store_root=args.store, journal_root=args.journal,
        journal_module_path=args.workflow_journal, bid=args.bid,
        inventory=inventory, download=download, delete=delete,
        destination=args.destination, source_eid=args.source_eid, lifetime=args.lifetime)
    expected_outcome = "accepted" if args.phase == "accept" else "duplicate"
    if result.outcome != expected_outcome or args.bid in inventory():
        raise RuntimeError(f"{args.phase} ingress/delete did not complete: {result.outcome}")
    snapshot = state_snapshot(args.phase)
    if args.phase == "duplicate":
        if args.baseline is None or not args.baseline.is_file():
            raise ValueError("duplicate phase requires accepted-state baseline")
        baseline = json.loads(args.baseline.read_text())["state"]
        if {key: snapshot[key] for key in ("records", "articles", "pins", "payload_sha256")} != \
           {key: baseline[key] for key in ("records", "articles", "pins", "payload_sha256")}:
            raise RuntimeError("exact duplicate changed article or retention state")

    report = {
        "schema": 1,
        "phase": args.phase,
        "outcome": result.outcome,
        "bid": args.bid,
        "destination": args.destination,
        "source_eid": args.source_eid,
        "lifetime": args.lifetime,
        "expected_adu_sha256": hashlib.sha256(expected).hexdigest(),
        "ingress_tool_sha256": sha256(args.ingress_root / "tools" / "run_bp_ingress.py"),
        "workflow_journal_sha256": sha256(args.workflow_journal),
        "state": snapshot,
        "endpoint_pop_used": False,
        "receipt_emitted": False,
    }
    (args.artifact_dir / f"fn-ingress-{args.phase}.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

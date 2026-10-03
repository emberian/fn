#!/usr/bin/env python3
"""SCN-1085: exact sparse NEWNEWS, tombstones, competing work and reopen.

The plan names literal fixture memberships; native fn alone performs posting,
expiry, discovery and reclamation. Payload-I/O attribution is unavailable.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import sys
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tests.native_harness import Client, EXIT, Node, runtime_sbcl
from tests.test_native_expiry import PAST, article
from tools.native_env import image_identity
from tools.native_mixed_workload import Recorder, Resources, percentile, wire_outcome
from tools.resilience.adapters.native_cuts import served_matches
from tools.resilience.adapters.page_io import file_hash

MATCH, OTHER = "fn.sparse.match", "fn.sparse.other"
COMMAND = "NEWNEWS fn.sparse.match 19700101 000000 GMT"


def recipe():
    return dict(schema=1, seed=0, groups=[MATCH, OTHER],
                initial=[f"sparse-{i}" for i in range(24)],
                matching=["sparse-0", "sparse-4", "sparse-8", "sparse-12", "sparse-16", "sparse-20"],
                tombstones=["sparse-0", "sparse-12"],
                expected=["sparse-4", "sparse-8", "sparse-16", "sparse-20"],
                competing_posts=[f"other-{i}" for i in range(4)], discovery_repetitions=8,
                read_tags=["sparse-4", "sparse-8", "sparse-16", "sparse-20"] * 2,
                command=COMMAND, profile="native default; explicit operator init recorded")


def mid(tag):
    return "<xpy-%s@example.invalid>" % tag


def run(image, image_source, work):
    work.mkdir(parents=True, exist_ok=False)
    plan = recipe()
    rec = Recorder("sparse-newnews")
    case = unittest.TestCase()
    node = Node(case, image, root=work / "node")
    gate = threading.Barrier(4)
    resources = None
    failure = None
    cleanup_errors = []
    started = datetime.now(timezone.utc).isoformat()
    expected = {mid(tag).encode("ascii") for tag in plan["expected"]}
    sources = {tag: article(tag, MATCH if tag in plan["matching"] else OTHER,
                            PAST if tag in plan["tombstones"] else None, 1560)
               for tag in plan["initial"]}
    accepted = []
    served_hashes = {}

    def post(client, tag, source, phase):
        begun = time.monotonic()
        try:
            first, final = client.post(source)
        except (OSError, EOFError) as error:
            rec.event("client", "post", tag=tag, phase=phase, outcome="uncertain",
                      diagnostic=str(error), latency_s=time.monotonic() - begun,
                      source_sha256=hashlib.sha256(source).hexdigest())
            raise
        reply = final if final is not None else first
        outcome = "uncertain" if final == b"" else wire_outcome(reply)
        rec.event("client", "post", tag=tag, phase=phase, outcome=outcome,
                  reply=reply.decode("ascii", "replace"), latency_s=time.monotonic() - begun,
                  source_sha256=hashlib.sha256(source).hexdigest())
        if outcome != "accepted":
            raise AssertionError(f"POST {tag}: {outcome}: {reply!r}")
        accepted.append(tag)

    def discovery(client, phase):
        begun = time.monotonic()
        status = client.command(COMMAND)
        if not status.startswith(b"230 "):
            rec.event("client", "newnews", phase=phase, status=status.decode("ascii", "replace"),
                      outcome="refused" if status.startswith(b"403") else "fault")
            raise AssertionError(f"complete NEWNEWS unavailable: {status!r}")
        rows = client.block().splitlines()
        rec.event("client", "newnews", phase=phase, outcome="accepted", rows=[r.decode("ascii") for r in rows],
                  latency_s=time.monotonic() - begun)
        if set(rows) != expected or len(rows) != len(expected):
            raise AssertionError(f"sparse NEWNEWS mismatch: {rows!r}; expected {sorted(expected)!r}")
        if not client.command("DATE").startswith(b"111 "):
            raise AssertionError("discovery connection did not progress after complete block")

    def read(client, tag, phase):
        begun = time.monotonic()
        data = client.article(mid(tag))
        if data is None or not served_matches(data, sources[tag]):
            raise AssertionError(f"retained ARTICLE changed/unavailable: {tag}")
        digest = hashlib.sha256(data).hexdigest()
        if tag in served_hashes and served_hashes[tag] != digest:
            raise AssertionError(f"served bytes changed across reopen: {tag}")
        served_hashes[tag] = digest
        rec.event("client", "read", tag=tag, phase=phase, outcome="accepted", served_sha256=digest,
                  latency_s=time.monotonic() - begun)

    def actor(name):
        gate.wait(timeout=30)
        if name == "maintenance":
            begun = time.monotonic()
            result = node.operator("store", "reclaim", timeout=120, expect=None)
            rec.event("environment", "live-reclaim", returncode=result.returncode,
                      stdout=result.stdout.decode("utf-8", "replace"), stderr=result.stderr.decode("utf-8", "replace"),
                      latency_s=time.monotonic() - begun)
            if result.returncode not in (EXIT.OK, EXIT.REFUSED):
                raise AssertionError(f"live reclaim uncertain/fault: {result.returncode}")
            return
        with Client(node.port, timeout=30) as client:
            if name == "discovery":
                for _ in range(plan["discovery_repetitions"]):
                    discovery(client, "competing")
            elif name == "reader":
                for tag in plan["read_tags"]:
                    read(client, tag, "competing")
            else:
                for tag in plan["competing_posts"]:
                    source = article(tag, OTHER, pad=1560)
                    sources[tag] = source
                    post(client, tag, source, "competing")

    try:
        result = node.operator("init", MATCH, OTHER, timeout=600, expect=None)
        rec.event("environment", "init", returncode=result.returncode,
                  stdout=result.stdout.decode("utf-8", "replace"), stderr=result.stderr.decode("utf-8", "replace"))
        if result.returncode != EXIT.OK:
            raise AssertionError("native profile/init unavailable")
        node.start(timeout=600)
        resources = Resources(node)
        resources.begin()
        with Client(node.port, timeout=30) as client:
            for tag in plan["initial"]:
                post(client, tag, sources[tag], "seed")
        resources.phase = "offline-expiry"
        node.stop(grace=120)
        node.operator("retention", "expire", MATCH, "purge", "30", expect=EXIT.OK)
        result = node.operator("store", "reclaim", timeout=600, expect=None)
        rec.event("environment", "offline-expiry", returncode=result.returncode,
                  stdout=result.stdout.decode("utf-8", "replace"), stderr=result.stderr.decode("utf-8", "replace"))
        if result.returncode != EXIT.OK:
            raise AssertionError("actual tombstone construction unavailable")
        node.start(timeout=600)
        resources.phase = "competing-discovery"
        with Client(node.port, timeout=30) as client:
            for tag in plan["tombstones"]:
                status = client.command("STAT " + mid(tag))
                rec.event("client", "tombstone", tag=tag, status=status.decode("ascii", "replace"))
                if not status.startswith(b"430 article reclaimed"):
                    raise AssertionError(f"no actual tombstone: {tag}: {status!r}")
            discovery(client, "cold-connection")
        with ThreadPoolExecutor(max_workers=4) as pool:
            futures = [pool.submit(actor, name) for name in ("discovery", "reader", "poster", "maintenance")]
            for future in futures:
                future.result(timeout=150)
        node.stop(grace=120)
        resources.phase = "recovery-and-verification"
        node.start(timeout=600)
        with Client(node.port, timeout=30) as client:
            discovery(client, "reopened")
            for tag in accepted:
                if tag in plan["tombstones"]:
                    status = client.command("STAT " + mid(tag))
                    rec.event("client", "tombstone", tag=tag, phase="reopened", status=status.decode("ascii", "replace"))
                    if not status.startswith(b"430 article reclaimed"):
                        raise AssertionError(f"tombstone changed across reopen: {tag}")
                else:
                    read(client, tag, "reopened")
    except Exception as error:
        gate.abort()
        failure = dict(exception=type(error).__name__, diagnostic=str(error))
        rec.event("environment", "run-failed", **failure)
    finally:
        peaks = resources.end() if resources else None
        try:
            if not case.doCleanups():
                cleanup_errors.append("fixture cleanup failed")
        except Exception as error:
            cleanup_errors.append(str(error))
        for index, process in enumerate(node.processes):
            (work / f"owner-{index}.stdout").write_bytes(process.stdout.since(0))
            (work / f"owner-{index}.stderr").write_bytes(process.stderr.since(0))
            if process.stdout.dropped or process.stderr.dropped:
                cleanup_errors.append(f"owner-{index} diagnostics truncated")
    rec.journal.write(work / "journal.jsonl")
    (work / "plan.json").write_text(json.dumps(plan, indent=2) + "\n")
    events = rec.journal.records
    latencies = [r["latency_s"] for r in events if r.get("event") == "newnews" and "latency_s" in r]
    summary = dict(verdict="failed" if failure or cleanup_errors else "passed", failure=failure,
                   cleanup_errors=cleanup_errors, accepted_posts=len(accepted),
                   tombstone_payload_io_attribution="unavailable: no per-command primitive observer",
                   resources=peaks, newnews_samples=len(latencies),
                   newnews_latency_s={name: percentile(latencies, q) for name, q in (("p50", .5), ("p95", .95), ("p99", .99))},
                   maintenance=[r for r in events if r.get("event") == "live-reclaim"], journal_digest=rec.journal.digest())
    (work / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    runtime = runtime_sbcl(image)
    manifest = dict(image_identity=image_identity(image, source=image_source), host=platform.uname()._asdict(),
                    started_utc=started, finished_utc=datetime.now(timezone.utc).isoformat(),
                    runtime=runtime[0] if runtime else None, python=sys.version, plan_seed=plan["seed"],
                    harness_source=os.environ.get("FN_MIXED_TOOL_SOURCE", "unavailable"),
                    inputs={p: file_hash(ROOT / p) for p in ("tools/native_sparse_newnews.py", "tools/native_mixed_workload.py",
                            "tests/native_harness.py", "tests/test_native_expiry.py", "tools/resilience/adapters/native_cuts.py")})
    (work / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--image", type=Path, required=True)
    parser.add_argument("--image-source", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    summary = run(args.image.resolve(), args.image_source, args.out.resolve())
    print(json.dumps(summary, indent=2))
    return 0 if summary["verdict"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Replayable workload against a scratch native fn, never a semantic simulation.

Run paired baseline/slow-reader cases on one image and profile. The plan fixes
actor requests and phase barriers; the sealed journal records the realized
concurrent order. Replay does not promise an identical OS thread schedule.
"""
from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import json
import hashlib
import os
from pathlib import Path
import platform
import random
import re
import subprocess
import sys
import threading
import time
import unittest
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tests.native_harness import Client, EXIT, Node, article, runtime_sbcl
from tools.native_env import image_identity
from tools.resilience.adapters.native_cuts import served_matches
from tools.resilience.adapters.page_io import file_hash
from tools.resilience.journal import Journal

GROUP = "fn.test"
# Matched modest profile for both cases; admission remains the image's decision.
PROFILE = ["--max-transactions", "8192", "--max-history-octets", "33554432",
           "--max-record-octets", "196608", "--max-article-octets", "32768",
           "--max-groups-per-article", "16", "--max-open-suffix", "8192"]


def plan(seed=19, initial=24, writers=3, posts=8, reads=12):
    rng = random.Random(seed)
    prior = [f"seed-{i}" for i in range(initial)]
    return dict(schema=1, seed=seed, profile=PROFILE, initial=prior,
                writers={f"writer-{i}": [f"post-{i}-{j}" for j in range(posts)]
                         for i in range(writers)},
                readers={kind: [rng.choice(prior) for _ in range(reads)]
                         for kind in ("warm", "cold", "slow")},
                maintenance=["checkpoint", "reclaim"],
                barriers=["seed-durable", "actors-ready", "mixed-finished", "reopened"])


def message_id(tag):
    return f"<mixed-{tag}@empirical.invalid>"


def payload(tag):
    # Unknown header and dot-leading body exercise byte preservation/framing.
    return article(message_id(tag), groups=GROUP, subject="mixed " + tag,
                   body=("body " + tag + "\r\n.dot line\r\n" + "q" * 76 + "\r\n") * 24,
                   headers=("X-Empirical: " + tag,))


def wire_outcome(reply):
    """Observe outcome spelling, preserving uncertainty before status classes."""
    if b"uncertain" in reply.lower():
        return "uncertain"
    if reply.startswith(b"240"):
        return "accepted"
    if reply.startswith(b"403") or b"fault" in reply.lower():
        return "fault"
    return "refused"


def percentile(values, q):
    if not values:
        return None
    ordered = sorted(values)
    return ordered[min(len(ordered) - 1, round(q * (len(ordered) - 1)))]


class Recorder:
    def __init__(self, scenario):
        self.journal = Journal(scenario)
        self.lock = threading.Lock()
        self.start = time.monotonic()

    def event(self, kind, event, **fields):
        with self.lock:
            return self.journal.append(kind, event=event,
                                       elapsed_s=time.monotonic() - self.start, **fields)


class Resources:
    """Sampled peaks, owner only; disk apparent/allocated bytes, never a bound."""
    def __init__(self, node):
        self.node = node
        self.done = threading.Event()
        self.samples = []
        self.errors = []
        self.phase = "seed-and-mixed"
        self.thread = threading.Thread(target=self.run, daemon=True)

    def run(self):
        while not self.done.is_set():
            try:
                pid = self.node.process.pid
                status = Path(f"/proc/{pid}/status")
                rss = hwm = fds = None
                if status.exists():
                    rows = dict(re.findall(r"^(VmRSS|VmHWM):\s+(\d+) kB", status.read_text(), re.M))
                    rss, hwm = (int(rows[k]) if k in rows else None for k in ("VmRSS", "VmHWM"))
                    fds = len(list(Path(f"/proc/{pid}/fd").iterdir()))
                else:
                    value = subprocess.check_output(["ps", "-o", "rss=", "-p", str(pid)], text=True).strip()
                    rss = int(value) if value else None
                sizes = [p.stat() for p in self.node.store_path.rglob("*") if p.is_file()]
                self.samples.append(dict(t=time.monotonic(), pid=pid, phase=self.phase, rss_kib=rss, hwm_kib=hwm,
                                         fd_count=fds, disk_bytes=sum(s.st_size for s in sizes),
                                         disk_allocated_bytes=sum(s.st_blocks * 512 for s in sizes)))
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                self.errors.append(dict(t=time.monotonic(), pid=pid,
                                        phase=self.phase, diagnostic=str(error)))
            self.done.wait(0.1)

    def begin(self):
        self.thread.start()

    def end(self):
        self.done.set()
        self.thread.join(timeout=10)
        keys = ("rss_kib", "hwm_kib", "fd_count", "disk_bytes", "disk_allocated_bytes")
        def peaks(samples):
            return {key: max((s[key] for s in samples if s[key] is not None), default=None) for key in keys}
        return dict(interval_s=0.1, scope="both owner lifetimes and store; sampled peaks, split by PID",
                    samples=len(self.samples), errors=self.errors,
                    peaks=peaks(self.samples),
                    owners={str(pid): dict(samples=sum(s["pid"] == pid for s in self.samples),
                                           peaks=peaks([s for s in self.samples if s["pid"] == pid]))
                            for pid in sorted({s["pid"] for s in self.samples})})


def read_exact(client, tag, delay=0):
    status = client.command("ARTICLE " + message_id(tag))
    if not status.startswith(b"220"):
        raise AssertionError(f"ARTICLE {tag}: {status!r}")
    chunks = []
    while True:
        line = client.line()
        if line == b".\r\n":
            break
        chunks.append(line[1:] if line.startswith(b"..") else line)
        if delay:
            time.sleep(delay)
    data = b"".join(chunks)
    if not served_matches(data, payload(tag)):
        raise AssertionError(f"ARTICLE {tag}: source bytes changed")
    return data


def number(client, tag):
    # GROUP selects the numbering coordinate, then STAT Message-ID observes it.
    group = client.command("GROUP " + GROUP)
    if not group.startswith(b"211"):
        raise AssertionError(repr(group))
    status = client.command("STAT " + message_id(tag))
    if not status.startswith(b"223"):
        raise AssertionError(repr(status))
    return int(status.split()[1])


def wait_checkpoint(owner, previous, deadline):
    end = time.monotonic() + deadline
    while time.monotonic() < end:
        rows = re.findall(rb"CHECKPOINT auto sequence=([0-9]+) [^\n]*", owner.stderr.since(0))
        if len(rows) > previous:
            return int(rows[-1])
        if owner.poll() is not None:
            raise AssertionError("owner died before checkpoint publication")
        time.sleep(0.05)
    raise AssertionError("accepted checkpoint request produced no publication within experiment budget")


def check_history(journal, recipe):
    """Check observed promises and complete workload, independent of log diagnostics."""
    records = journal.records
    posts = [r for r in records if r.get("event") == "post" and r.get("outcome") == "accepted"]
    intended = recipe["initial"] + [tag for tags in recipe["writers"].values() for tag in tags]
    if Counter(r["tag"] for r in posts) != Counter(intended):
        raise AssertionError("accepted client history differs from complete intended workload")
    before = {r["tag"]: (r["number"], r["served_sha256"])
              for r in records if r.get("event") == "verified"}
    after_rows = [r for r in records if r.get("event") == "recovered"]
    after = {r["tag"]: (r["number"], r["served_sha256"]) for r in after_rows}
    if len(after_rows) != len(intended) or set(before) != set(intended) or before != after:
        raise AssertionError("recovered client bytes/numbers differ from acknowledged verified history")
    if len(set(n for n, _ in after.values())) != len(after):
        raise AssertionError("recovered client history reused local numbers")
    for actor, tags in recipe["readers"].items():
        reads = [r for r in records if r.get("event") == "read" and r.get("actor") == actor]
        if [r["tag"] for r in reads] != tags or any(r.get("result") != "match" for r in reads):
            raise AssertionError("incomplete or incorrect reader history: " + actor)


def run_case(image, image_source, work, recipe, mode, deadline=120):
    work.mkdir(parents=True, exist_ok=False)
    rec = Recorder("mixed-" + mode)
    started_utc = datetime.now(timezone.utc).isoformat()
    case = unittest.TestCase()
    node = Node(case, image, root=work / "node")
    resources = None
    failure = None
    cleanup_errors = []
    coverage_gaps = []
    accepted = {}
    durable_hashes = {}
    actor_ready = threading.Barrier(len(recipe["writers"]) + len(recipe["readers"]) + 1)
    stop = threading.Event()
    def observed_post(client, tag, actor, phase):
        begun = time.monotonic()
        try:
            first, final = client.post(payload(tag))
            reply = final or first
            outcome = wire_outcome(reply)
            rec.event("client", "post", actor=actor, phase=phase, tag=tag,
                      outcome=outcome, reply=reply.decode("ascii", "replace"),
                      latency_s=time.monotonic() - begun)
            if outcome == "accepted":
                with rec.lock:
                    accepted[tag] = None
            else:
                raise AssertionError(f"POST {tag}: {outcome}: {reply!r}")
        except (OSError, EOFError) as error:
            rec.event("client", "post", actor=actor, phase=phase, tag=tag,
                      outcome="uncertain", diagnostic=str(error), latency_s=time.monotonic() - begun)
            raise

    def writer(actor, tags):
        with Client(node.port, timeout=deadline) as client:
            actor_ready.wait(timeout=deadline)
            for tag in tags:
                if stop.is_set():
                    return
                observed_post(client, tag, actor, "mixed")

    def reader(actor, tags):
        with Client(node.port, timeout=deadline) as warm:
            actor_ready.wait(timeout=deadline)
            for tag in tags:
                if stop.is_set():
                    return
                begun = time.monotonic()
                if actor == "cold":
                    with Client(node.port, timeout=deadline) as cold:
                        data = read_exact(cold, tag)
                else:
                    data = read_exact(warm, tag, 0.001 if actor == "slow" and mode == "slow" else 0)
                rec.event("client", "read", actor=actor, phase="mixed", tag=tag,
                          result="match", served_sha256=hashlib.sha256(data).hexdigest(),
                          latency_s=time.monotonic() - begun)

    try:
        rec.event("stage", "setup-begun")
        initialized = node.operator("init", *recipe["profile"], GROUP, timeout=600)
        rec.event("environment", "init", returncode=initialized.returncode,
                  stdout=initialized.stdout.decode("utf-8", "replace"),
                  stderr=initialized.stderr.decode("utf-8", "replace"))
        if initialized.returncode != EXIT.OK:
            raise AssertionError("profile init refused/faulted; see trace")
        boot_begun = time.monotonic()
        node.start(timeout=600)
        rec.event("environment", "owner-ready", pid=node.process.pid,
                  boot_s=time.monotonic() - boot_begun, opening="initial")
        resources = Resources(node)
        resources.begin()
        with Client(node.port, timeout=deadline) as client:
            for tag in recipe["initial"]:
                observed_post(client, tag, "seed", "setup")
            for tag in recipe["initial"]:
                accepted[tag] = number(client, tag)
        rec.event("stage", "seed-durable")
        started = time.monotonic()
        with ThreadPoolExecutor(max_workers=len(recipe["writers"]) + len(recipe["readers"])) as pool:
            futures = [pool.submit(writer, actor, tags) for actor, tags in recipe["writers"].items()]
            futures += [pool.submit(reader, actor, tags) for actor, tags in recipe["readers"].items()]
            actor_ready.wait(timeout=deadline)
            rec.event("stage", "actors-ready")
            for verb in recipe["maintenance"]:
                begun = time.monotonic()
                result = node.operator("store", verb, timeout=deadline)
                rec.event("client", "maintenance", actor="maintenance", phase="mixed", verb=verb,
                          outcome={EXIT.OK: "accepted", EXIT.REFUSED: "refused",
                                   EXIT.UNCERTAIN: "uncertain", EXIT.FAULT: "fault"}.get(result.returncode, "other"),
                          returncode=result.returncode, stdout=result.stdout.decode("utf-8", "replace"),
                          stderr=result.stderr.decode("utf-8", "replace"), latency_s=time.monotonic() - begun)
                if result.returncode not in (EXIT.OK, EXIT.REFUSED):
                    raise AssertionError(f"{verb} uncertain/fault: {result.returncode}")
            for future in futures:
                future.result(timeout=deadline)
        mixed_elapsed = time.monotonic() - started
        rec.event("stage", "mixed-finished", duration_s=mixed_elapsed)
        with Client(node.port, timeout=deadline) as client:
            for tag in accepted:
                data = read_exact(client, tag)
                durable_hashes[tag] = hashlib.sha256(data).hexdigest()
                current = number(client, tag)
                if accepted[tag] is not None and accepted[tag] != current:
                    raise AssertionError(f"number changed before restart: {tag}")
                accepted[tag] = current
                rec.event("client", "verified", tag=tag, number=current, result="match",
                          served_sha256=durable_hashes[tag])
        if len(set(accepted.values())) != len(accepted):
            raise AssertionError("local article numbers reused")
        previous = len(re.findall(rb"CHECKPOINT auto sequence=", node.process.stderr.since(0)))
        node.operator("store", "checkpoint", timeout=deadline, expect=EXIT.OK)
        sequence = wait_checkpoint(node.process, previous, deadline)
        rec.event("internal", "checkpoint-published", sequence=sequence)
        # Preserve a named resource refusal while still checking all promises.
        quiet = node.operator("store", "reclaim", timeout=deadline)
        rec.event("client", "quiet-reclaim", returncode=quiet.returncode,
                  outcome={EXIT.OK: "accepted", EXIT.REFUSED: "refused",
                           EXIT.UNCERTAIN: "uncertain", EXIT.FAULT: "fault"}.get(quiet.returncode, "other"),
                  stdout=quiet.stdout.decode("utf-8", "replace"), stderr=quiet.stderr.decode("utf-8", "replace"))
        if quiet.returncode == EXIT.REFUSED:
            coverage_gaps.append("quiet-reclaim-refused:" + quiet.stdout.decode("utf-8", "replace").strip())
        elif quiet.returncode != EXIT.OK:
            raise AssertionError(f"quiet reclaim uncertain/fault: {quiet.returncode}")
        resources.phase = "shutdown"
        shutdown_begun = time.monotonic()
        node.stop(grace=deadline)
        rec.event("environment", "owner-stopped", returncode=node.process.returncode)
        rec.event("environment", "shutdown-duration", duration_s=time.monotonic() - shutdown_begun)
        resources.phase = "recovery-and-verification"
        boot_begun = time.monotonic()
        node.start(timeout=600)
        rec.event("environment", "owner-ready", pid=node.process.pid,
                  boot_s=time.monotonic() - boot_begun, opening="recovery")
        with Client(node.port, timeout=deadline) as client:
            for tag, old in accepted.items():
                data = read_exact(client, tag)
                current = number(client, tag)
                if current != old:
                    raise AssertionError(f"number changed on reopen: {tag}: {old}->{current}")
                if hashlib.sha256(data).hexdigest() != durable_hashes[tag]:
                    raise AssertionError(f"served bytes changed on reopen: {tag}")
                rec.event("client", "recovered", tag=tag, number=current, result="match",
                          served_sha256=hashlib.sha256(data).hexdigest())
        rec.event("stage", "reopened")
        check_history(rec.journal, recipe)
    except Exception as error:
        stop.set()
        actor_ready.abort()
        failure = dict(exception=type(error).__name__, diagnostic=str(error))
        rec.event("environment", "run-failed", **failure)
    finally:
        peaks = resources.end() if resources else None
        try:
            if not case.doCleanups():
                cleanup_errors.append("fixture cleanup failed")
        except Exception as error:
            cleanup_errors.append(str(error))
        for i, process in enumerate(node.processes):
            (work / f"owner-{i}.stderr").write_bytes(process.stderr.since(0))
            (work / f"owner-{i}.stdout").write_bytes(process.stdout.since(0))
            if process.stderr.dropped or process.stdout.dropped:
                cleanup_errors.append(f"owner-{i} diagnostic stream truncated")
    rec.journal.write(work / "journal.jsonl")
    (work / "plan.json").write_text(json.dumps(recipe, indent=2) + "\n")
    rows = [r for r in rec.journal.records if r.get("phase") == "mixed"]
    actors = {}
    for actor in sorted(set(r["actor"] for r in rows)):
        events = [r for r in rows if r["actor"] == actor]
        latencies = [r["latency_s"] for r in events]
        finished = [r["elapsed_s"] for r in events]
        actors[actor] = dict(completed=len(events), p50_ms=1000 * percentile(latencies, .5),
                            p95_ms=1000 * percentile(latencies, .95), p99_ms=1000 * percentile(latencies, .99),
                            max_ms=1000 * max(latencies),
                            max_completion_gap_s=max((b - a for a, b in zip(finished, finished[1:])), default=0))
    summary = dict(verdict=("failed" if failure or cleanup_errors else "incomplete" if coverage_gaps else "passed"),
                   correctness="passed" if failure is None and not cleanup_errors else "failed",
                   coverage_gaps=coverage_gaps,
                   failure=failure, cleanup_errors=cleanup_errors, actors=actors,
                   post_outcomes=dict(Counter(r["outcome"] for r in rows if r["event"] == "post")),
                   recovered=len([r for r in rec.journal.records if r.get("event") == "recovered"]),
                   mixed_elapsed_s=locals().get("mixed_elapsed"), resources=peaks,
                   accepted_posts_per_mixed_phase_s=(sum(r.get("outcome") == "accepted" for r in rows
                                             if r["event"] == "post") / mixed_elapsed
                                         if "mixed_elapsed" in locals() and mixed_elapsed else None),
                   journal_digest=rec.journal.digest(),
                   scope="empirical finite schedule; cold means fresh TCP, not evicted OS cache; "
                         "slow means delayed client line consumption, not asserted socket backpressure")
    (work / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    runtime = runtime_sbcl(image)
    tool_source = os.environ.get("FN_MIXED_TOOL_SOURCE")
    if tool_source is None:
        revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        tool_source = revision.stdout.strip() if revision.returncode == 0 else None
    manifest = dict(image=str(image), image_identity=image_identity(Path(image), source=image_source),
                    host=platform.uname()._asdict(), python=sys.version, profile=recipe["profile"],
                    seed=recipe["seed"], mode=mode, tool_revision=tool_source,
                    started_utc=started_utc, finished_utc=datetime.now(timezone.utc).isoformat(),
                    runtime=runtime[0] if runtime else None,
                    inputs={p: file_hash(ROOT / p) for p in (
                        "tools/native_mixed_workload.py", "tests/native_harness.py",
                        "tools/native_env.py", "tools/resilience/journal.py",
                        "tools/resilience/adapters/native_cuts.py", "tests/campaign/native_operator_campaign.py")})
    (work / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--image")
    parser.add_argument("--image-source")
    parser.add_argument("--out", type=Path)
    parser.add_argument("--check-run", type=Path, help="verify a sealed run's observed promises without a node")
    parser.add_argument("--plan", type=Path, help="replay this actor plan and barriers")
    parser.add_argument("--mode", choices=("baseline", "slow", "paired"), default="paired")
    parser.add_argument("--seed", type=int, default=19)
    parser.add_argument("--initial", type=int, default=24)
    args = parser.parse_args()
    if args.check_run:
        recipe = json.loads((args.check_run / "plan.json").read_text())
        journal = Journal.read(args.check_run / "journal.jsonl")
        check_history(journal, recipe)
        summary = json.loads((args.check_run / "summary.json").read_text())
        print(json.dumps(dict(history_check="passed", recorded_run_verdict=summary["verdict"],
                              recorded_coverage_gaps=summary.get("coverage_gaps", []),
                              scope="acknowledged content/number promise history only", journal=journal.seal()), indent=2))
        return 0
    if not args.image or not args.image_source or not args.out:
        parser.error("native execution requires --image, --image-source and --out")
    recipe = json.loads(args.plan.read_text()) if args.plan else plan(args.seed, args.initial)
    if not recipe["initial"] or recipe["profile"] != PROFILE:
        parser.error("requires nonempty initial articles and the supported matched profile")
    results = {mode: run_case(Path(args.image).resolve(), args.image_source, args.out / mode, recipe, mode)
               for mode in (("baseline", "slow") if args.mode == "paired" else (args.mode,))}
    print(json.dumps({mode: {k: value[k] for k in ("verdict", "failure", "post_outcomes", "recovered")}
                      for mode, value in results.items()}, indent=2))
    return 0 if all(r["verdict"] == "passed" for r in results.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())

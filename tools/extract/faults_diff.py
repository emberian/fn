#!/usr/bin/env python3
"""tools/extract/faults_diff.py IMAGE CORE OUT [--traces DIR]... -- the fault differential:
the reference image and fn-core over the same fault cases, observation for observation.

X1's obligation O4 (effect preservation; EXTRACTION-PROGRAM-20261007.md) is evidenced, not
proved, by differentials.  gate.py's transcripts, store and stateful steps cover the served
happy paths and the writable verbs.  This cell covers the fault corpus:
  * every reproducer in tests/fixtures/fuzz-nntp (tests/fuzz_nntp.py campaigns): the wire
    bytes, EOF/reset/timeout and liveness for the diff, node and bounds campaigns; for the store
    campaign, each step's exit status and its stderr with paths elided, then the articles served
    after an accepted open.  RSS is measured by the bounds campaign itself and is not compared;
  * every trace in each --traces DIR (L's load fault corpus, schema 1; see TRACES below), as
    soon as it appears there.
The two sides run each case in sequence, never concurrently.  A case passes when the two
observations are equal.  Writes OUT/faults.json (each case, both observations, the verdict) and
prints `faults: N cases, M agree'.  Exits 1 if any case differs or fails to run, or if no case
ran at all.
"""
import argparse
import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tests" / "fixtures" / "fuzz-nntp"
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "tests"))
import fuzz_nntp as fz  # noqa: E402


def blob(octets):
    """A byte observation: its length and digest, and the first 200 octets for the report."""
    if isinstance(octets, str):
        octets = octets.encode("latin-1")
    return {"len": len(octets), "sha256": hashlib.sha256(octets).hexdigest(),
            "head": octets[:200].decode("latin-1")}


def session_obs(s):
    return {"received": blob(fz.normalize(s["received"])), "eof": s["eof"], "reset": bool(s["reset"]),
            "timeout": s["timeout"], "connect_error": bool(s["connect_error"]), "send_error": bool(s["send_error"])}


def observe_diff(launcher, record):
    chunks = [bytes.fromhex(h) for h in record.get("minimized_hex") or record["chunks_hex"]]
    store = None if record.get("store", "-") == "-" else record["store"]
    rc, out, _ = fz.model_reply(launcher, [b"".join(chunks)], store)
    reader = fz.Reader(launcher, store)
    try:
        s = fz.served(reader, chunks, 0.02 if len(chunks) > 1 else 0.0)
        alive = reader.alive()
    finally:
        reader.stop()
    return {"model_exit": rc, "model": blob(fz.normalize(out)), "served": session_obs(s), "reader_alive": alive}


def observe_node(launcher, record):
    chunks = [bytes.fromhex(h) for h in record.get("minimized_hex") or record["chunks_hex"]]
    scratch = Path(tempfile.mkdtemp(prefix="fd-node-"))
    node = fz.Node(launcher, scratch, tls=record.get("node_tls", record.get("tls", False)))
    try:
        source = "127.0.0.1" if record.get("role") == "peer" else "127.0.0.2"
        port = node.tls_port if record.get("tls") else node.port
        s = fz.Session("127.0.0.1", port, chunks, gap=0.001 if len(chunks) > 1 else 0.0, deadline=60.0,
                       source=source, tls_context=node.tls_context() if record.get("tls") else None).run()
        return {"session": session_obs(s), "node_alive": node.alive(), "login_ok": node.login_ok}
    finally:
        node.stop()
        shutil.rmtree(scratch, ignore_errors=True)


def observe_bounds(launcher, record):
    scratch = Path(tempfile.mkdtemp(prefix="fd-bounds-"))
    node = fz.Node(launcher, scratch, tls=False)
    try:
        r = fz.stream_endless(node.port, bytes.fromhex(record["prefix_hex"]), bytes.fromhex(record["filler_hex"]),
                              record["total"], source=record.get("source", "127.0.0.2"))
        return {"replies": blob(r["replies"]), "closed": bool(r["closed"]), "node_alive": node.alive()}
    finally:
        node.stop()
        shutil.rmtree(scratch, ignore_errors=True)


def observe_store(launcher, record):
    scratch = Path(tempfile.mkdtemp(prefix="fd-store-"))
    try:
        base, archive, ids = fz.build_base_store(launcher, scratch, record.get("articles", 12))
        _, baseline_out, _ = fz.article_bytes(launcher, base, ids)
        baseline = fz.store_article_map(baseline_out, ids)
        fields, bad = fz.store_case(launcher, base, archive, ids, baseline, scratch / "case", record["mutation"])
        steps = [[name, rc, err.replace(str(scratch), "SCRATCH")] for name, rc, err in fields["steps"]]
        return {"steps": steps, "served": fields["served"], "verdict": list(bad) if bad else None}
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


OBSERVE = {"diff": observe_diff, "node": observe_node, "bounds": observe_bounds, "store": observe_store}

# TRACES (agreed with L, 2026-10-08): <corpus>/<cell>/<run-label>-<id>.json, schema 1:
# {"schema":1,"cell","id","store":{"init_flags","groups","fixture"},"sbcl_user_args","sequential",
#  "steps":[{"t":"start"}|{"t":"conn","c"}|{"t":"send","c","hex"}|{"t":"read","c","until"}|{"t":"close","c"}|
#           {"t":"crash","boundary","hit"}|{"t":"restart"}|{"t":"inventory"}], "ops":[...]}
# Crashes are injected by boundary name and hit count through L's f2-crash.lisp hook (XL_HOOK in fn-core,
# --eval in the image; FN_LOAD_CRASH_AT=function:k).  A trace is replayed by tools/load (L's driver) on each
# launcher; this cell compares the two replays' per-op outcome class and reply line (byte for byte only when
# "sequential"), the store's durable files after each restart, and the inventory.


def trace_cases(dirs):
    out = []
    for d in dirs:
        for f in sorted(Path(d).glob("*/*.json")):
            out.append(("trace", f))
    return out


def observe_trace(launcher, path):
    raise NotImplementedError("trace replay lands with L's first example trace (schema agreed 2026-10-08)")


def run(image, core, out, traces=()):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    cases = [("fixture", f) for f in sorted(FIXTURES.glob("*.json"))] + trace_cases(traces)
    results, agree = [], 0
    for kind, path in cases:
        res = {"case": str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path), "kind": kind}
        try:
            if kind == "fixture":
                record = json.loads(path.read_text())
                observe = OBSERVE[record["campaign"]]
                res["campaign"] = record["campaign"]
                res["image"] = observe(image, record)
                res["core"] = observe(core, record)
            else:
                res["image"] = observe_trace(image, path)
                res["core"] = observe_trace(core, path)
            res["verdict"] = "agree" if res["image"] == res["core"] else "DIFFER"
        except Exception as ex:  # a case that cannot run is a failure, never a pass
            res["verdict"] = "ERROR"
            res["error"] = repr(ex)[:400]
        if res["verdict"] == "agree":
            agree += 1
        else:
            print("faults: %s %s%s" % (res["verdict"], res["case"], (": " + res.get("error", "")) if "error" in res else ""))
        results.append(res)
        (out / "faults.json").write_text(json.dumps({"results": results}, indent=1) + "\n")
    print("faults: %d cases, %d agree" % (len(results), agree))
    return 0 if results and agree == len(results) else 1


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("image")
    p.add_argument("core")
    p.add_argument("out")
    p.add_argument("--traces", action="append", default=[])
    a = p.parse_args(argv)
    return run(Path(a.image).absolute(), Path(a.core).absolute(), a.out, a.traces)


if __name__ == "__main__":
    sys.exit(main())

"""Manual GROUP/LISTGROUP measurement on the 128-article maximum profile.

Run from the repository root: python3 tests/index_measure.py

This times one ACL2 bridge call per sample, so every number includes exactly
one bridge round trip.  The `refusal` arm is that round trip with no
enumeration at all -- `fn-index-host-query` with a generation the cache was
not built for -- and is reported so the round trip can be subtracted.  This
measures a persistent process, not CLI startup, not power-loss behavior, and
not a served socket.
"""
import hashlib
import json
import statistics
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from tests.test_index_cache import IndexReader  # noqa: E402
from tools.run_store import (Acl2Store, Store, profile_config,  # noqa: E402
                             conservative_charge, metadata)

RUNS = 5
GROUP = "fn.letters"
ALL_HIGH = 2147483647


def build_maximum_profile(path):
    """The store_capacity_probe.py profile: max_transactions maximum payloads."""
    store, bridge = Store(path, writable=True), None
    try:
        store.initialize()
        store.acquire()
        bridge = Acl2Store()
        store.recover(bridge)
        payload = b"x" * profile_config()["max_payload_bytes"]
        count = profile_config()["max_transactions"]
        for sequence in range(count):
            msgid = ("<capacity-%d@example.invalid>" % sequence).encode("ascii")
            obligation, subject, evidence = metadata(msgid, payload)
            store.advance_frontier(bridge, bridge.next_txid())
            assert bridge.prepare(msgid, payload, [0, 1], obligation, subject,
                                  evidence, conservative_charge(payload)) == "prepared"
            assert store.publish(bridge, sequence, bridge.pending_record()) == "durable"
            assert store.finish(bridge) == "durable"
        return count
    finally:
        if bridge is not None:
            bridge.close()
        store.close()


def sample(reader, form, runs=RUNS):
    seconds = []
    for _ in range(runs):
        started = time.perf_counter()
        reader.bridge.call(form, timeout=600)
        seconds.append(time.perf_counter() - started)
    return {"runs": runs,
            "min_seconds": round(min(seconds), 6),
            "median_seconds": round(statistics.median(seconds), 6)}


def main():
    output = ROOT / "build/index-measure/measure.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    result = {"command": [sys.executable, "tests/index_measure.py"],
              "profile": {"articles": profile_config()["max_transactions"],
                          "payload_bytes": profile_config()["max_payload_bytes"],
                          "groups_per_article": 2,
                          "group": GROUP},
              "note": "each sample is one ACL2 bridge call; the refusal arm is"
                      " the same round trip with no enumeration",
              "status": "running"}
    with tempfile.TemporaryDirectory(prefix="fn-index-measure-") as temporary:
        path = Path(temporary) / "store"
        started = time.monotonic()
        result["articles_committed"] = build_maximum_profile(path)
        result["build_seconds"] = round(time.monotonic() - started, 3)
        reader = IndexReader(path)
        try:
            assert reader.generation == result["articles_committed"]
            opened = time.perf_counter()
            reader.open_index()
            result["index_open_seconds"] = round(time.perf_counter() - opened, 6)
            # The answers must agree before any timing is reported.
            checks = {}
            for kind, extra in (("count", {}), ("low", {}), ("high", {}),
                                ("range", {})):
                index_answer = reader.query(kind, GROUP, **extra)
                fold_answer = reader.fold(kind, GROUP, **extra)
                assert index_answer[0] == "ok", (kind, index_answer)
                assert index_answer == fold_answer, (kind, index_answer, fold_answer)
                checks[kind] = (index_answer[1] if kind != "range"
                                else len(index_answer[1]))
            result["answers"] = checks
            generation = reader.generation
            arms = {
                "group_count_fold":
                    '(fn-index-host-fold :count "{}" 1 {} nil state)'.format(GROUP, ALL_HIGH),
                "group_count_index":
                    '(fn-index-host-query {} :count "{}" 1 {} nil state)'.format(
                        generation, GROUP, ALL_HIGH),
                "group_low_fold":
                    '(fn-index-host-fold :low "{}" 1 {} nil state)'.format(GROUP, ALL_HIGH),
                "group_low_index":
                    '(fn-index-host-query {} :low "{}" 1 {} nil state)'.format(
                        generation, GROUP, ALL_HIGH),
                "group_high_fold":
                    '(fn-index-host-fold :high "{}" 1 {} nil state)'.format(GROUP, ALL_HIGH),
                "group_high_index":
                    '(fn-index-host-query {} :high "{}" 1 {} nil state)'.format(
                        generation, GROUP, ALL_HIGH),
                "listgroup_range_fold":
                    '(fn-index-host-fold :range "{}" 1 {} nil state)'.format(GROUP, ALL_HIGH),
                "listgroup_range_index":
                    '(fn-index-host-query {} :range "{}" 1 {} nil state)'.format(
                        generation, GROUP, ALL_HIGH),
                "refusal_round_trip":
                    '(fn-index-host-query {} :count "{}" 1 {} nil state)'.format(
                        generation + 1, GROUP, ALL_HIGH),
            }
            result["measurements"] = {name: sample(reader, form)
                                      for name, form in sorted(arms.items())}
            result["status"] = "passed"
        finally:
            reader.close()
            result["runtime_source_sha256"] = {
                name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                for name in ("books/nntp-index.lisp", "host/index-host.lisp",
                             "tests/index_measure.py", "tests/test_index_cache.py")}
            output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
            print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()

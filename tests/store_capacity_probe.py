"""Manual maximum-profile probe using the real ACL2/store path in a temp dir.

Run from the repository root: python3 tests/store_capacity_probe.py
This exercises a persistent process, not CLI startup cost or power-loss behavior.
"""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from tools.run_store import (Acl2Store, Store, profile_config, conservative_charge,
                             metadata, open_live_store)


def main():
    output = ROOT / "build/store-probe/resource.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    result = {"command": [sys.executable, "tests/store_capacity_probe.py"],
              "profile": profile_config(), "status": "running", "transactions": 0,
              "payload_bytes": profile_config()["max_payload_bytes"]}
    with tempfile.TemporaryDirectory(prefix="fn-resource-probe-") as temporary:
        path = Path(temporary) / "store"
        store, bridge = Store(path, writable=True), None
        try:
            store.initialize()
            store.acquire()
            bridge = Acl2Store()
            store.recover(bridge)
            payload = b"x" * result["payload_bytes"]
            count = profile_config()["max_transactions"]
            for sequence in range(count):
                msgid = ("<capacity-%d@example.invalid>" % sequence).encode("ascii")
                obligation, subject, evidence = metadata(msgid, payload)
                store.advance_frontier(bridge, bridge.next_txid())
                assert bridge.prepare(msgid, payload, [0, 1], obligation, subject,
                                      evidence, conservative_charge(payload)) == "prepared"
                assert store.publish(bridge, sequence, bridge.pending_record()) == "durable"
                assert store.finish(bridge) == "durable"
                result["transactions"] = sequence + 1
            result["commit_seconds"] = time.monotonic() - started
            bridge.close()
            store.close()
            bridge = None
            before = time.monotonic()
            store, bridge, records = open_live_store(path, writable=False)
            result.update(reopen_seconds=time.monotonic() - before,
                          replayed_records=len(records), article_count=bridge.article_count(),
                          pin_count=bridge.pin_count(), reserved=bridge.reserved(),
                          next_txid=bridge.next_txid())
            assert result["article_count"] == result["pin_count"] == len(records) == count
            assert bridge.group_next(0) == bridge.group_next(1) == count + 1
            assert bridge.lookup(b"<capacity-0@example.invalid>") == payload
            assert result["reserved"] == count * conservative_charge(payload)
            result["status"] = "passed"
        except Exception as error:
            result.update(status="failed", error=repr(error))
            raise
        finally:
            if bridge is not None:
                bridge.close()
            store.close()
            result["elapsed_seconds"] = time.monotonic() - started
            result["runtime_source_sha256"] = {
                name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                for name in ("tools/run_store.py", "host/store-node-host.lisp",
                             "tests/store_capacity_probe.py")}
            output.write_text(json.dumps(result, indent=2) + "\n")
            print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()

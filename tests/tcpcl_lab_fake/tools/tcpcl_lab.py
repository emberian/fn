#!/usr/bin/env python3
"""tests/twonode_gate_fake: the TCPCLv4 lab, for the twonode gate's dry run.

Every row here is this file's.  It speaks no TCPCL, starts no image and makes
no claim about fn; it prints the JSON shape `tools/twonode_gate.py` parses --
one object per scenario and a summary -- so that the gate's row accounting,
its note rendering and its treatment of a missing row are exercised with no
ACL2 on the box.  The real lab is `tools/tcpcl_lab.py` and the dry run never
reaches it, the same way it never reaches the real `tools/run_store.py`.

`FN_FAKE_TCPCL_DROP` names scenarios to leave out, so a test can drive the
gate's "the lab produced no result for this scenario" path on purpose.
"""
import json
import os
import sys

SCENARIOS = ("exchange", "refused", "keepalive", "crash", "profile", "adu",
             "replay")
DETAIL = {
    "exchange": {"segments": 2, "both_spools": True},
    "refused": {"refused_before_any_segment": True, "exit_code": 1},
    "keepalive": {"keepalives": 4, "neither_side_timed_out": True},
    "crash": {"acknowledged_survived": True, "in_flight_absent": True},
    "profile": {"per_chunk_calls": 1, "quadratic": False},
    "adu": {"adu_byte_identical": True},
    "replay": {"event_streams_equal": True},
}


def main(argv) -> int:
    dropped = set(filter(None, os.environ.get("FN_FAKE_TCPCL_DROP", "").split(",")))
    names = [name for name in SCENARIOS if name not in dropped]
    for name in names:
        print(json.dumps(dict(scenario=name, ok=True, **DETAIL[name]),
                         sort_keys=True), flush=True)
    print(json.dumps({"scenario": "summary", "ok": True, "passed": names,
                      "failed": []}, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

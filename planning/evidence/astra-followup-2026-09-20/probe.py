#!/usr/bin/env python3
"""Review probes of actual host/gate methods with simulated boundary outcomes.

Usage: python3 probe.py PATH_TO_REVIEWED_CHECKOUT
These do not run ACL2, sockets, or a storage device. They establish which
events the host emits and how the gate classifies an injected failure.
"""
import json
from pathlib import Path
import sys
from types import SimpleNamespace as NS

sys.path.insert(0, str(Path(sys.argv[1]).resolve() / "tools"))
from deploy_gate import Step
from run_owner import Owner
from twonode_gate import TwoNodeGate


def gate_probe(arrived, accepted_lines, end_count):
    gate = TwoNodeGate.__new__(TwoNodeGate)
    gate.a = NS(post_enabled=True, port=1111, accepted=[])
    gate.b = NS(tap_port=2222, port=3333, tap_log="/simulated/tap", accepted=[])
    gate.steps, gate.gaps, gate.facts = [], [], {}
    presence_calls = 0

    def step(name, output, rc=0, expect=None):
        result = Step(name, "SIMULATED boundary outcome", rc, output, 0, expect=expect)
        gate.steps.append(result)
        return result

    def feed(phase, extra, name=None, expect=0, **kwargs):
        nonlocal presence_calls
        if phase == "post":
            value = {"ok": True}
        elif phase == "wait":
            value = {"ok": arrived, "status": "article" if arrived else "timeout",
                     "identical": arrived}
        else:
            from twonode_gate import GROUPS
            count = 0 if presence_calls == 0 else end_count
            presence_calls += 1
            value = {"groups": {GROUPS[0]: f"211 {count} 1 1 {GROUPS[0]}"}}
        return step(name or phase, json.dumps(value),
                    1 if phase == "wait" and not arrived else 0, expect)

    gate.feed = feed
    gate.tap_mark = lambda node: 0
    gate.stop_node = lambda *a, **k: None
    gate.start_node = lambda *a, **k: True
    gate.sh = lambda name, command, **kw: step(name, "CUT-TAKEN", expect=kw.get("expect"))
    gate.read_tap = lambda *a, **k: step("tap", "S< 239 accepted\n" * accepted_lines)
    gate.scenario_feed_peer_cut()
    bad = [s for s in gate.steps if s.failed]
    assert gate.gaps and not bad
    return {"arrived": arrived, "accepted_replies": accepted_lines,
            "final_group_count": end_count, "failed_steps": len(bad),
            "main_exit_expression_without_exception": 1 if bad else 0,
            "gaps": gate.gaps}


def close_probe():
    events = []
    owner = Owner.__new__(Owner)
    feed = NS(peer="peer-b", session=NS(sock="socket"), next_dial=0)

    def close():
        events.append(["close-socket"])
        feed.session = None

    feed.close = close
    owner.selector = NS(unregister=lambda sock: events.append(["unregister", sock]))
    owner.bridge = NS(
        feed_connect=lambda peer, conn: events.append(["feed-connect", peer, conn]),
        # Explicit fixture: the queue contains only an in-flight entry.
        feed_has_queued=lambda peer: False)
    owner.clock = NS(milliseconds=lambda: 1000)
    owner.feeds = {feed.peer: feed}
    owner.feed_dial = lambda feed: events.append(["dial"]) or True
    owner.feed_drop(feed)
    owner.feed_poll()
    assert events == [["unregister", "socket"], ["close-socket"],
                      ["feed-connect", "peer-b", None]]
    return {"fixture": "only in-flight work, no queued work", "host_events": events,
            "scope": "Actual Python methods; ACL2 transition established separately by source trace."}


print(json.dumps({"gate": [gate_probe(False, 0, 0), gate_probe(True, 2, 1),
                            gate_probe(True, 1, 2)],
                  "disconnect": close_probe()}, indent=2))

"""The INN lab as a differential backend (design §W7e; the interop row of
§3).  tools/inn_lab.py runs fn against a real INN 2.7.4 on hbox and writes
one finding per declared assertion (`<evidence>.findings.json`: key,
instance, verdict, the observed reply).  This adapter is the lab's IR: its
flows are scenarios over the same operations every other backend uses
(post, read, retry, recover, probe, disconnect), its findings are the
journal's observations, and the verdict is `checker.check` under the
contract's rules, so a differential run is judged by the checker, never by
a per-assertion `ok`.

What is normalized is explicit and named (NORMALIZED): the two fields RFC
5537 lets a relaying or serving agent change, Path (3.6 step 4, 3.2.1) and
Xref (3.7 step 7; specs/peering.md 2.3).  Local numbers are never compared:
every read is by Message-ID.  Response classes, Message-IDs, memberships
and authored bytes are never normalized: a differential naming any other
field, a body that differs, a served Path that does not name the server or
a sender's Xref served is a violation of `relay-changes-permitted`, judged
by the contract from the differential itself.  The RFC adjudicates, and the
same rules judge both agents: `inn-lab-inn-refusals` is INN's own
duplicate and loop answers under the rules fn is held to.

The lab's faults are two: the fn owner's SIGTERM with no transfer in flight
(boundary `peer-idle`) and the peer daemon killed (`peer-innd`).  What the
peer does after its own death (innd restarted, its history kept) is the
peer's; it is journaled as environment facts and no rule of fn's judges it.
fn's own recovery and the articles it serves after the SIGTERM are judged
by the rules every other backend uses (recovery-keeps-history,
committed-serves-exact).

Over the three findings files in planning/evidence (2026-09-22, 2026-09-23
twice): the 2026-09-22 run's `operator post` (INN's 437 "Missing Path"
refutes the injection) and inn-to-fn flow (the served Path without fn's
identity, the sender's Xref served) are violations; every other scenario is
consistent.  The lab writes findings; the next step is the lab itself
running from these scenarios (its checks become journal writes).

    python3 -m tools.resilience.adapters.inn_lab [FINDINGS.json ...]
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.resilience.scenario import (  # noqa: E402
    Scenario, Operation, Fault, check as check_scenario,
    INTEROP_IDLE_BOUNDARY, INTEROP_PEER_BOUNDARY)
from tools.resilience.journal import Journal  # noqa: E402
from tools.resilience import checker  # noqa: E402

EVIDENCE_DIR = ROOT / "planning/evidence"
GROUP = "fn.letters"
# The fields a relaying or serving agent may change, each with the RFC that
# lets it (tools/inn_lab.py RELAY_MAY_CHANGE; the test asserts they agree).
NORMALIZED = {
    "path": "RFC 5537 3.6 step 4 and 3.2.1: each relaying or injecting agent prefixes "
            "its identity",
    "xref": "RFC 5537 3.7 step 7; specs/peering.md 2.3: the serving agent's own, never "
            "stored, never the sender's",
}
NEVER_NORMALIZED = ("response classes", "Message-IDs", "memberships", "authored bytes",
                    "local numbers (never compared: every read is by Message-ID)")
REQUIREMENTS = ["INT-001", "STO-002"]


def records() -> list:
    return sorted(EVIDENCE_DIR.glob("inn-lab-*.findings.json"))


def load(path) -> dict:
    return json.loads(Path(path).read_text())


class Rows:
    """The findings by (key, instance); `used` names every row a scenario
    read, so its expected verdict is the lab's over those rows only."""

    def __init__(self, findings: dict):
        self.by = {(r["key"], r.get("instance", "")): r for r in findings["rows"]}
        self.used = []

    def get(self, key: str, instance: str = "") -> dict | None:
        r = self.by.get((key, instance))
        if r is not None:
            self.used.append(r)
        return r

    def expected(self) -> str:
        return "violation" if any(r["verdict"] == "violated" for r in self.used) \
            else "consistent"

    def text(self, key: str, instance: str = "") -> str:
        r = self.get(key, instance)
        return "" if r is None else str(r.get("observed") or r.get("detail") or "")


def parse_differential(text: str) -> dict:
    """tools/inn_lab.py describe_differences, back into its fields."""
    d = {"changed": [], "only_first": [], "only_second": [], "body_identical": False,
         "order_identical": True, "normalized": sorted(NORMALIZED)}
    if text.strip() == "byte-identical":
        d["body_identical"] = True
        return d
    for part in text.split(";"):
        part = part.strip()
        if part.startswith("changed: "):
            d["changed"] = part[len("changed: "):].split(", ")
        elif part.startswith("only in the first: "):
            d["only_first"] = part[len("only in the first: "):].split(", ")
        elif part.startswith("only in the second: "):
            d["only_second"] = part[len("only in the second: "):].split(", ")
        elif part == "body identical":
            d["body_identical"] = True
        elif part == "the shared fields are in a different order":
            d["order_identical"] = False
    return d


def _status(text: str, *codes) -> str:
    """The reply line of TEXT (segments joined by ' / ') that starts with one
    of CODES, else the last segment."""
    segments = [s.strip() for s in text.split(" / ")]
    for s in segments:
        if any(s.startswith(c) for c in codes):
            return s
    return segments[-1] if segments else ""


def _post(id_: str, payload: str, **args) -> Operation:
    return Operation(id_, "client", "post", dict({"groups": [GROUP], "payload": payload}, **args))


def _reply(j, rows, key, instance, op, accepted_codes, route):
    text = rows.text(key, instance)
    status = _status(text, *accepted_codes)
    row = rows.by.get((key, instance))
    ok = row is not None and row["verdict"] == "held"
    outcome = "accepted" if ok else ("lost" if row is None else "refused")
    j.client("reply", operation=op, outcome=outcome, route=route, status=status)
    return ok


def _transfer(j, rows, key, instance, op, side):
    text = rows.text(key, instance)
    row = rows.by.get((key, instance))
    status = _status(text, "235", "239", "437", "435")
    outcome = ("lost" if row is None else
               "accepted" if status.startswith(("235", "239")) else "refused")
    j.environment("peer-transfer", operation=op, side=side, outcome=outcome, status=status,
                  evidence=text[:160])


def _retry(j, rows, key, instance, op, side):
    text = rows.text(key, instance)
    status = _status(text, "435", "437")
    outcome = "duplicate" if status.startswith("435") else \
        "refused" if status.startswith(("437", "441")) else "accepted" if status else "lost"
    j.client("reply", operation=op, outcome=outcome, route="peer-transit", side=side,
             status=status)


def _read(j, rows, key, instance, op, article, side, **extra):
    row = rows.get(key, instance)
    if row is None:
        j.client("read", operation=op, article=article, route="peer", side=side, result="absent")
        return
    diff = dict(parse_differential(str(row.get("observed") or "")), **extra)
    touched = set(diff["changed"]) | set(diff["only_first"]) | set(diff["only_second"])
    permitted = (diff["body_identical"] and touched <= set(diff["normalized"])
                 and diff.get("path_names_self", True) and not diff.get("sender_xref_served"))
    j.client("read", operation=op, article=article, route="peer", side=side,
             result="match" if permitted else "other", differential=diff)


def _scenario(id_, title, ops, faults, healing, witnesses, expected) -> Scenario:
    return check_scenario(Scenario(
        id=id_, title=title, requirements=REQUIREMENTS, contract="local-commit-log",
        initial={"recipe": "inn-lab", "groups": [GROUP], "prior": [],
                 "normalized": sorted(NORMALIZED), "never_normalized": list(NEVER_NORMALIZED)},
        actors=[{"name": "client", "kind": "client"}, {"name": "inn", "kind": "peer"},
                {"name": "lab", "kind": "nemesis"}],
        operations=ops, faults=faults, healing=healing, witnesses=witnesses,
        healing_bound=None, replay="exact", expected=expected))


def fn_to_inn(rows: Rows) -> tuple:
    ops = [_post("post-fn", "posted at fn"),
           Operation("read-inn", "client", "read", {"article": "post-fn", "side": "inn"}),
           Operation("dup-inn", "client", "retry",
                     {"of": "post-fn", "route": "peer-transit", "bytes": "same"}),
           Operation("dup-fn-own", "client", "retry",
                     {"of": "post-fn", "route": "peer-transit", "bytes": "same"})]
    j = Journal("inn-lab-fn-to-inn")
    j.stage("workload", "begun")
    _reply(j, rows, "fn-post-240", "", "post-fn", ("240",), "served-post")
    _transfer(j, rows, "fn-feeds-inn", "", "post-fn", "inn")
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    _read(j, rows, "inn-serves-fn-article", "", "read-inn", "post-fn", "inn")
    _retry(j, rows, "inn-duplicate-435", "fn-article", "dup-inn", "inn")
    _retry(j, rows, "fn-duplicate-435", "fn-article", "dup-fn-own", "fn")
    j.stage("healing", "ended", elapsed=0.0)
    s = _scenario("inn-lab-fn-to-inn",
                  "an article posted at fn reaches INN by fn's feed; INN serves it changed "
                  "only in the normalized fields; a second offer is refused as held on "
                  "both sides",
                  ops, [], ["read-inn", "dup-inn", "dup-fn-own"],
                  ["post-accepted", "relay-normalized", "duplicate-refused"],
                  rows.expected())
    return s, j


def inn_to_fn(rows: Rows) -> tuple:
    ops = [_post("post-inn", "fed by innfeed"),
           Operation("read-fn", "client", "read", {"article": "post-inn", "side": "fn"}),
           Operation("dup-fn", "client", "retry",
                     {"of": "post-inn", "route": "peer-transit", "bytes": "same"}),
           _post("post-loop", "Path names fn", loop=True),
           Operation("read-loop", "client", "read", {"article": "post-loop", "side": "fn"})]
    j = Journal("inn-lab-inn-to-fn")
    j.stage("workload", "begun")
    _reply(j, rows, "innfeed-feeds-fn", "", "post-inn", ("239", "235", "238"), "peer-transit")
    loop = rows.text("fn-loop-refused", "")
    refused = _status(loop, "437", "435")
    j.client("reply", operation="post-loop", route="peer-transit",
             outcome="refused" if refused.startswith(("437", "435")) else "accepted",
             status=refused)
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    own = rows.get("fn-serves-own-path-identity", "")
    sender_xref = rows.get("fn-serves-no-sender-xref", "")
    _read(j, rows, "fn-serves-inn-article", "", "read-fn", "post-inn", "fn",
          path_names_self=own is None or own["verdict"] == "held",
          sender_xref_served=sender_xref is not None and sender_xref["verdict"] != "held")
    _retry(j, rows, "fn-duplicate-435", "inn-article", "dup-fn", "fn")
    j.client("read", operation="read-loop", article="post-loop", route="peer", side="fn",
             result="absent" if _status(loop, "430").startswith("430") else "match")
    j.stage("healing", "ended", elapsed=0.0)
    s = _scenario("inn-lab-inn-to-fn",
                  "an article innfeed transfers is served by fn with only the normalized "
                  "fields changed, fn's own identity in the Path and no sender Xref; a "
                  "second offer is refused as held; a Path naming fn is refused and not "
                  "served",
                  ops, [], ["read-fn", "dup-fn", "read-loop"],
                  ["post-accepted", "relay-normalized", "duplicate-refused", "loop-refused"],
                  rows.expected())
    return s, j


def fn_term(rows: Rows) -> tuple:
    ops = [_post("post-fn", "posted at fn"), _post("post-inn", "fed by innfeed"),
           Operation("idle", "client", "probe", {"what": "no transfer in flight"}),
           Operation("recover", "client", "recover"),
           Operation("read-fn-own", "client", "read", {"article": "post-fn", "side": "fn"}),
           Operation("read-fn-inn", "client", "read", {"article": "post-inn", "side": "fn"})]
    faults = [Fault("idle", INTEROP_IDLE_BOUNDARY, "kill", "contract-admissible", "observed",
                    "served-post")]
    j = Journal("inn-lab-fn-term")
    j.stage("workload", "begun")
    _reply(j, rows, "fn-post-240", "", "post-fn", ("240",), "served-post")
    _reply(j, rows, "innfeed-feeds-fn", "", "post-inn", ("239", "235", "238"), "peer-transit")
    term = rows.text("fn-term-stopped", "")
    j.environment("fault-fired", operation="idle", boundary=INTEROP_IDLE_BOUNDARY,
                  action="kill", route="served-post", evidence=term[:120])
    j.environment("peer-alive", side="inn", evidence=rows.text("innd-survived-fn-term", "")[:120])
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    rec = rows.get("fn-recover", "")
    j.client("recover", operation="recover", phase="healing",
             outcome="completed" if rec is not None and rec["verdict"] == "held" else "lost",
             evidence=(rec or {}).get("observed", "")[:120])
    for op, article, instance in (("read-fn-own", "post-fn", "fn-article"),
                                  ("read-fn-inn", "post-inn", "inn-article")):
        row = rows.get("fn-articles-survived-term", instance)
        j.client("read", operation=op, article=article, route="served", side="fn",
                 result="match" if row is not None and row["verdict"] == "held" else "absent")
    j.stage("healing", "ended", elapsed=0.0)
    s = _scenario("inn-lab-fn-term",
                  "the fn owner is stopped by SIGTERM with no transfer in flight while INN "
                  "runs; after recovery fn serves both the article it injected and the one "
                  "it took by transit",
                  ops, faults, ["recover", "read-fn-own", "read-fn-inn"],
                  ["post-accepted", "recovery-completed", "read-completed"], rows.expected())
    return s, j


def innd_cut(rows: Rows) -> tuple:
    ops = [_post("post-fn", "posted at fn"), _post("post-inn", "fed by innfeed"),
           Operation("innd", "client", "disconnect", {"peer": "inn"}),
           Operation("again-fn-article", "client", "retry",
                     {"of": "post-fn", "route": "peer-transit", "bytes": "same"}),
           Operation("again-inn-article", "client", "retry",
                     {"of": "post-inn", "route": "peer-transit", "bytes": "same"})]
    faults = [Fault("innd", INTEROP_PEER_BOUNDARY, "kill", "assumption-challenging",
                    "observed", "peer-transit")]
    j = Journal("inn-lab-innd-cut")
    j.stage("workload", "begun")
    _reply(j, rows, "fn-post-240", "", "post-fn", ("240",), "served-post")
    _reply(j, rows, "innfeed-feeds-fn", "", "post-inn", ("239", "235", "238"), "peer-transit")
    j.environment("fault-fired", operation="innd", boundary=INTEROP_PEER_BOUNDARY,
                  action="kill", route="peer-transit", evidence=rows.text("innd-died", "")[:120])
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    j.environment("peer-restarted", side="inn", evidence=rows.text("innd-restarted", "")[:120])
    _retry(j, rows, "inn-history-survived-kill", "fn-article", "again-fn-article", "inn")
    _retry(j, rows, "inn-history-survived-kill", "inn-article", "again-inn-article", "inn")
    j.stage("healing", "ended", elapsed=0.0)
    s = _scenario("inn-lab-innd-cut",
                  "innd is killed and restarted; offered both articles again it refuses each "
                  "as held (the peer's history is the peer's: an environment fact, no rule "
                  "of fn's)",
                  ops, faults, ["again-fn-article", "again-inn-article"],
                  ["post-accepted", "duplicate-refused"], rows.expected())
    return s, j


def operator_post(rows: Rows) -> tuple:
    ops = [_post("post-op", "submitted by operator post", route="operator-post"),
           Operation("offer", "client", "probe", {"what": "the feed's offer to INN"})]
    j = Journal("inn-lab-operator-post")
    j.stage("workload", "begun")
    # `operator post` acknowledged the submission before the feed ran (the
    # lab's step); the finding is what INN answered fn's offer of it.
    row = rows.by.get(("operator-post-feeds-inn", ""))
    j.client("reply", operation="post-op", outcome="accepted" if row else "lost",
             route="operator-post", status="accepted operator post")
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    _transfer(j, rows, "operator-post-feeds-inn", "", "post-op", "inn")
    j.stage("healing", "ended", elapsed=0.0)
    s = _scenario("inn-lab-operator-post",
                  "an article submitted through `operator post` is offered to INN with the "
                  "injected fields (Path naming fn, Injection-Info) and taken",
                  ops, [], ["offer"], ["post-accepted"], rows.expected())
    return s, j


def inn_refusals(rows: Rows) -> tuple:
    ops = [_post("post-at-inn", "hand-made IHAVE into innd"),
           Operation("dup-at-inn", "client", "retry",
                     {"of": "post-at-inn", "route": "peer-transit", "bytes": "same"}),
           _post("loop-at-inn", "Path names INN", loop=True)]
    j = Journal("inn-lab-inn-refusals")
    j.stage("workload", "begun")
    _reply(j, rows, "inn-transfer-235", "", "post-at-inn", ("235",), "peer-transit")
    loop = _status(rows.text("inn-loop-437", ""), "437", "435")
    j.client("reply", operation="loop-at-inn", route="peer-transit",
             outcome="refused" if loop.startswith(("437", "435")) else "accepted", status=loop)
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    _retry(j, rows, "inn-duplicate-435", "", "dup-at-inn", "inn")
    j.stage("healing", "ended", elapsed=0.0)
    s = _scenario("inn-lab-inn-refusals",
                  "INN under the rules fn is held to: a hand-made transfer taken, a second "
                  "offer refused as held, a Path naming INN refused",
                  ops, [], ["dup-at-inn"], ["post-accepted", "duplicate-refused", "loop-refused"],
                  rows.expected())
    return s, j


FLOWS = (fn_to_inn, inn_to_fn, fn_term, innd_cut, operator_post, inn_refusals)


def scenarios_for(findings: dict) -> list:
    """[(scenario, journal)] for one findings file; each flow reads its own
    rows, so its expected verdict is the lab's over those rows."""
    out = []
    for flow in FLOWS:
        out.append(flow(Rows(findings)))
    return out


def check_findings(path) -> list:
    """[(scenario, journal, verdict)] over one findings file."""
    return [(s, j, checker.check(s, j)) for s, j in scenarios_for(load(path))]


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("findings", nargs="*", help="findings files (default: planning/evidence)")
    a = p.parse_args(argv)
    paths = [Path(x) for x in a.findings] or records()
    bad = 0
    for path in paths:
        findings = load(path)
        print("{} ({} {}):".format(path.name, findings.get("revision", "?")[:9],
                                   findings.get("verdict", "?")))
        for s, j, v in check_findings(path):
            mark = "" if v.kind == s.expected else "  UNEXPECTED (expected {})".format(s.expected)
            bad += bool(mark)
            print("  {:26} {:11} witnesses={} pending={}{}".format(
                s.id, v.kind, ",".join(sorted(v.witnesses_observed)) or "-",
                ",".join(sorted(v.pending_rules)) or "-", mark))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

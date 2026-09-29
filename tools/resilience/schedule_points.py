"""The review's six schedule points (design §5) as GENERATED scenarios.

Each row of the design's table becomes one scenario per boundary it names,
with the adversarial interleaving the review asks for and the verdict the
composed node is expected to earn (`consistent`, with the row's witnesses).
A row whose boundary has no host coordinate for its interleaving is
generated all the same and reported PENDING BY NAME, with the owning lane
and what is missing (`scenario.PENDING_BOUNDARIES`); it is never skipped
silently and no verdict is manufactured for it.

    python3 -m tools.resilience.schedule_points        # the table, by status
"""
from __future__ import annotations

from dataclasses import dataclass

from .adapters import native_cuts as adapter
from .scenario import (Scenario, Operation, Fault, boundary_registry, validate,
                       pending_reasons, pending_owner, PENDING_BOUNDARIES)
from tests.campaign import native_cuts

GROUP = adapter.GROUP


@dataclass(frozen=True)
class Row:
    point: str
    boundaries: tuple
    interleaving: str
    family: str          # an adapter family, or "pending"


ROWS = (
    Row("publication-durable-reply-pending", ("log-fenced",),
        "lose the reply, restart, retry the original identity", "served"),
    Row("page-read-outstanding", ("page-read-outstanding",),
        "cancel the reader, retire the old generation, then deliver the read", "pending"),
    Row("reclaim-candidate-selected", ("reclaim-candidate-selected",),
        "acquire a new independent hold before the destructive action", "pending"),
    Row("new-checkpoint-prepared",
        ("state-checkpoint-staged-durable", "state-checkpoint-replaced",
         "state-checkpoint-durable"),
        "crash before installation, during it, during cleanup", "checkpoint"),
    Row("recovery-repair-write", ("log-truncated", "log-recovered", "recovery-stage-unlinked"),
        "crash again before recovery completes", "recovery"),
    Row("receipt-observed", ("receipt-observed",),
        "duplicate it, reorder with a policy change, lose its durable completion", "bp-node"),
)

PRIOR = {"id": "post-prior", "groups": [GROUP]}


def _pending_page_read() -> Scenario:
    return Scenario(
        id="schedule-page-read-outstanding",
        title="a page read outstanding: the reader cancelled, the old generation retired, "
              "the delayed page delivered; the read completes with the article's bytes",
        requirements=["STO-002"], contract="local-commit-log",
        initial={"recipe": "served-node", "groups": [GROUP], "prior": [PRIOR]},
        actors=adapter.ACTORS,
        operations=[Operation("snapshot", "client", "reader-snapshot", {"article": "post-prior"}),
                    Operation("read-prior", "client", "read", {"article": "post-prior"}),
                    Operation("cancel", "nemesis", "cancel-reader", {"reader": "snapshot"}),
                    Operation("retire", "nemesis", "retire-generation"),
                    Operation("deliver", "nemesis", "deliver-delayed-page",
                              {"article": "post-prior"})],
        faults=[Fault("read-prior", "page-read-outstanding", "interleave", "contract-admissible",
                      "performed", "served-post", ("cancel", "retire", "deliver"))],
        healing=["deliver"], witnesses=["read-completed", "read-during-competing-work"],
        healing_bound=adapter.healing_bound())


def _pending_reclaim() -> Scenario:
    return Scenario(
        id="schedule-reclaim-candidate-selected",
        title="a reclaim candidate selected: a new independent hold is acquired before the "
              "destructive action; the held article is still read whole, eligible content "
              "is freed",
        requirements=["STO-002"], contract="local-commit-log",
        initial={"recipe": "served-node", "groups": [GROUP], "prior": [PRIOR]},
        actors=adapter.ACTORS,
        operations=[Operation("reclaim-1", "client", "reclaim"),
                    Operation("hold", "nemesis", "acquire-hold", {"article": "post-prior"}),
                    Operation("read-prior", "nemesis", "read", {"article": "post-prior"}),
                    Operation("release", "nemesis", "release-hold", {"article": "post-prior"})],
        faults=[Fault("reclaim-1", "reclaim-candidate-selected", "interleave",
                      "contract-admissible", "performed", "store-post",
                      ("hold", "read-prior"))],
        healing=["release"], witnesses=["reclaim-freed", "read-during-competing-work"],
        healing_bound=adapter.healing_bound())


def _receipt(variant: str) -> Scenario:
    """The receipt-observed point on a real BP node (adapters/bp_node.py,
    recipe `bp-node`): the sender's carrier of one request is held at the
    receiver after its decision is recorded; the nemesis interleaves; the
    healing is a dispatch pass (the replay, or the forwarding), the receipt
    observed at the sender's node and the receiver Store probed."""
    receipt = Operation("receipt-1", "client", "receipt", {"bundle": "bundle-1"})
    deliver = Operation("deliver", "client", "status", {"identity": "bundle-1"})
    probe = Operation("probe", "client", "probe", {"identity": "bundle-1"})
    if variant == "duplicate":
        ops = [receipt,
               Operation("receipt-dup", "nemesis", "receipt",
                         {"bundle": "bundle-1", "duplicate_of": "receipt-1"}),
               Operation("dispatch", "client", "restart"), deliver, probe]
        fault = Fault("receipt-1", "receipt-observed", "interleave", "contract-admissible",
                      "observed", "bp-transit", ("receipt-dup",))
        healing = ["dispatch", "deliver", "probe"]
    elif variant == "reorder":
        ops = [receipt,
               Operation("policy", "nemesis", "policy-change",
                         {"what": "receipt-policy", "change": "route-removed"}),
               Operation("dispatch-held", "client", "restart"),
               Operation("restore", "client", "policy-change",
                         {"what": "receipt-policy", "change": "route-restored"}),
               Operation("dispatch", "client", "restart"), deliver, probe]
        fault = Fault("receipt-1", "receipt-observed", "interleave", "contract-admissible",
                      "observed", "bp-transit", ("policy",))
        healing = ["dispatch-held", "restore", "dispatch", "deliver", "probe"]
    else:
        ops = [receipt, Operation("replay", "client", "restart"), deliver, probe]
        fault = Fault("receipt-1", "receipt-observed", "withhold-completion",
                      "contract-admissible", "persisted", "bp-transit")
        healing = ["replay", "deliver", "probe"]
    return Scenario(
        id="schedule-receipt-observed-" + variant,
        title="a receipt observed, then {}: the receipt's effect happens once, in policy "
              "order, and survives the loss of its completion".format(
                  {"duplicate": "duplicated", "reorder": "reordered with a policy change",
                   "lose-completion": "its durable completion lost"}[variant]),
        requirements=["RET-001", "RET-003"], contract="local-commit-log",
        initial={"recipe": "bp-node", "groups": ["fn.test"], "prior": []},
        actors=adapter.ACTORS, operations=ops, faults=[fault],
        healing=healing, witnesses=["receipt-delivered", "receipt-effect-once"],
        healing_bound=adapter.healing_bound())


def _cut(name: str):
    for table in (native_cuts.POST_LOG_CUTS, native_cuts.STATE_CHECKPOINT_CUTS,
                  native_cuts.RECOVERY_CUTS, native_cuts.LOG_CUTS):
        for c in table:
            if c.name == name:
                return c
    raise KeyError(name)


def scenarios_for(row: Row) -> list:
    if row.family == "served":
        return [adapter.served_scenario_for(_cut(b)) for b in row.boundaries]
    if row.family == "checkpoint":
        return [adapter.checkpoint_scenario_for(_cut(b)) for b in row.boundaries]
    if row.family == "recovery":
        return [adapter.recovery_scenario_for(_cut(b)) for b in row.boundaries]
    if row.point == "page-read-outstanding":
        return [_pending_page_read()]
    if row.point == "reclaim-candidate-selected":
        return [_pending_reclaim()]
    if row.point == "receipt-observed":
        return [_receipt(v) for v in ("duplicate", "reorder", "lose-completion")]
    raise KeyError(row.point)


def scenarios() -> list:
    return [s for row in ROWS for s in scenarios_for(row)]


def status(registry: dict | None = None) -> list:
    """One line per generated scenario: its point, boundary, whether the
    native backend can drive it, why not, and the verdict it expects."""
    registry = boundary_registry() if registry is None else registry
    out = []
    for row in ROWS:
        for s in scenarios_for(row):
            problems = validate(s, registry)
            reasons = pending_reasons(s, registry)
            out.append({"point": row.point, "scenario": s.id,
                        "boundaries": sorted({f.boundary for f in s.faults}),
                        "interleaving": row.interleaving, "family": row.family,
                        "valid": not problems, "problems": problems,
                        "status": "executable" if not reasons else "pending",
                        "reasons": reasons, "expected": s.expected,
                        "owner": pending_owner(s, registry)})
    return out


def main(argv=None) -> int:
    rows = status()
    for r in rows:
        print("{:<32} {:<44} {:<10} expected={} {}".format(
            r["point"], r["scenario"], r["status"], r["expected"],
            ("; ".join(r["reasons"]) if r["reasons"] else "")))
        for p in r["problems"]:
            print("    problem: " + p)
    print("{} scenarios: {} executable, {} pending".format(
        len(rows), sum(r["status"] == "executable" for r in rows),
        sum(r["status"] == "pending" for r in rows)))
    return 1 if any(not r["valid"] for r in rows) else 0


if __name__ == "__main__":
    raise SystemExit(main())

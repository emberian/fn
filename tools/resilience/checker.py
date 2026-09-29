"""The whole-history checker (design §6): does ONE legal execution of the
contract explain ALL the observations together?

B_t is the set of histories consistent with the narrowing records through
t (the client history and the environment facts, in sequence).  A lost
reply leaves both fates; a later read, retry or listing narrows; B_t empty
is a violation, reported with the record that emptied it and the last
non-empty set.  Past its budget the checker answers `inconclusive`, never
`consistent`.  A run is green only when the history is consistent AND the
scenario's positive witnesses were observed (`no-witness` otherwise) AND
the healing phase finished within the scenario's declared bound
(`healing-overran` otherwise; an experimental budget's overrun is listed,
not a verdict: design §7).  A fault that never fired, a stage begun and
never ended, a healing bound declared and never measured, a truncated
journal or a verdict whose digest no longer matches its fields is a
`harness-failure`, named.  Internal diagnostics never narrow: they are
compared with the surviving histories and any conflict is listed.
"""
from __future__ import annotations

from dataclasses import dataclass, field, asdict
import hashlib
import json

from . import CHECKER_VERSION
from . import contract
from .journal import Journal
from .scenario import Scenario, boundary_registry

KINDS = ("consistent", "violation", "inconclusive", "no-witness", "healing-overran",
         "harness-failure")


@dataclass
class Budget:
    max_histories: int = 4096
    max_records: int = 100000


@dataclass
class Verdict:
    kind: str
    scenario_id: str
    journal_digest: str
    checker: str = CHECKER_VERSION
    cause: str | None = None                # harness-failure's name
    explanation: dict | None = None         # violation: the record and the last non-empty B
    surviving: int | None = None            # |B| at the end, when it was computed
    witnesses_observed: list = field(default_factory=list)
    witnesses_missing: list = field(default_factory=list)
    pending_rules: list = field(default_factory=list)
    diagnostics: list = field(default_factory=list)
    healing: dict | None = None             # {elapsed, bound} when a bound was declared
    budget: dict = field(default_factory=dict)
    digest: str = ""

    def fields(self) -> dict:
        d = asdict(self)
        d.pop("digest")
        return d

    def sign(self) -> "Verdict":
        self.digest = hashlib.sha256(
            json.dumps(self.fields(), sort_keys=True).encode()).hexdigest()
        return self

    def verify(self) -> bool:
        """Tamper evidence for a stored verdict: its digest is over its
        fields.  A verdict whose kind was edited fails this; it does not
        re-run the checker (re-checking the journal does that)."""
        return self.digest == hashlib.sha256(
            json.dumps(self.fields(), sort_keys=True).encode()).hexdigest()

    @property
    def green(self) -> bool:
        return self.kind == "consistent" and not self.witnesses_missing

    def to_json(self) -> dict:
        return asdict(self)

    @classmethod
    def from_json(cls, d: dict) -> "Verdict":
        return cls(**d)


def harness_failure(scenario: Scenario, journal: Journal, cause: str) -> Verdict:
    return Verdict("harness-failure", scenario.id, journal.digest(), cause=cause).sign()


def healing_measure(scenario: Scenario, journal: Journal) -> tuple:
    """(healing dict or None, overran, harness cause or None) for the
    scenario's declared bound against the healing stage's `elapsed`."""
    bound = scenario.healing_bound
    if not bound:
        return None, False, None
    ended = [r for r in journal.of_kind("stage")
             if r.get("name") == "healing" and r.get("event") == "ended"]
    if not ended or not isinstance(ended[-1].get("elapsed"), (int, float)):
        return None, False, "healing-unmeasured"
    elapsed = ended[-1]["elapsed"]
    return ({"elapsed": elapsed, "bound": dict(bound)}, elapsed > bound["value"], None)


def check(scenario: Scenario, journal: Journal, budget: Budget | None = None,
          registry: dict | None = None) -> Verdict:
    budget = budget or Budget()
    registry = boundary_registry() if registry is None else registry
    if journal.scenario_id != scenario.id:
        return harness_failure(scenario, journal, "journal-of-another-scenario")
    # Stages: every begun stage ended.
    open_stages = []
    for r in journal.of_kind("stage"):
        if r["event"] == "begun":
            open_stages.append(r["name"])
        elif r["event"] == "ended" and r["name"] in open_stages:
            open_stages.remove(r["name"])
    if open_stages:
        return harness_failure(scenario, journal, "stage-killed:" + open_stages[0])
    # Faults: every scheduled fault fired (an environment fact says so).
    fired = {(r["operation"], r["boundary"], r.get("action"))
             for r in journal.of_kind("environment") if r.get("event") == "fault-fired"}
    for f in scenario.faults:
        if (f.operation, f.boundary, f.action) not in fired:
            return harness_failure(scenario, journal, "fault-never-occurred:{}@{}:{}".format(
                f.operation, f.boundary, f.action))
    # The workload happened at all: a scenario with operations and no client
    # record is a suppressed workload, not a consistent empty history.
    if scenario.operations and not journal.of_kind("client"):
        return harness_failure(scenario, journal, "workload-suppressed")
    healing, overran, unmeasured = healing_measure(scenario, journal)
    if unmeasured:
        return harness_failure(scenario, journal, unmeasured)
    narrowing = journal.narrowing()
    if len(narrowing) > budget.max_records:
        return Verdict("inconclusive", scenario.id, journal.digest(),
                       cause="budget:records", budget=asdict(budget)).sign()
    hist = contract.histories(scenario, budget.max_histories)
    if hist is None:
        return Verdict("inconclusive", scenario.id, journal.digest(),
                       cause="budget:histories", budget=asdict(budget)).sign()
    used = set()
    survivors = list(hist)
    for rec in narrowing:
        kept, here = [], set()
        for h in survivors:
            ok, rules = contract.narrow(scenario, h, rec, journal, registry)
            here.update(rules)
            if ok:
                kept.append(h)
        used |= here
        if not kept:
            return Verdict(
                "violation", scenario.id, journal.digest(),
                explanation={"record": rec, "last_non_empty": survivors[:8],
                             "rules": sorted(here), "rules_used": sorted(used)},
                surviving=0, pending_rules=contract.pending_rules(used),
                witnesses_observed=sorted(contract.witnesses_observed(scenario, journal)),
                healing=healing, budget=asdict(budget)).sign()
        survivors = kept
    # Internal diagnostics against the survivors: listed, never a verdict.
    diagnostics = []
    for r in journal.of_kind("internal"):
        if r.get("event") == "claim" and r.get("claim") == "durable":
            op = r.get("operation")
            if op in survivors[0] and not any(
                    contract.committed_at(scenario, h, op, r["seq"], journal)
                    for h in survivors):
                diagnostics.append("internal 'durable' for {} but no surviving history "
                                   "commits it (seq {})".format(op, r["seq"]))
    observed = contract.witnesses_observed(scenario, journal)
    missing = sorted(set(scenario.witnesses) - observed)
    common = dict(surviving=len(survivors), witnesses_observed=sorted(observed),
                  witnesses_missing=missing, pending_rules=contract.pending_rules(used),
                  diagnostics=diagnostics, healing=healing, budget=asdict(budget))
    if overran:
        note = "healing:{:.1f}s>{}s".format(healing["elapsed"], healing["bound"]["value"])
        if healing["bound"]["kind"] == "seconds":
            return Verdict("healing-overran", scenario.id, journal.digest(),
                           cause=note, **common).sign()
        diagnostics.append("experimental healing budget exceeded: " + note)
    kind = "no-witness" if missing else "consistent"
    return Verdict(kind, scenario.id, journal.digest(),
                   cause=("missing:" + ",".join(missing)) if missing else None,
                   **common).sign()


def independent_per_membership(scenario: Scenario, journal: Journal) -> bool:
    """The oracle the review warns against (§2): each observation judged on
    its own, each membership allowed "old or new" independently.  Kept so
    the tooth can show what it accepts; never a verdict."""
    for r in journal.of_kind("client"):
        if r.get("event") == "read" and r.get("result") == "other":
            return False
        if r.get("event") == "list-group":
            declared = {o.id for o in scenario.posts() if r["group"] in o.args.get("groups", ())}
            declared |= {p["id"] for p in scenario.prior_posts() if r["group"] in p["groups"]}
            if set(r["members"]) - declared:
                return False
    return True

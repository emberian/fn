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
    if scenario.contract == "acceptance-model":
        return check_acceptance_model(scenario, journal, budget, healing, overran)
    if scenario.contract == "response-holds-model":
        return check_response_holds_model(scenario, journal, budget, healing, overran)
    if scenario.contract == "admitted-page-source":
        from .admitted_page import judge
        return judge(scenario, journal)
    if scenario.contract == "page-io-ownership":
        return check_page_io(scenario, journal, budget, healing, overran)
    if scenario.contract == "reclaim-response-hold":
        return check_reclaim_hold(scenario, journal, budget, healing, overran)
    from .payload_boundary import inspect as inspect_payload_boundary
    boundary_failure = inspect_payload_boundary(scenario, journal)
    if boundary_failure:
        kind, cause = boundary_failure
        return Verdict(kind, scenario.id, journal.digest(), cause=cause,
                       pending_rules=["payload-boundary-native-qualification"]).sign()
    narrowing = journal.narrowing()
    if len(narrowing) > budget.max_records:
        return Verdict("inconclusive", scenario.id, journal.digest(),
                       cause="budget:records", budget=asdict(budget)).sign()
    hist = contract.histories(scenario, budget.max_histories, journal)
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
    if "payload_boundary" in scenario.initial:
        diagnostics.append("Boundary reference PRF-110 at " + scenario.initial["payload_boundary"]["reference_source"] +
                           "; observed selected-image outcomes do not establish native qualification.")
    common = dict(surviving=len(survivors), witnesses_observed=sorted(observed),
                  witnesses_missing=missing, pending_rules=contract.pending_rules(used) + (["payload-boundary-native-qualification"]
                      if "payload_boundary" in scenario.initial else []),
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


def check_reclaim_hold(scenario, journal, budget, healing, overran):
    """PRF-1059 response ownership plus fn-orcp-swap-word's readers refusal.

    Requires capture FIRST, then an independent actual acquired response,
    deferral while held, named settlement and productive reclaim afterward.
    Full native composition and physical sector release remain pending.
    """
    if len(journal.records) > budget.max_records or budget.max_histories < 1:
        return Verdict("inconclusive", scenario.id, journal.digest(),
                       cause="budget:response-hold", budget=asdict(budget)).sign()
    rows = [r for r in journal.of_kind("environment") if r.get("event") == "response-reclaim"]
    held = [r for r in rows if r.get("phase") == "held"]
    if len(held) != 1 or type(held[0].get("cid")) is not int or held[0]["cid"] < 0:
        return harness_failure(scenario, journal, "independent-response-identity-unobserved")
    cid = held[0]["cid"]
    captured = acquired = deferred = settled = installed = False

    def violation(row, rule):
        return Verdict("violation", scenario.id, journal.digest(), surviving=0,
                       explanation=dict(record=row, rule=rule),
                       pending_rules=["reclaim-response-native-composition"]).sign()

    for row in rows:
        phase = row.get("phase")
        if phase == "captured":
            captured = True
        elif phase == "held":
            if not captured or installed:
                return violation(row, "new-independent-hold-after-capture")
            acquired = True
        elif phase == "deferred":
            if not acquired or settled or row.get("reason") != "readers":
                return violation(row, "live-response-excludes-swap")
            deferred = True
        elif phase == "settled" and row.get("cid") == cid:
            if not deferred or settled or row.get("status") != "released":
                return violation(row, "named-response-settles-once-after-deferral")
            settled = True
        elif phase == "installed":
            if not settled or installed:
                return violation(row, "destructive-work-waits-for-new-hold")
            if row.get("reclaimed", 0) <= 0:
                return violation(row, "productive-reclaim-not-empty")
            installed = True
    activation = [r for r in journal.of_kind("environment") if r.get("event") == "fault-fired"]
    terminal = [r for r in journal.of_kind("environment") if r.get("event") == "response-terminal"]
    if (len(activation) != 1 or activation[0].get("cid") != cid
            or len(terminal) != 1 or terminal[0].get("cid") != cid):
        return harness_failure(scenario, journal, "independent-response-coordinate-unobserved")
    client_rows = journal.of_kind("client")
    clients = {r.get("operation"): r for r in client_rows}
    expected = {"reclaim-1", "hold", "read-prior", "release", "reclaim-heal", "read-retained"}
    if len(client_rows) != len(expected) or set(clients) != expected:
        return harness_failure(scenario, journal, "capture-first-operation-unobserved")
    if clients["hold"].get("cid") != cid or clients["release"].get("cid") != cid:
        return violation(clients["hold"], "response-operation-identity")
    if not str(clients["hold"].get("group", "")).startswith("211 5 "):
        return violation(clients["hold"], "productive-five-article-group")
    if clients["reclaim-1"].get("installed") or clients["reclaim-1"].get("returncode") != 0:
        return violation(clients["reclaim-1"], "deferred-request-is-distinct")
    if (clients["reclaim-heal"].get("returncode") != 0
            or not clients["reclaim-heal"].get("installed")):
        return violation(clients["reclaim-heal"], "released-reclaim-makes-progress")
    if (not str(clients["release"].get("status", "")).startswith("224 ")
            or clients["release"].get("numbers") != [1, 2, 3, 4, 5]):
        return violation(clients["release"], "captured-response-drains-old-complete-view")
    observed = set()
    if acquired and deferred:
        observed.add("independent-response-held")
    if settled:
        observed.add("response-hold-settled")
    if installed and str(clients["read-retained"].get("expired_status", "")).startswith("430 article reclaimed"):
        observed.add("reclaim-freed")
    if (clients["read-prior"].get("result") == "match"
            and clients["read-prior"].get("during_competing_work")):
        observed.add("read-during-competing-work")
    if clients["read-retained"].get("result") == "match":
        observed.add("read-completed")
    missing = sorted(set(scenario.witnesses) - observed)
    kind = ("healing-overran" if overran and healing["bound"]["kind"] == "seconds"
            else "no-witness" if missing else "consistent")
    diagnostics = ["reclaim-freed names logical retirement and observed install; physical sectors unclaimed"]
    if overran and healing["bound"]["kind"] == "experimental":
        diagnostics.append("experimental healing budget exceeded: {:.1f}s>{}s".format(
            healing["elapsed"], healing["bound"]["value"]))
    return Verdict(kind, scenario.id, journal.digest(), surviving=1,
                   witnesses_observed=sorted(observed), witnesses_missing=missing,
                   pending_rules=["reclaim-response-native-composition"], healing=healing,
                   diagnostics=diagnostics,
                   budget=asdict(budget)).sign()


def check_page_io(scenario, journal, budget, healing, overran):
    """PRF-1057 token cancellation/settlement rules over observed actual I/O.

    The host-called fn-pio-complete's publication criterion and file-clear
    rule justify the independent token-state checker. Native integration,
    actual worker death and the scenario's full composition stay pending.
    """
    rows = [r for r in journal.of_kind("environment") if r.get("event") == "page-io"]
    if len(journal.records) > budget.max_records or budget.max_histories < 1:
        return Verdict("inconclusive", scenario.id, journal.digest(),
                       cause="budget:page-io", budget=asdict(budget)).sign()
    held = [r for r in rows if r.get("phase") == "held"]
    if len(held) != 1:
        return harness_failure(scenario, journal, "page-io-issued-hold-unobserved")
    token = held[0].get("token")
    if (not isinstance(token, list) or len(token) != 6
            or any(type(v) is not int or v < 0 for v in token)
            or held[0].get("file") != token[2]):
        return harness_failure(scenario, journal, "page-io-token-malformed")
    cancelled = blocked = settled = closed = published = False
    seen_hold = False
    activation = [r for r in journal.of_kind("environment") if r.get("event") == "fault-fired"]
    if len(activation) != 1 or activation[0].get("token") != token:
        return harness_failure(scenario, journal, "page-io-activation-token-unobserved")

    def violation(row, rule):
        return Verdict("violation", scenario.id, journal.digest(), surviving=0,
                       explanation=dict(record=row, rule=rule),
                       pending_rules=["page-io-native-composition"]).sign()

    for row in rows:
        phase = row.get("phase")
        if phase == "held":
            seen_hold = True
        elif phase == "cancelled":
            if not seen_hold or row.get("token") != token or settled:
                return violation(row, "cancel-issued-token")
            cancelled = True
        elif phase == "close-held" and row.get("file") == token[2]:
            if not cancelled or settled or closed:
                return violation(row, "retirement-retains-issued-owner")
            blocked = True
        elif phase == "settled":
            completion = row.get("token")
            if completion == token:
                if not cancelled or not blocked or settled or row.get("answer") != ":CANCELLED":
                    return violation(row, "cancelled-completion-discards-once")
                settled = True
            elif row.get("answer") == ":PUBLISH":
                if (not settled or not closed or not isinstance(completion, list)
                        or len(completion) != 6
                        or any(type(v) is not int or v < 0 for v in completion)
                        or completion[0] <= token[0] or completion[2] == token[2]):
                    return violation(row, "replacement-publishes-own-issued-identity")
                published = True
            else:
                return violation(row, "unexpected-completion-identity")
        elif phase == "closed" and row.get("file") == token[2]:
            if not settled or closed:
                return violation(row, "close-after-settlement")
            closed = True
        elif phase in ("stale", "duplicate") and row.get("answer") != ":STALE":
            return violation(row, "stale-completion-does-nothing")
    terminal = [r for r in journal.of_kind("environment") if r.get("event") == "io-terminal"]
    if len(terminal) != 1 or terminal[0].get("token") != token:
        return harness_failure(scenario, journal, "page-io-terminal-unobserved")
    client_rows = journal.of_kind("client")
    clients = {r.get("operation"): r for r in client_rows}
    expected = {"read-prior", "cancel", "retire", "deliver", "read-retained"}
    if (set(clients) != expected or len(client_rows) != len(expected)
            or {o.id for o in scenario.operations} != expected):
        return harness_failure(scenario, journal, "page-io-operation-unobserved")
    if any(clients[operation].get("token") != token for operation in ("cancel", "deliver")):
        return violation(clients["cancel"], "interleave-targets-issued-token")
    if not str(clients["read-prior"].get("status", "")).startswith("403 article temporarily unavailable"):
        return violation(clients["read-prior"], "cancelled-request-stays-distinct")
    if not clients["retire"].get("installed") or clients["retire"].get("returncode") != 0:
        return violation(clients["retire"], "retirement-actually-installed")
    observed = {"issued-read-held"}
    if settled:
        observed.add("cancelled-read-settled")
    if closed:
        observed.add("retired-file-closed")
    if published and clients["read-retained"].get("result") == "match":
        observed.add("read-completed")
    missing = sorted(set(scenario.witnesses) - observed)
    kind = ("healing-overran" if overran and healing["bound"]["kind"] == "seconds"
            else "no-witness" if missing else "consistent")
    return Verdict(kind, scenario.id, journal.digest(), surviving=1,
                   witnesses_observed=sorted(observed), witnesses_missing=missing,
                   pending_rules=["page-io-native-composition"], healing=healing,
                   diagnostics=["new socket is not native CID-reuse evidence; worker thread death unclaimed"],
                   budget=asdict(budget)).sign()


def check_response_holds_model(scenario, journal, budget, healing, overran):
    rows = [r for r in journal.of_kind("client") if r.get("event") == "response-model-step"]
    oracles = [r for r in journal.of_kind("internal") if r.get("event") == "response-model-oracle"]
    if len(rows) > budget.max_records or budget.max_histories < 1:
        return Verdict("inconclusive", scenario.id, journal.digest(),
                       cause="budget:response-model", budget=asdict(budget)).sign()
    if ([r.get("operation") for r in rows] != [o.id for o in scenario.operations]
            or [r.get("operation") for r in oracles] != [o.id for o in scenario.operations]):
        return harness_failure(scenario, journal, "response-model-schedule-incomplete")
    state = dict(generation=0, owners={}, pending=[], released=0, answer="-")
    expected = contract.response_holds_model_view(state)
    observed = set()
    for operation, row, oracle in zip(scenario.operations, rows, oracles):
        state = contract.response_holds_model_step(state, operation)
        expected = contract.response_holds_model_view(state)
        if any(row.get(k) != v or oracle.get(k) != v for k, v in expected.items()):
            return Verdict("violation", scenario.id, journal.digest(),
                explanation=dict(record=row, oracle=oracle, expected=expected, rule="response-model-step"),
                pending_rules=["response-holds-model-composition"]).sign()
        if len(state["owners"]) == 2:
            observed.add("two-model-holds")
        if operation.op == "reclaim" and len(state["owners"]) == 1 and state["pending"]:
            observed.add("one-model-hold-blocks")
        if state["released"]:
            observed.add("model-retirement-released")
        for fault in scenario.faults:
            if fault.operation == operation.id and row["a"] != ":ABSENT":
                return harness_failure(scenario, journal, "response-model-fault-not-activated")
    terminal = [r for r in journal.of_kind("environment") if r.get("event") == "response-model-terminal"]
    if len(terminal) != 1 or any(terminal[0].get(k) != v for k, v in expected.items()):
        return harness_failure(scenario, journal, "response-model-terminal-unobserved")
    if not state["owners"] and not state["pending"]:
        observed.add("model-settled")
    missing = sorted(set(scenario.witnesses) - observed)
    kind = "healing-overran" if overran and healing["bound"]["kind"] == "seconds" else (
        "no-witness" if missing else "consistent")
    return Verdict(kind, scenario.id, journal.digest(), surviving=1,
        witnesses_observed=sorted(observed), witnesses_missing=missing,
        pending_rules=["response-holds-model-composition"], healing=healing,
        diagnostics=["Logical response holds and retirement only; no native I/O or sectors."],
        budget=asdict(budget)).sign()


def check_acceptance_model(scenario, journal, budget, healing, overran):
    """Every model observation must fit one independent sequential fixture.
    Model observations never stand in for native socket or disk evidence.
    """
    rows = [r for r in journal.of_kind("client") if r.get("event") == "model-step"]
    if budget.max_histories < 1:
        return Verdict("inconclusive", scenario.id, journal.digest(),
                       cause="budget:histories", budget=asdict(budget)).sign()
    if len(rows) > budget.max_records:
        return Verdict("inconclusive", scenario.id, journal.digest(),
                       cause="budget:records", budget=asdict(budget)).sign()
    if [r.get("operation") for r in rows] != [o.id for o in scenario.operations]:
        return harness_failure(scenario, journal, "model-schedule-incomplete")
    state = dict(published=set(), pending=None, generation=None, fenced=False)
    observed = set()
    for operation, row in zip(scenario.operations, rows):
        before = state
        state = contract.acceptance_model_step(state, operation)
        expected = contract.acceptance_model_view(state)
        if any(row.get(key) != value for key, value in expected.items()):
            return Verdict("violation", scenario.id, journal.digest(),
                           explanation=dict(record=row, expected=expected,
                                            rule="acceptance-model-step"),
                           surviving=0, pending_rules=["acceptance-model-composition"]).sign()
        if before["pending"] is None and state["pending"] is not None:
            observed.add("model-prepared")
        if state["published"] - before["published"]:
            observed.add("model-published")
    terminals = [r for r in journal.of_kind("environment")
                 if r.get("event") == "model-terminal"]
    if len(terminals) != 1 or any(terminals[0].get(key) != value
                                for key, value in contract.acceptance_model_view(state).items()):
        return harness_failure(scenario, journal, "model-terminal-unobserved")
    if state["pending"] is None and not state["fenced"]:
        observed.add("model-settled")
    missing = sorted(set(scenario.witnesses) - observed)
    if overran and healing["bound"]["kind"] == "seconds":
        kind = "healing-overran"
    else:
        kind = "no-witness" if missing else "consistent"
    return Verdict(kind, scenario.id, journal.digest(), surviving=1,
                   witnesses_observed=sorted(observed), witnesses_missing=missing,
                   pending_rules=["acceptance-model-composition"],
                   diagnostics=["Logical pending ownership only; no native I/O executed."],
                   healing=healing, budget=asdict(budget)).sign()


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


def check_bp_slice_observations(journal, *, expected_source, budget=None):
    """Judge SCN1046's observed relationships without promoting log promises.

    This is the fixed composed fixture's observation checker. Scenario-driven
    fault scheduling, physical lifetime and whole composition remain pending.
    A source label is compared with the fixture's validated published image
    pair; the runner separately verifies its immutable artifact set.
    """
    import re
    from . import bp_slice_contract
    from .adapters.bp_slice_observer import EVENTS, OBSERVATION_KINDS
    budget = budget or Budget()
    base = dict(scenario_id=journal.scenario_id, journal_digest=journal.digest(),
                budget=asdict(budget),
                pending_rules=["bp-slice-whole-composition", "bp-slice-fault-observation"])
    if len(journal.records) > budget.max_records:
        return Verdict("inconclusive", cause="record-budget", **base).sign()
    if (journal.scenario_id != "bp-disconnected-delivery-recovery" or
            not isinstance(expected_source, str) or
            not re.fullmatch(r"[0-9a-f]{40}", expected_source)):
        return Verdict("harness-failure", cause="fixture-source-coordinate", **base).sign()
    artifacts = [r for r in journal.of_kind("environment")
                 if r.get("event") == "image-artifact-coordinate"]
    if len(artifacts) != 1:
        return Verdict("harness-failure", cause="image-artifact-coordinate-missing", **base).sign()
    images = artifacts[0].get("images")
    if (not isinstance(images, list) or len(images) != 2 or
            any(not isinstance(row, dict) or row.get("source") != expected_source or
                not isinstance(row.get("manifest_sha256"), str) or
                not re.fullmatch(r"[0-9a-f]{64}", row["manifest_sha256"]) or
                not row.get("launcher") or not row.get("manifest") for row in images)):
        return Verdict("harness-failure", cause="image-artifact-coordinate-invalid", **base).sign()
    observations = [r for r in journal.records if r.get("event") in OBSERVATION_KINDS]
    if (tuple(r.get("event") for r in observations) != EVENTS or
            any(r["kind"] != OBSERVATION_KINDS[r["event"]] for r in observations)):
        return Verdict("harness-failure", cause="missing-or-reordered-slice-observation", **base).sign()
    complete = [r for r in journal.of_kind("environment")
                if r.get("event") == "fixture-observations-complete"]
    if len(complete) != 1 or complete[0].get("semantic_verdict") != "pending":
        return Verdict("harness-failure", cause="fixture-not-complete", **base).sign()
    events = {r["event"]: r for r in observations if r["event"] != "post-observed"}
    events["post-observed"] = [r for r in observations if r["event"] == "post-observed"]
    if events["fixture"].get("source") != expected_source:
        return Verdict("harness-failure", cause="fixture-source-mismatch", **base).sign()
    environment_faults = [r for r in journal.of_kind("environment") if r.get("event") == "slice-fault-fact"]
    expected_faults = {
        "decision-cut-readback": events["decision-cut-readback"].get("fault"),
        "outbox-process-death": {key: events["outbox-process-death"][key] for key in ("exit_code", "held_stdout", "selector", "value") if key in events["outbox-process-death"]},
        "receipt-contact-uncertain": events["receipt-contact-uncertain"].get("relay_faults"),
        "checkpoint-stage-cut": events["checkpoint-stage-cut"].get("fault"),
    }
    if (len(environment_faults) != 4 or
            {r.get("operation"): r.get("facts") for r in environment_faults} != expected_faults):
        return Verdict("harness-failure", cause="slice-environment-fault-facts-missing-or-inconsistent", **base).sign()
    try:
        violation = bp_slice_contract.obligations(events) or bp_slice_contract.fault_observations(events)
    except (KeyError, bp_slice_contract.MissingObservation) as error:
        return Verdict("harness-failure", cause="missing-slice-fact:" + str(error), **base).sign()
    if violation:
        rule, reason = violation
        return Verdict("violation", cause=rule,
                       explanation={"rule": rule, "reason": reason}, surviving=0, **base).sign()
    return Verdict("consistent", surviving=1,
                   witnesses_observed=["post-accepted", "accepted-readback",
                                       "receipt-reoffered", "matching-obligation-only",
                                       "retirement-debt-preserved"],
                   diagnostics=["Fixed-fixture relationships only; scheduling and full native composition remain open."],
                   **base).sign()

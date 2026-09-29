"""Test the testers (review §9, design §9): seven mutations of a run, each
of which the framework must distinguish from a successful run, by name.

A mutation transforms (scenario, journal) or the verdict; `EXPECTED` says
the verdict each must produce.  `fabricated_green_run` builds the journal
of a successful run of a scenario of the native-cut family for these tests
only: it is the tester's input, never evidence about fn.
"""
from __future__ import annotations

import copy

from .checker import Verdict
from .journal import Journal
from .scenario import Scenario


def fabricated_green_run(scenario: Scenario, boundary_rule: str = "either",
                         fate: str = "committed") -> Journal:
    """A journal of the scenario as a correct node would produce it: the
    prior post accepted, the faulted post's reply lost at its boundary, the
    image's scan, recovery, reads and the retry agreeing with FATE."""
    j = Journal(scenario.id)
    prior = scenario.prior_posts()
    fault = scenario.faults[0]
    j.stage("workload", "begun")
    for o in scenario.operations:
        if o.op == "post" and o.id != fault.operation:
            j.client("reply", operation=o.id, outcome="accepted")
    j.client("reply", operation=fault.operation, outcome="lost")
    j.environment("fault-fired", operation=fault.operation, boundary=fault.boundary,
                  action=fault.action, evidence="returncode=-9")
    committed = fate == "committed"
    n_other = sum(1 for o in scenario.operations if o.op == "post" and o.id != fault.operation)
    j.environment("persisted-records", count=len(prior) + n_other + (1 if committed else 0),
                  source="log scan-store")
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    order = {o.id: i for i, o in enumerate(scenario.operations)}
    for o in scenario.operations:
        if o.op == "read":
            art = o.args["article"]
            if art == fault.operation:
                j.client("read", operation=o.id, article=art,
                         result="match" if committed else "absent")
            else:
                j.client("read", operation=o.id, article=art, result="match")
        if o.op == "retry":
            j.client("reply", operation=o.id, outcome="duplicate" if committed else "accepted")
        if o.op == "list-group":
            g = o.args["group"]
            members = [p["id"] for p in prior if g in p["groups"]]
            for p in scenario.posts():
                if g in p.args.get("groups", ()) and (
                        p.id != fault.operation or committed
                        or any(r.args.get("of") == p.id and order[r.id] < order[o.id]
                               for r in scenario.retries())):
                    members.append(p.id)
            j.client("list-group", operation=o.id, group=g, members=members)
    j.stage("healing", "ended")
    return j


def suppress_workload(scenario, journal):
    j = Journal(scenario.id)
    for r in journal.records:
        if r["kind"] != "client":
            j.append(**{k: v for k, v in r.items() if k != "seq"})
    return scenario, j


def refuse_every_post(scenario, journal):
    j = Journal(scenario.id)
    for r in journal.records:
        r = {k: v for k, v in r.items() if k != "seq"}
        if r["kind"] == "client" and r.get("event") == "reply":
            r["outcome"] = "refused"
        elif r["kind"] == "client" and r.get("event") == "read":
            r["result"] = "absent"
        elif r["kind"] == "client" and r.get("event") == "list-group":
            r["members"] = [m for m in r["members"]
                            if any(p["id"] == m for p in scenario.prior_posts())]
        elif r["kind"] == "environment" and r.get("event") == "persisted-records":
            r["count"] = len(scenario.prior_posts())
        j.append(**r)
    return scenario, j


def disable_fault_hook(scenario, journal):
    """The process did not die: no fault-fired fact, the reply accepted."""
    j = Journal(scenario.id)
    fault = scenario.faults[0]
    for r in journal.records:
        r = {k: v for k, v in r.items() if k != "seq"}
        if r["kind"] == "environment" and r.get("event") == "fault-fired":
            continue
        if r["kind"] == "client" and r.get("operation") == fault.operation:
            r["outcome"] = "accepted"
        j.append(**r)
    return scenario, j


def corrupt_checker_result(verdict: Verdict) -> Verdict:
    v = copy.deepcopy(verdict)
    v.kind = "consistent"
    v.witnesses_missing = []
    v.cause = None
    return v


def truncate_history(journal_path):
    """Drop the journal's last lines (its seal among them) on disk."""
    lines = journal_path.read_text().splitlines()
    journal_path.write_text("\n".join(lines[:-2]) + "\n")
    return journal_path


def omit_witness(scenario, journal):
    """The run never reconciled a retry: its reply is missing from the record."""
    j = Journal(scenario.id)
    retries = {o.id for o in scenario.retries()}
    for r in journal.records:
        r = {k: v for k, v in r.items() if k != "seq"}
        if r["kind"] == "client" and r.get("operation") in retries:
            continue
        j.append(**r)
    return scenario, j


def kill_stage(scenario, journal):
    """The healing stage began and never ended."""
    j = Journal(scenario.id)
    for r in journal.records:
        r = {k: v for k, v in r.items() if k != "seq"}
        if r["kind"] == "stage" and r["name"] == "healing" and r["event"] == "ended":
            continue
        j.append(**r)
    return scenario, j


MUTATIONS = {
    "suppress-workload": suppress_workload,
    "refuse-every-post": refuse_every_post,
    "disable-fault-hook": disable_fault_hook,
    "omit-witness": omit_witness,
    "kill-stage": kill_stage,
}

# (kind, cause prefix) each mutation must yield; the two that act on the
# stored artefacts (the journal file, the verdict) are judged by their
# readers: truncate-history by Journal.read, corrupt-checker-result by
# Verdict.verify.
EXPECTED = {
    "suppress-workload": ("harness-failure", "workload-suppressed"),
    "refuse-every-post": ("no-witness", "missing:"),
    "disable-fault-hook": ("harness-failure", "fault-never-occurred:"),
    "omit-witness": ("no-witness", "missing:retry-reconciled"),
    "kill-stage": ("harness-failure", "stage-killed:healing"),
    "truncate-history": ("harness-failure", "truncated-history"),
    "corrupt-checker-result": ("harness-failure", "checker-corrupted"),
}

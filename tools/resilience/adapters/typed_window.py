"""Actual typed-window fixed lifecycle trace, distinct from native return/join.

The driver calls fn-pwx-acquire/cancel/return/release/settle-cancelled. These
records are logical API observations, not physical worker observations.
"""
import re
from ..journal import Journal
from ..checker import Verdict

TRACE = re.compile(r"FN_W7_WINDOW step=(\d+)\s+answer=(:[A-Z-]+)\s+"
                   r"phase=(:[A-Z-]+)\s+bytes=(\d+)\s+workers=(\d+)\s+close=(:[A-Z-]+)")
EXPECTED = (
    (":ASSIGNED", ":RUNNING", 320, 1, ":READ-FILE-HELD"),
    (":CANCELLED", ":CANCELLED-RUNNING", 320, 1, ":READ-FILE-HELD"),
    (":STALE-JOB", ":CANCELLED-RUNNING", 320, 1, ":READ-FILE-HELD"),
    (":STALE-JOB", ":CANCELLED-RUNNING", 320, 1, ":READ-FILE-HELD"),
    (":RETURNED", ":CANCELLED-RETURNED", 320, 1, ":READ-FILE-HELD"),
    (":STALE-JOB", ":CANCELLED-RETURNED", 320, 1, ":READ-FILE-HELD"),
    (":RELEASED", ":IDLE", 64, 0, ":CLOSABLE"),
    (":STALE-JOB", ":IDLE", 64, 0, ":CLOSABLE"),
)
RULES = ("exact-worker-acquisition", "cancel-keeps-charges", "running-cannot-settle",
         "wrong-request-cannot-return", "return-keeps-charges",
         "revoked-cannot-publish", "returned-cancel-settles-once", "duplicate-settlement-stale")


def observe(text):
    journal = Journal("typed-window-cancel-return-settle")
    for match in TRACE.finditer(text):
        step, answer, phase, charged, workers, close = match.groups()
        journal.client("typed-window-step", step=int(step), answer=answer,
                       phase=phase, charged_bytes=int(charged),
                       workers=int(workers), close=close)
    return journal


def judge(journal):
    base = dict(scenario_id=journal.scenario_id, journal_digest=journal.digest(),
                pending_rules=["typed-window-native-return-and-join",
                               "typed-window-broader-lifecycle-composition"])
    rows = journal.of_kind("client")
    if (journal.scenario_id != "typed-window-cancel-return-settle" or
            len(rows) != len(EXPECTED) or
            [r.get("step") for r in rows] != list(range(len(EXPECTED))) or
            any(r.get("event") != "typed-window-step" for r in rows)):
        return Verdict("harness-failure", cause="typed-window-operations-missing-or-reordered", **base).sign()
    required = {"answer", "phase", "charged_bytes", "workers", "close"}
    if any(not required <= set(row) or
           any(type(row[field]) is not int or row[field] < 0 for field in ("charged_bytes", "workers"))
           for row in rows):
        return Verdict("harness-failure", cause="typed-window-observation-incomplete", **base).sign()
    for index, (row, expected) in enumerate(zip(rows, EXPECTED)):
        actual = tuple(row.get(field) for field in
                       ("answer", "phase", "charged_bytes", "workers", "close"))
        if actual != expected:
            return Verdict("violation", cause=RULES[index], surviving=0,
                           explanation={"rule": RULES[index], "step": index,
                                        "observed": actual, "expected": expected}, **base).sign()
    return Verdict("consistent", surviving=1,
                   witnesses_observed=["cancelled-running-held", "returned-still-held",
                                       "exact-cancelled-settlement", "duplicate-settlement-stale"],
                   diagnostics=["Fixed supplied-vector fixture charged bytes exclude its separate immutable baseline; no native primitive return was observed."],
                   **base).sign()

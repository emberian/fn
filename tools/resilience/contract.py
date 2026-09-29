"""The contract model the checker interprets: profile `local-commit-log`, v1.

This is the ONLY fn semantics in Python, and each rule is a transcription
of a named theorem statement (or the cut table's verified column), cited
here; a rule whose theorem is pending says so, and a verdict lists the
pending rules it rests on.  The decisions themselves stay ACL2's: what the
store persisted is the image's own scan (`log scan-store`), recorded as an
environment fact; Python never recomputes it.

A HISTORY is one legal execution: the fate of each post's ORIGINAL attempt
(committed or absent).  Prior posts of the initial recipe are committed.  A
retry of an absent post commits it from the retry on; a retry of a
committed post is a duplicate (no-op).  A committed post is a member of
every group it named (atomic memberships) and serves exactly its bytes.
"""
from __future__ import annotations

from dataclasses import dataclass
import itertools

PROFILE = "local-commit-log"
FATES = ("committed", "absent")


@dataclass(frozen=True)
class Rule:
    name: str
    statement: str
    theorem: str | None
    book: str | None
    proof: str | None      # the registry id (planning/proofs.json), or None
    status: str            # "registered" (a theorem with an id) | "verified-table" | "pending"


RULES = {
    "crash-prefix": Rule(
        "crash-prefix",
        "a crash image of the log reads the committed history plus a prefix of the "
        "open batch; for a batch of one, the prior history or the prior and the record",
        "fn-lg-batch-crash-is-a-prefix", "books/store-log-crash.lisp", None, "registered"),
    "boundary-fate": Rule(
        "boundary-fate",
        "at a named cut of `store post' the candidate is absent, present or either, as "
        "the cut table's column says (verified against the model program's steps)",
        None, "tests/campaign/native_cuts.py", None, "verified-table"),
    "committed-serves-exact": Rule(
        "committed-serves-exact",
        "a durable completion installs exactly the pending article: a committed post "
        "is served with its own bytes, never others",
        "fn-durable-completion-installs-exact-pending-article", "books/acceptance.lisp",
        "PRF-003", "registered"),
    "committed-publishes-id": Rule(
        "committed-publishes-id",
        "a durable completion publishes the Message-ID: a committed post is found by it",
        "fn-durable-completion-publishes-message-id", "books/acceptance.lisp",
        "PRF-003", "registered"),
    "absent-until-committed": Rule(
        "absent-until-committed",
        "a prepare does not publish: an uncommitted post is not served",
        "fn-prepare-does-not-publish", "books/acceptance.lisp", "PRF-003", "registered"),
    "duplicate-is-no-op": Rule(
        "duplicate-is-no-op",
        "a retry of an accepted identity is a duplicate and changes nothing; a retry of "
        "an absent one commits it",
        "fn-duplicate-accepted-prepare-is-no-op", "books/acceptance.lisp", "PRF-003",
        "registered"),
    "atomic-memberships": Rule(
        "atomic-memberships",
        "an accepted post is a member of every group it named and of none otherwise; "
        "no membership exists without the others (OBJ-005, STO-002)",
        None, None, "PRF-050", "pending"),
}


def pending_rules(names) -> list:
    return sorted(n for n in set(names) if RULES[n].status == "pending")


def histories(scenario, budget: int):
    """Every assignment of a fate to each post's original attempt, or None
    past BUDGET (the caller answers `inconclusive`, never `consistent`)."""
    posts = [o.id for o in scenario.posts()]
    if 2 ** len(posts) > budget:
        return None
    return [dict(zip(posts, fates)) for fates in itertools.product(FATES, repeat=len(posts))]


def committed_at(scenario, history: dict, post_id: str, seq: int, journal) -> bool:
    """Whether POST_ID is committed in HISTORY when the record at SEQ is
    observed: a prior post always; else its original fate, or a retry of it
    the client saw accepted before SEQ (duplicate-is-no-op)."""
    if any(p["id"] == post_id for p in scenario.prior_posts()):
        return True
    if history[post_id] == "committed":
        return True
    for r in journal.of_kind("client"):
        if r["seq"] >= seq:
            break
        if r.get("event") == "reply" and r.get("outcome") == "accepted":
            op = scenario.operation(r["operation"])
            if op.op == "retry" and op.args.get("of") == post_id:
                return True
    return False


def narrow(scenario, history: dict, rec: dict, journal, registry: dict) -> tuple:
    """(consistent, rules used): does HISTORY explain the record REC?"""
    ev, seq = rec.get("event"), rec["seq"]
    if rec["kind"] == "client":
        if ev == "reply":
            op = scenario.operation(rec["operation"])
            out = rec["outcome"]
            if op.op == "post":
                if out == "accepted":
                    return history[op.id] == "committed", ("committed-publishes-id",)
                if out == "refused":
                    return history[op.id] == "absent", ("absent-until-committed",)
                return True, ()          # lost: both fates survive
            if op.op == "retry":
                of = op.args["of"]
                was = committed_at(scenario, history, of, seq, journal)
                if out == "duplicate":
                    return was, ("duplicate-is-no-op",)
                if out == "accepted":
                    return not was, ("duplicate-is-no-op",)
                return True, ()          # refused for another reason, or lost
            return True, ()
        if ev == "read":
            art = rec["article"]
            is_in = committed_at(scenario, history, art, seq, journal)
            if rec["result"] == "match":
                return is_in, ("committed-serves-exact", "committed-publishes-id")
            if rec["result"] == "absent":
                return not is_in, ("absent-until-committed",)
            return False, ("committed-serves-exact",)   # other bytes: no history serves them
        if ev == "list-group":
            group, members = rec["group"], set(rec["members"])
            used = ("atomic-memberships", "committed-publishes-id")
            declared = [p["id"] for p in scenario.prior_posts() if group in p["groups"]]
            declared += [o.id for o in scenario.posts() if group in o.args.get("groups", ())]
            for post_id in declared:
                is_in = committed_at(scenario, history, post_id, seq, journal)
                if (post_id in members) != is_in:
                    return False, used
            for post_id in members:
                if post_id not in declared:
                    return False, used   # a membership the post never named
            return True, used
        return True, ()
    if rec["kind"] == "environment":
        if ev == "fault-fired" and rec.get("action") == "kill":
            rule = registry[rec["boundary"]]["rule"]
            op = scenario.operation(rec["operation"])
            if op.op != "post" or rule is None:
                return True, ()
            allowed = {"absent": ("absent",), "present": ("committed",),
                       "either": FATES}[rule]
            return history[op.id] in allowed, ("boundary-fate", "crash-prefix")
        if ev == "persisted-records":
            count = len(scenario.prior_posts()) + sum(
                1 for o in scenario.posts()
                if committed_at(scenario, history, o.id, seq, journal))
            return count == rec["count"], ("crash-prefix",)
        return True, ()
    return True, ()


def witnesses_observed(scenario, journal) -> set:
    """The positive witnesses the CLIENT history shows (design §7)."""
    seen = set()
    for r in journal.of_kind("client"):
        ev = r.get("event")
        if ev == "reply":
            op = scenario.operation(r["operation"])
            if r["outcome"] == "accepted":
                seen.add("post-accepted")
            if op.op == "retry" and r["outcome"] in ("duplicate", "accepted"):
                seen.add("retry-reconciled")
        if ev == "read" and r.get("result") == "match":
            seen.add("read-completed")
        if ev == "read" and r.get("during_competing_work") and r.get("result") == "match":
            seen.add("read-during-competing-work")
        if ev == "reclaim" and r.get("freed"):
            seen.add("reclaim-freed")
    return seen

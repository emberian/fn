"""The contract model the checker interprets: profile `local-commit-log`, v2.

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
Recovery, killed or complete, keeps the history; a checkpoint's
publication, killed or complete, leaves the next open reading one whole
checkpoint and reconstructing the same state.
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
        "at a named cut of a post the candidate is absent, present or either, as the "
        "cut table's column for the post's route says (verified against the model "
        "program's steps)",
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
    "recovery-keeps-history": Rule(
        "recovery-keeps-history",
        "recovery truncates only past the last complete record and completes: at every "
        "cut of recovery, and after it, the history the next open reads is the killed "
        "store's committed history",
        "fn-lg-recovered-frontier-is-the-last-complete-record", "books/store-log-recover.lisp",
        "PRF-245", "registered"),
    "checkpoint-old-or-new": Rule(
        "checkpoint-old-or-new",
        "a death at a cut of the checkpoint's publication leaves the next open reading "
        "one of the two whole checkpoints: the old before the rename, the new after the "
        "root barrier, either at the rename (the cut table's column)",
        "fn-bs-scp-program-crash-is-old-or-new",
        "books/byte-store-state-checkpoint-program.lisp", "PRF-083", "registered"),
    "checkpoint-open-equals-full-replay": Rule(
        "checkpoint-open-equals-full-replay",
        "an open from a checkpoint reconstructs the full replay's state: what is served "
        "does not depend on which checkpoint the open read",
        "fn-sn-recover-from-checkpoint-equals-full-recover", "books/store-checkpoint-open.lisp",
        "PRF-083", "registered"),
    "reclaim-old-or-new": Rule(
        "reclaim-old-or-new",
        "a death at a cut of the reclaim pass leaves the old publication before "
        ":installed and the new one from it: the rerun rewrites nothing "
        "(fn-orcp-rerun-rewrites-nothing); the swap happens only over exactly the "
        "captured store with no other reader, in one mutex hold "
        "(fn-orcp-swap-only-over-the-capture); every open connection is re-pinned onto "
        "the rebuilt history (books/owner-reclaim-conns.lisp "
        "fn-orcn-swap-over-the-rebuild-keeps-conn-histories); no single theorem states "
        "old-or-new at the reader level (online-reclaim-8)",
        "fn-orcp-rerun-rewrites-nothing", "books/owner-reclaim-pass.lisp", None, "registered"),
    "receipt-once": Rule(
        "receipt-once",
        "a BP application request whose decision is durable (:committed) is never "
        "re-dispatched: a replay or a duplicate carrier of the same request answers only "
        "(:return-receipt), so the request's effect (the stored article, the owed receipt) "
        "happens once however many carriers arrive and survives the loss of its completion "
        "(fn-bpaj-dispatch-committed-never-retries; the sender's obligation is released "
        "only by a receipt naming exactly it: fn-bpah-released-receipt-names-exactly-its-"
        "obligation, books/bp-release-authority.lisp, PRF-075)",
        "fn-bpaj-dispatch-committed-never-retries", "books/bp-native-app.lisp", "PRF-132",
        "registered"),
    "receipt-policy-order": Rule(
        "receipt-policy-order",
        "a policy change after the decision is recorded does not re-decide it: the "
        "article stays stored and the receipt stays owed; the receipt's forwarding follows "
        "the route table of the pass that forwards it (host/native/bp-node.lisp reads "
        "fn-owner-bp-route-table each pass): no route, the receipt is held and the pass "
        "reports no-route; the route restored, it is sent (no theorem states the "
        "pass-order property; the host's route read is measured by "
        "tests/test_bp_node_native.py test_removed_route_keeps_transit_held_and_reports_"
        "no_route)",
        None, "host/native/bp-node.lisp", None, "pending"),
}

# Which rule a persisted-records fact (the image's scan) is judged by, per
# the phase the adapter records it in.
PHASE_RULES = {"at-cut": "crash-prefix",
               "after-killed-recovery": "recovery-keeps-history",
               "after-recovery": "recovery-keeps-history",
               "after-checkpoint": "checkpoint-open-equals-full-replay",
               "final": "crash-prefix"}
OLD_OR_NEW = {"old": ("old",), "new": ("new",), "either": ("old", "new")}


def pending_rules(names) -> list:
    return sorted(n for n in set(names) if RULES[n].status == "pending")


FATED = ("post", "receipt")      # the operations whose original attempt has a fate


def fated(scenario) -> list:
    return [o for o in scenario.operations if o.op in FATED]


def histories(scenario, budget: int):
    """Every assignment of a fate to each post's (and each BP request
    carrier's) original attempt, or None past BUDGET (the caller answers
    `inconclusive`, never `consistent`)."""
    ids = [o.id for o in fated(scenario)]
    if 2 ** len(ids) > budget:
        return None
    return [dict(zip(ids, fates)) for fates in itertools.product(FATES, repeat=len(ids))]


def identity_committed_at(scenario, history: dict, identity: str, seq: int, journal) -> bool:
    """Whether the BP request IDENTITY (a receipt operation's `bundle`) has
    a committed carrier in HISTORY at SEQ: any carrier of it committed
    (receipt-once: a second carrier of a committed request adds nothing)."""
    return any(committed_at(scenario, history, o.id, seq, journal)
               for o in scenario.operations
               if o.op == "receipt" and o.args.get("bundle") == identity)


def committed_at(scenario, history: dict, post_id: str, seq: int, journal) -> bool:
    """Whether POST_ID is committed in HISTORY when the record at SEQ is
    observed: a prior post always; else its original fate, or a retry of it
    the client saw accepted before SEQ (duplicate-is-no-op)."""
    if any(p["id"] == post_id for p in scenario.prior_posts()):
        return True
    if history.get(post_id) == "committed":
        return True
    for r in journal.of_kind("client"):
        if r["seq"] >= seq:
            break
        if r.get("event") == "reply" and r.get("outcome") == "accepted":
            op = scenario.operation(r["operation"])
            if op.op == "retry" and op.args.get("of") == post_id:
                return True
    return False


def _boundary_rule(registry: dict, boundary: str, route: str):
    entry = registry.get(boundary, {})
    return entry.get("rules", {}).get(route, entry.get("rule"))


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
            if op.op == "receipt":
                # The sender's transfer completed (its disposition durable):
                # this carrier committed; interrupted: both fates survive.
                if out == "accepted":
                    return history[op.id] == "committed", ("receipt-once",)
                return True, ()
            return True, ()
        if ev == "probe":
            # The receiver Store after healing: the identity present exactly
            # when a carrier of it committed; the count is the committed
            # identities (a duplicate carrier adds no article).
            identity = rec["identity"]
            is_in = identity_committed_at(scenario, history, identity, seq, journal)
            identities = {o.args.get("bundle") for o in scenario.operations if o.op == "receipt"}
            count = sum(1 for i in identities
                        if identity_committed_at(scenario, history, i, seq, journal))
            return (rec["present"] == is_in and rec["articles"] == count), ("receipt-once",)
        if ev == "status":
            # The sender's obligation released only by a receipt naming it:
            # pinned=no needs a committed carrier of the request.
            if rec.get("pinned") == "no":
                return identity_committed_at(scenario, history, rec.get("identity", "bundle-1"),
                                             seq, journal), ("receipt-once",)
            return True, ()
        if ev == "restart" and "forward" in rec:
            # A dispatch pass after a policy change: without the route the
            # owed receipt is held (no-route), never sent; with it, never
            # reported no-route.  Which pass sends it is the host's.
            forward, present = rec["forward"], rec.get("route_present", True)
            if not present:
                return forward != "sent", ("receipt-policy-order",)
            return forward != "no-route", ("receipt-policy-order",)
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
        if ev == "recover":
            # A killed recovery (outcome lost) says nothing; the healing
            # recovery completes, or the history was not kept.
            if rec.get("phase") == "healing":
                return rec.get("outcome") == "completed", ("recovery-keeps-history",)
            return True, ()
        return True, ()
    if rec["kind"] == "environment":
        if ev == "fault-fired" and rec.get("action") == "kill":
            op = scenario.operation(rec["operation"])
            if op.op == "post":
                rule = _boundary_rule(registry, rec["boundary"], rec.get("route", "store-post"))
                if rule is None:
                    return True, ()
                allowed = {"absent": ("absent",), "present": ("committed",),
                           "either": FATES}[rule]
                return history[op.id] in allowed, ("boundary-fate", "crash-prefix")
            if op.op in ("recover", "restart"):
                return True, ("recovery-keeps-history",)
            if op.op == "checkpoint":
                return True, ("checkpoint-old-or-new",)
            if op.op == "reclaim":
                return True, ("reclaim-old-or-new",)
            return True, ()
        if ev == "persisted-records":
            count = len(scenario.prior_posts()) + sum(
                1 for o in scenario.posts()
                if committed_at(scenario, history, o.id, seq, journal))
            rule = PHASE_RULES.get(rec.get("phase", "at-cut"), "crash-prefix")
            return count == rec["count"], (rule,)
        if ev == "checkpoint-installed":
            # Which whole checkpoint the open read, against the cut's column:
            # not a fact about any post's fate, so it empties B or leaves it.
            rule = _boundary_rule(registry, rec["boundary"], "store-post")
            if rule is None or rec.get("which") not in ("old", "new"):
                return False, ("checkpoint-old-or-new",)
            return rec["which"] in OLD_OR_NEW[rule], ("checkpoint-old-or-new",)
        return True, ()
    return True, ()


def witnesses_observed(scenario, journal) -> set:
    """The positive witnesses the CLIENT history shows (design §7)."""
    seen = set()
    for r in journal.of_kind("client"):
        ev = r.get("event")
        if ev == "reply":
            op = scenario.operation(r["operation"])
            if r["outcome"] == "accepted" and op.op in ("post", "retry"):
                seen.add("post-accepted")
            if op.op == "retry" and r["outcome"] in ("duplicate", "accepted"):
                seen.add("retry-reconciled")
        if ev == "read" and r.get("result") == "match":
            seen.add("read-completed")
        if ev == "read" and r.get("during_competing_work") and r.get("result") == "match":
            seen.add("read-during-competing-work")
        if ev == "reclaim" and r.get("freed"):
            seen.add("reclaim-freed")
        if ev == "recover" and r.get("phase") == "healing" and r.get("outcome") == "completed":
            seen.add("recovery-completed")
        if ev == "list-group" and r.get("members"):
            seen.add("memberships-listed")
        if ev == "status" and str(r.get("open", "")).startswith("open=checkpoint:"):
            seen.add("checkpoint-installed")
        if ev == "status" and r.get("receipt") == "accepted" and r.get("pinned") == "no":
            seen.add("receipt-delivered")
        if ev == "probe" and r.get("present") and r.get("articles") == 1:
            seen.add("receipt-effect-once")
    return seen

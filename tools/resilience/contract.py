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


def response_holds_model_step(state, operation):
    """Independent interpretation of fn-rpin-step and fn-arpn-step.

    PRF-1059 funds each response separately. Reaping follows arena-reader-pins
    fn-arpn-clear-through-p, not merely the disappearance of one owner.
    This bounded model fixture is not a composed native ownership theorem.
    """
    state = dict(state, owners=dict(state["owners"]), pending=list(state["pending"]), released=0)
    owner = operation.args.get("owner")
    if operation.op == "acquire-hold":
        state["answer"] = ":DUPLICATE" if owner in state["owners"] else ":ACQUIRED"
        if owner not in state["owners"]:
            state["owners"][owner] = state["generation"]
    elif operation.op == "release-hold":
        state["answer"] = ":RELEASED" if owner in state["owners"] else ":ABSENT"
        state["owners"].pop(owner, None)
    elif operation.op == "begin-compaction":
        state["answer"] = str(state["generation"])
        state["pending"].append(state["generation"])
        state["generation"] += 1
    else:
        keep = [stamp for stamp in state["pending"]
                if any(g <= stamp for g in state["owners"].values())]
        state["released"] = len(state["pending"]) - len(keep)
        state["pending"] = keep
        state["answer"] = str(state["released"])
    return state


def response_holds_model_view(state):
    return dict(g=str(state["generation"]), h=str(len(state["owners"])),
                q=str(sum(1 << owner for owner in state["owners"])),
                p=str(len(state["pending"])), r=str(state["released"]), a=state["answer"])


def acceptance_model_step(state: dict, operation) -> dict:
    """Independent checker for the bounded A/B acceptance-model fixture.

    Transcribes books/acceptance.lisp fn-accept-prepare/complete/recover;
    publication, stale completion and fencing are PRF-003 statements named
    in RULES below. Recovery and the whole fixture relation remain model
    checks, not a new composed theorem. This never decides a served request.
    """
    state = dict(state, published=set(state["published"]))
    args = operation.args
    identity, generation = args["identity"], args["generation"]
    pending = state["pending"]
    if operation.op == "model-prepare":
        if not state["fenced"] and pending is None and identity not in state["published"]:
            state.update(pending=identity, generation=generation)
        return state
    if pending != identity or state["generation"] != generation:
        return state
    result = args["result"]
    if operation.op == "model-complete":
        if state["fenced"]:
            return state
        if result == "indeterminate":
            state["fenced"] = True
            return state
        publish, clear = result == "durable", result in ("durable", "aborted")
    else:
        if not state["fenced"]:
            return state
        publish, clear = result == "committed", result in ("committed", "absent")
    if publish:
        state["published"].add(identity)
    if clear:
        state.update(pending=None, generation=None, fenced=False)
    return state


def acceptance_model_view(state: dict) -> dict:
    return dict(a=str(len(state["published"])), p=state["pending"] or "none",
                f="T" if state["fenced"] else "NIL",
                q=str((1 if "A" in state["published"] else 0) +
                      (2 if "B" in state["published"] else 0)))


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
    "xref-locations-exact": Rule(
        "xref-locations-exact",
        "the one Xref line ARTICLE serves ahead of the stored octets (RFC 5537 §3.5 item 8, "
        "RFC 5536 §3.2.14; fn-rcompat-served-payload-inserts-one-line, books/nntp-reader-"
        "compat.lisp, PRF-346) names exactly the (group, local number) pairs at which the "
        "node serves the article, the numbers its own LISTGROUP gave; the stored octets "
        "never carry one (a supplied Xref is refused at injection)",
        "fn-xref-pairs-exact", "books/nntp-xref.lisp", "PRF-206", "registered"),
    "identity-is-the-bytes": Rule(
        "identity-is-the-bytes",
        "a retry that takes another route than its original carries other bytes (the served "
        "route stores the injected article, the store verb the payload as posted) and is "
        "refused by name as a different article under the same Message-ID "
        "(fn-post-store-refusal-text :conflict, books/nntp-post.lisp), never a duplicate, "
        "and changes nothing: the store's committed history and the served bytes are those "
        "before it (no theorem states the conflict decision at the store boundary yet)",
        None, "books/nntp-post.lisp", None, "pending"),
    "power-loss-prefix": Rule(
        "power-loss-prefix",
        "a power cut at a recorded write boundary (tools/power_loss.py, dm-log-writes; W7d) "
        "leaves the recovered store serving every acknowledged post (its 240 was durable) "
        "and a PREFIX of the unacknowledged ones in log order (the recovery truncates at the "
        "first incomplete record), whatever writes the device presented (flush, prefix, "
        "subset or torn selection): the served count is the committed count and no "
        "acknowledged article is absent or other; judged whole-history, never per article",
        "fn-lg-batch-crash-is-a-prefix", "books/store-log-crash.lisp", None, "registered"),
    "number-stability": Rule(
        "number-stability",
        "after recovery a fresh article takes a local number above every number the "
        "recovered store serves: no allocated number is handed out twice (tools/power_loss.py "
        "bindings; no theorem states it at the served boundary yet)",
        None, "tools/power_loss.py", None, "pending"),
    "relay-changes-permitted": Rule(
        "relay-changes-permitted",
        "a copy of one article served by the other agent after transit differs from the "
        "copy it was given only in the NORMALIZED fields the record names (Path, which each "
        "relaying or injecting agent prefixes with its identity, RFC 5537 3.6 step 4 and "
        "3.2.1; Xref, the serving agent's own, RFC 5537 3.7 step 7 and specs/peering.md "
        "2.3): the body octet for octet, every other field and its count the same, the "
        "receiver's own identity in the served Path and never the sender's Xref; response "
        "classes, Message-IDs, memberships and authored bytes are never normalized (design "
        "W7e; fn's served Xref line is fn-rcompat-served-payload-inserts-one-line, no "
        "theorem states the transit Path prefix at the store boundary yet)",
        None, "books/nntp-reader-compat.lisp", None, "pending"),
    "loop-refused": Rule(
        "loop-refused",
        "an article offered by transit whose Path already names the receiving agent is "
        "refused (437, or 435 as already held: RFC 5537 3.6 step 3, RFC 3977 6.3.2.1) "
        "and is not stored or served (no theorem states the loop refusal at the store "
        "boundary yet; the host's is measured by tools/inn_lab.py scenario_duplicates_and_loop)",
        None, "specs/peering.md", None, "pending"),
    "injection-complete": Rule(
        "injection-complete",
        "an article fn injected (a POST or `operator post` it acknowledged) is offered to "
        "its peer with the fields an injecting agent must add, Path naming fn and "
        "Injection-Info (RFC 5537 3.5 items 4 and 11), so the peer's 437 naming a missing "
        "field refutes the injection, never the transfer (no theorem states the offered "
        "octets carry the injected fields yet; books/injection.lisp builds them)",
        None, "books/injection.lisp", None, "pending"),
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


def histories(scenario, budget: int, journal=None):
    """Every assignment of a fate to each post's (and each BP request
    carrier's) original attempt, or None past BUDGET (the caller answers
    `inconclusive`, never `consistent`).  With JOURNAL, an attempt whose
    own reply the client saw (accepted: committed; refused: absent) has
    that fate fixed before enumeration: the first narrowing step would fix
    it anyway, and only the attempts with a lost reply are uncertain (a
    power-loss image with a hundred acknowledged posts and two in flight
    has four histories, not 2^102)."""
    fixed = {}
    if journal is not None:
        for r in journal.of_kind("client"):
            if r.get("event") == "reply" and r.get("outcome") in ("accepted", "refused"):
                op = scenario.operation(r["operation"])
                if op.op in FATED and op.id not in fixed and not r.get("cross_route"):
                    fixed[op.id] = "committed" if r["outcome"] == "accepted" else "absent"
    ids = [o.id for o in fated(scenario) if o.id not in fixed]
    if 2 ** len(ids) > budget:
        return None
    return [dict(fixed, **dict(zip(ids, fates)))
            for fates in itertools.product(FATES, repeat=len(ids))]


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
                if op.args.get("loop"):
                    # A Path naming the receiver: refused with 437 (or 435
                    # as held) and absent, never taken (W7e, loop-refused);
                    # an accepted or lost loop is judged here, before the
                    # committed history could explain it.
                    status = str(rec.get("status", ""))
                    named = status.startswith("437") or status.startswith("435")
                    return (out == "refused" and named
                            and history[op.id] == "absent"), ("loop-refused",)
                if out == "accepted":
                    return history[op.id] == "committed", ("committed-publishes-id",)
                if out == "refused":
                    return history[op.id] == "absent", ("absent-until-committed",)
                return True, ()          # lost: both fates survive
            if op.op == "retry":
                of = op.args["of"]
                was = committed_at(scenario, history, of, seq, journal)
                if rec.get("cross_route"):
                    # Other bytes under the same Message-ID: the named
                    # conflict exactly when the original is committed; an
                    # acceptance when it is not; never a duplicate.
                    if out == "lost":
                        return True, ()
                    named = "different article with this Message-ID" in str(rec.get("status", ""))
                    if out == "refused" and named:
                        return was, ("identity-is-the-bytes",)
                    if out == "accepted":
                        return not was, ("identity-is-the-bytes",)
                    return False, ("identity-is-the-bytes",)
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
            xref = rec.get("xref")
            if xref is not None and rec["result"] in ("match", "other"):
                # The served Xref names exactly the article's memberships at
                # the local numbers this session's LISTGROUP gave.
                if xref.get("malformed") or not is_in:
                    return False, ("xref-locations-exact",)
                expected = {}
                for group in sorted(scenario.groups_of(art)):
                    number = None
                    for lst in journal.of_kind("client"):
                        if lst["seq"] >= seq:
                            break
                        if (lst.get("event") == "list-group" and lst.get("group") == group
                                and art in lst.get("members", ())):
                            number = lst["numbers"][lst["members"].index(art)]
                    expected[group] = number
                got = xref.get("locations", {})
                if set(got) != set(expected) or any(
                        n is not None and got[g] != n for g, n in expected.items()):
                    return False, ("xref-locations-exact",)
            diff = rec.get("differential")
            if diff is not None and rec["result"] in ("match", "other"):
                # The interop backend (W7e): the copy the other agent serves
                # against the copy it was given, judged from the differential
                # itself (never from the adapter's word): only the named
                # normalized fields differ, the body is identical, the
                # receiver's Path names itself, the sender's Xref is not served.
                touched = (set(diff.get("changed", ())) | set(diff.get("only_first", ()))
                           | set(diff.get("only_second", ())))
                permitted = (bool(diff.get("body_identical"))
                             and touched <= set(diff.get("normalized", ()))
                             and diff.get("path_names_self", True)
                             and not diff.get("sender_xref_served", False))
                if not permitted or not is_in:
                    return False, ("relay-changes-permitted", "committed-serves-exact")
                return rec["result"] == "match", ("relay-changes-permitted",
                                                  "committed-serves-exact")
            if rec["result"] == "match":
                rules = ("committed-serves-exact", "committed-publishes-id")
                return is_in, rules + (("xref-locations-exact",) if xref else ())
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
        if ev == "served-counts":
            # The block replay rig's classification as one observation (W7d,
            # counts until the rig writes per-article outcomes): the served
            # count is the committed count, nothing is served with other
            # bytes, the rest are absent.
            # The rig's `served_ref` counts a match with the uncut run's
            # reference, a 430 matching a 430 reference (a refused post)
            # included, so on counts the composition says: no article is
            # served with other bytes (an acknowledged article's 430 is
            # `other`), and the absent ones are among the unanswered whose
            # fate is absent.  The prefix property waits for per-article
            # outcomes (`per`).
            committed = sum(1 for o in scenario.posts()
                            if committed_at(scenario, history, o.id, seq, journal))
            refused = sum(1 for r in journal.of_kind("client")
                          if r["seq"] < seq and r.get("event") == "reply"
                          and r.get("outcome") == "refused"
                          and scenario.operation(r["operation"]).op == "post")
            ok = (rec.get("other", 0) == 0
                  and rec["served"] + rec["absent"] == rec["attempted"]
                  and rec["absent"] <= rec["attempted"] - refused - committed)
            return ok, ("power-loss-prefix", "committed-serves-exact")
        if ev == "numbers":
            fresh, top = rec.get("fresh_number"), rec.get("max_served")
            if fresh is None or top is None:
                return False, ("number-stability",)
            return fresh > top, ("number-stability",)
        if ev == "number":
            # A number a reader was served before the cut names the same
            # article after recovery; unlisted only once the reclaim ran
            # (the reclaim withdraws articles, never reissues a number);
            # served with another Message-ID it was handed out twice.
            result = rec.get("result")
            if result == "same":
                return True, ("number-stability",)
            if result == "unlisted":
                return bool(rec.get("reclaimed")), ("number-stability",)
            return False, ("number-stability",)
        if ev == "recover":
            # A killed recovery (outcome lost) says nothing; the healing
            # recovery completes, or the history was not kept.
            if rec.get("phase") == "healing":
                if rec.get("outcome") == "no-store":
                    # The cut fell before the store's initialization was
                    # durable (the block rig's init phase): no store is the
                    # old state, consistent only with nothing committed.
                    committed = any(committed_at(scenario, history, o.id, seq, journal)
                                    for o in fated(scenario))
                    return not committed, ("crash-prefix",)
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
        if ev == "peer-transfer":
            # The interop backend (W7e): the transport's answer to an offer of
            # one article between fn and its peer.  An offer the receiver took
            # (335/235, 238/239) carries an article committed at the sender;
            # a 437 naming a missing injected field refutes fn's injection.
            op = scenario.operation(rec["operation"])
            was = committed_at(scenario, history, op.id, seq, journal)
            status = str(rec.get("status", ""))
            if rec.get("outcome") == "accepted":
                return was, ("committed-publishes-id",)
            if rec.get("outcome") == "refused" and "Missing" in status and was:
                return False, ("injection-complete",)
            return True, ()
        if ev == "persisted-write-selection":
            # Whatever the device presented, the committed unacknowledged
            # posts are a prefix of the open batch in log order.
            fates = [history.get(o) == "committed" for o in rec.get("open", ())]
            prefix = all(fates[:sum(fates)]) if fates else True
            return prefix, ("power-loss-prefix",)
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
            if (op.op == "retry" and r.get("cross_route") and r["outcome"] == "refused"
                    and "different article with this Message-ID" in str(r.get("status", ""))):
                seen.add("cross-route-retry-refused")
        if ev == "read" and r.get("result") == "match":
            seen.add("read-completed")
            if r.get("differential") is not None:
                seen.add("relay-normalized")
        if ev == "reply":
            op = scenario.operation(r["operation"])
            if op.op == "post" and op.args.get("loop") and r["outcome"] == "refused":
                seen.add("loop-refused")
            if (op.op == "retry" and r.get("route") == "peer-transit"
                    and r["outcome"] == "duplicate"):
                seen.add("duplicate-refused")
        if ev == "read" and r.get("during_competing_work") and r.get("result") == "match":
            seen.add("read-during-competing-work")
        if ev == "reclaim" and r.get("freed"):
            seen.add("reclaim-freed")
        if ev == "recover" and r.get("phase") == "healing" and r.get("outcome") == "completed":
            seen.add("recovery-completed")
        if ev == "recover" and r.get("phase") == "healing" and r.get("init_phase") and (
                r.get("outcome") == "completed"
                or (r.get("outcome") == "no-store" and r.get("reinit") == 0)):
            # A cut in the store's initialization leaves the old state (no
            # store, re-initialized) or the new (a store that recovers).
            seen.add("init-old-or-new")
        if ev == "list-group" and r.get("members"):
            seen.add("memberships-listed")
        if ev == "status" and str(r.get("open", "")).startswith("open=checkpoint:"):
            seen.add("checkpoint-installed")
        if ev == "status" and r.get("receipt") == "accepted" and r.get("pinned") == "no":
            seen.add("receipt-delivered")
        if ev == "probe" and r.get("present") and r.get("articles") == 1:
            seen.add("receipt-effect-once")
    return seen

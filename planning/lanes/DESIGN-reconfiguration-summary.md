# Design: assured live reconfiguration

Lane `w4/reconfig-design`, branched at `9321344`. Deliverable:
[`specs/reconfiguration.md`](../../specs/reconfiguration.md). No certification
ran; nothing here is a proved theorem.

## The problem

fn has no configuration, only constants. The carried group list is a `defconst`
in `books/store-config.lisp`, capacity is a `defconst` in
`host/store-host.lisp`, the BP policy/terms/issuer ids and inbound group map are
`defconst`s in `host/bp-ingress-host.lisp`, and `run_store.py` refuses any store
whose JSON is not `==` to `DEFAULT_CONFIG`. Adding a newsgroup means recompiling
the core. The w2 owner's `(:declare-group name)` fact log is in-process and lost
on restart — its own first open item.

## The design in one paragraph

A configuration change becomes a **transaction in the same journal as a post**,
under the same staging, durability and replay discipline. The journal becomes a
two-kind stream (`:article`, `:config`); a config record carries a *list* of
typed deltas, a txid, the generation it results in, and a clock observation.
Replay folds them into a `(generation . value)` pair the node carries in a new
fifth slot. `fn-initial-state` takes no groups; `fn-replay`, `fn-sf-replay-node`,
`fn-sn-open-observed` and `fn-sn-make` lose their configuration parameters;
`fn-sn-groups`/`fn-sn-capacity` survive as *derived* accessors so downstream
books keep their call sites. An unconfigured store has no groups and zero
capacity, so it accepts nothing — the correct fail-closed floor.

## Four decisions worth arguing about

- **The generation counts config records, not journal records.** A thousand
  posts leave the generation at 3, so "this reply is consistent with exactly one
  generation" stays true across a busy posting period, and a reader need not be
  advanced merely because someone posted.
- **The group table is a history, not a set.** Each entry carries
  `created-gen`, `created-stamp`, `retired-gen`, and its retained local-number
  watermark. `:remove-group` sets `retired-gen`; it never deletes. This is what
  lets an article accepted at generation 2 stay bound to a group retired at 3,
  makes NNT-006's "watermarks survive removal" structural rather than a rule to
  remember, and is exactly the creation fact NEWGROUPS has always needed.
- **"No mixed generation" is carried in `fn-node-statep`, not recomputed.** Two
  equalities — acceptance groups *are* the config's live table at the current
  generation, retention capacity *is* the config's capacity — do the work. This
  respects the no-whole-state-revalidation rule (D3).
- **Admissibility splits into a replay-checkable layer and an owner layer.**
  Group removal's article/obligation/stage conditions are node-derivable, so
  replay re-checks them and faults; the reader-pin condition is owner state and
  never enters a durable record. Group *creation* is inadmissible if the
  resulting table would overflow RFC 3977 §3.1's 512-octet initial line — a
  reconfiguration must not be able to deny service to every future connection.

## Seven keystone statements

Atomicity (no state observes a mix of two generations, plus the
inadmissible-changes-nothing direction); reader consistency (a reply is the
pinned prefix's reply, the pin is derived, the pin is stable without
`:advance`); acceptance/configuration binding (every article names groups live
at *its* generation; replay reproduces the bindings by an independent
enumeration; an article can never change configuration); reservation
preservation; recovery replays configuration (open-observed equals live, and
acknowledged reconfigurations survive a crash image — `<=`, not `=`, so an
unacknowledged tail may vanish per STO-004); liveness of application (advancing
is sufficient and nothing else is required — no timing claim); and
listener/peer changes as effects, not state. Teeth are named per hypothesis,
including the witnesses that must not be degenerate: the reservation witness
must have a nonzero reservation, the delta-list witness must have three distinct
intermediate values, the retired-group witness must still retrieve the article.

## What changes elsewhere

`fn-nntp-projectionp` becomes a per-generation verdict taking the config, with a
new theorem that the verdict depends only on the generation; `fn-snt-relation`
drops its `groups`/`capacity` bindings and gains a config-is-replay-config
statement; NEWGROUPS becomes implementable with separate soundness and
completeness directions; the store format id goes to `fn-store-experiment-5`
(eleven-slot article record, two-kind stream) and `*fn-store-group-table-id*` is
deleted outright. `DEFAULT_CONFIG` shrinks to four pure format keys — the last
place Python held a value a deployment could choose.

## Six packets

R1 value/record/parameters with `init` writing one default config record and
**every existing test passing unchanged**; R2 the node transition and its four
keystones; R3 the owner event, the reader pin and the three reader/liveness
keystones (deletes `fn-own-facts` — the owner state shrinks); R4 hosts and CLI
(deletes eleven `defconst`s; acceptance is that `grep '^(defconst' host/*.lisp`
returns only format and protocol constants); R5 the per-generation verdict and
NEWGROUPS with a transcript test; R6 quotas, peers and contact plans read live.

## Open, deliberately

Who may submit a reconfiguration is the deployment profile's question; this
design only guarantees an untrusted *article* cannot. The group-table history
grows without bound — STO-006 will have to preserve it as the "relevant policy
context" that clause already names. A generation is local; D11's portable group
authority stays M4.

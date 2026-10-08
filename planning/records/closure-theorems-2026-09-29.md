# Closure theorems: the statements B10 showed were missing (2026-09-29)

Lane closure-theorems (Claude Fable 5.1). Ember, after B10: "what missing
statement let this slip past our proofs? what other missing statements
should we try and demonstrate?"

B10: a configuration record accepted on a transaction-full store after an
automatic checkpoint, then a clean stop, left a store every open refused as
checkpoint-damaged. Root cause (lane limits-live): refused POSTs on a full
budget consume transaction ids without records; the open's frontier came from
the article records alone; the replay's `:frontier` check then had a premise
(`fn-replay-advance-okp node frontier`: every id the node reaches is below
the frontier) that the writers never established. Two statements were
missing, and each has a family:

1. **What a refusal leaves behind.** No theorem said "a refused request has
   no effect on the state", so the one refusal that does have an effect (a
   consumed transaction id) had no name and no reader accounted for it.
   Section B.
2. **The open's premise is what a clean stop leaves.** The open's check was
   proved of its own model; nothing said the writers leave a state that
   satisfies it. Section A generalises the question over the whole tree
   (every premise a hosted theorem assumes that no hosted theorem
   establishes); section C states it for the open.

## A. The premise audit (tools/premise_audit.py)

Generated from the readable tree with tools/reach_check.py's reader (the
same subject rule as the ledger: the subject is what the conclusion calls,
hosted when a host line reaches it). A PREMISE is a hypothesis `(R v)` of a
theorem whose subject a host line reaches, R a book-defined predicate, v a
bare variable. R is ESTABLISHED when a theorem concludes `(R (F ...))`
without assuming R and F (or a function inside the argument) is
host-reachable; ESTABLISHED OFF THE HOST PATH when only an unreachable F
does; PRESERVED ONLY when every theorem concluding R assumes it; NEVER
CONCLUDED otherwise. Not counted: record-macro recognizers and ACL2
primitives.

At dev 1922efe84 (persvati, `python3 tools/premise_audit.py --summary`; the
reader then stopped at a top-level `let*`, see the 2026-09-29 note below):

    premise_audit: 1528 premises at hosted entries, 1011 unestablished
    (3800 theorems): 601 never concluded, 109 preserved only,
    301 established off the host path; baseline 1011

The baseline (planning/premise-baseline.json) is shrink-only: `make check`
runs `premise_audit.py --summary --strict`, which fails on a premise not in
the baseline and on a baseline entry that is no longer a finding. The
relation-shaped subset (names matching
`inv|relation|okp|statep|carried|wf|valid|consistent|coherent|sound|related|admissible|frontier|history`)
is 114 premises: 50 never concluded, 27 preserved only, 37 established off
the host path; the table is planning/evidence/closure-theorems-premise-relations.md
(generated: `premise_audit.py --markdown --pattern ...`). The full listing at
this revision is planning/evidence/closure-theorems-premise-full.txt.

What the count means and does not. A finding is not a false theorem: the
theorems are true of any state that satisfies R. It says that on the running
node nothing proved establishes R at that entry, so the theorem's claim rests
on the host's (unverified) construction of the state. The B10 premise
(`fn-replay-advance-okp` of the replayed node and the host's frontier) is of
this kind; owner-relation's PKT-888 (`fn-ocl-relation` false after the peer
open) is the stronger finding this reader cannot make: a hosted establishment
exists (the open) but not for every entry. The reader also cannot see a
premise established by a `verify-guards` (a guard is checked at the call,
not proved of the host's argument) nor a premise inside a definition (B10's
check was one: `fn-rii-sco-finalize-configured`'s `:frontier` arm, whose
premise is now a theorem, section C). The 301 "off the host path" are
dominated by the byte-model programs (`fn-bs-record-inputp`,
`fn-bs-crash-imagep`, `fn-scol-okp`), which are models of host programs by
design (planning/decisions.md, the byte model): their establishment is the
transcription check's, not a hosted call's. The 109 "preserved only"
include `fn-lgoc-invariantp` (22 theorems), which owner-relation established
for the Store open (`fn-ohr-store-open-installs-the-carried-relation`) on a
branch not yet on dev: the count shrinks as such lanes land.

Reader correction (closure-theorems-2, 2026-09-29): `reach_check.split_statement`
stops at a top-level `let`/`let*`/`mv-let`, so a theorem concluding of a bound
name (`fn-scj-invp-at-install`: `(fn-scj-invp o ...)` with `o` the installed
owner) read as no conclusion at all and the row's "fn-scj-invp, 31, never
concluded" was the reader's, not the tree's. `premise_audit.statement` now
opens the binders (unit test `test_statement_opens_binders`). At dev e78a6645d
+ limits-live-b10 (persvati): 1,588 premises at hosted entries, 1,003
unestablished (608 never concluded, 101 preserved only, 294 off the host
path); `fn-scj-invp` and `fn-lgoc-invariantp` read as established by a hosted
entry (`fn-scj-invp-at-install` of `fn-ock-install`; owner-relation's open).
reach_check's own subject rule has the same blind spot (its `_bindings`
helper is not used by `split_statement`): an open ask for its owner.

Creators (closure-theorems-3, 2026-09-29): a `defstobj`'s creator was never a
definition to the graph, so an abstract stobj's `:creator ... :exec
create-NAME` edge dropped and nothing concluded of `(create-NAME)` could be
hosted. `reach_check.Graph` now names `create-NAME` for every `defstobj`
(test `test_a_defstobj_creator_is_reached_through_the_abstract_creator`), and
`fn-arp-okp` is established by `fn-arp-okp-of-create-fn-arena$p`
(books/payload-arena-paged.lisp: a conjunct of
`create-fn-arena-paged{correspondence}` stated of the creator; the paged arena
is the live extent arena's foundation, host/bp-ingress-host.lisp ->
fn-arena-seal-list -> fn-arena-extent-seal-list -> fn-arena-paged-seal-list).
With the creators reached, the seven stobj correspondence rows
(`fn-arena$lcorr`, `fn-arena$pcorr`, `fn-arena$xcorr`, `fn-cat$corr`,
`fn-cat$corr-w`, `fn-hist$corr`, `fn-octets$corr`) read as established by
their own obligations. At db7fb5fa0 + this change (hbox): 1,588 premises,
995 unestablished (608 never concluded, 100 preserved only, 287 off the host
path); baseline 1,003 -> 995. `fn-lgoc-invariantp` was already out of the
baseline at 4c08b2a63 (the binder fix reads owner-relation's open).

### What to establish next (the relation-shaped subset, by weight)

The number after each R is how many hosted theorems assume it. What is
missing in each class is one theorem at the host entry that builds the state
(the open, the init, the recovery): `(R (open ...))` with no `(R ...)`
hypothesis, of a function a host line reaches.

Preserved only (every theorem concluding R assumes it: no base case):
`fn-scj-invp` 31 (the store checkpoint journal), `fn-lgoc-invariantp` 22
(the carried owner relation: owner-relation's
`fn-ohr-store-open-installs-the-carried-relation` is that base case, on
lane/owner-relation), `pgs-alloc-inv` 13, `fn-ocri-relation`
13, `fn-sxd-okp` 9, `pgs-x-inv` 8.

Never concluded (nothing proves R of anything; the host's construction is
the only source): `fn-retain-admissiblep` 9, `fn-sched-admissiblep` 8,
`fn-tj-record-okp` 7, `fn-bs-imp-okp` 7, `fn-cpc-validp` (reach_check's old
orphan: valid checkpoint, no caller and no establishment).

Established only by a model (the establishing theorem's subject is not
host-reached): `fn-scol-okp` 59 (`fn-scol-okp-of-clear`,
`-of-load-held-rows`), `fn-bs-frontier-inputp` 53 (typed by the byte model's
k0 host arguments), `fn-hp-okp` 24 (`fn-hp-empty-image-facts`),
`fn-scj-versions-okp` 20, `pgs-x-tab-inv` 18, `fn-hrc-wfp` 12,
`fn-sn-observed-identity-okp` 10 (`fn-sob-sn-open-ok-facts`). For these the
question is whether the host calls the establishing function or a twin of
it: a twin needs the named equality (reach_check's bridge), a model needs
the transcription check.

The reader cannot tell a stobj correspondence (`fn-arena$lcorr`,
`fn-cat$corr`: established by the abstract stobj's own proof obligation)
from a relation; those rows are noise in the total and are why the baseline,
not the count, is the gate. (Resolved, closure-theorems-3: the creators are
reached, and the rows read as established.)

## B. Refusal is effect-free, and the one refusal that is not

books/refusal-effect.lisp (prefix `fn-rfx-`); the coverage table (host
refusal entry, the ACL2 function, the theorem) is the book's header.

Effect-free, by definition (the else branch with its test negated), each
`:rule-classes nil`:

| host entry | subject | theorem |
| --- | --- | --- |
| fn-owner-prepare-buffer, unserved group | `fn-psrv-prepare` | `fn-rfx-unserved-prepare-is-unchanged-by-definition` |
| fn-owner-prepare-buffer, budget | `fn-prc-sbud-prepare` | `fn-rfx-unaffordable-prepare-is-unchanged-by-definition` |
| fn-owner-reconfigure, not admitted | `fn-ocfg-reconfigure` | `fn-rfx-refused-reconfigure-is-unchanged-by-definition` |

Teeth (closure-theorems-3, 2026-09-29, tests/acl2/refusal-effect-tests.lisp):
per theorem a positive witness (the antecedent and the conclusion) and a
hypothesis-removal witness (its one hypothesis fails and the request stages,
so the conclusion fails), each on the subject's own fixture: the unserved
prepare on owner-prepare-served-tests' retired-group owner `*lgt-r-reserved*`
(removal: `*lgt-reserved*` stages, phase :record-staged); the budget on the
same owner at budget 0 (the word through the served prepare is :unaffordable;
removal: the host's 1000000 stages); the reconfigure on owner-config-tests'
recovered owner `*ocfg-l-reader*` from a connection it does not hold
(:no-such-connection; removal: connection 0 stages a `fn-cfg-recordp`); the
configuration record's txid (`fn-rfx-config-record-txid-is-the-node-next-by-definition`)
on that owner and on an owner over `*rfx-after*`, the store the full-store
refusal burned txid 0 in: the record's id is 1 with no record holding 0.

FALSE, by design: the full-store POST refusal. The host reserves a
transaction (`fn-store-sn-io :log-reserve` = `fn-olr-sn-reserve`) before the
prepare decides, and a refused prepare resolves the reservation with
`fn-owner-refuse-reservation` (`fn-sn-refuse-reservation`), which "consumes
the durable file reservation and advances the actual idle node over the same
txid" (books/store-node-resolution.lisp). What it consumes, exactly, as a
theorem over the two host-called functions composed:

- `fn-rfx-refused-post-keeps-records`: the records after are the records before;
- `fn-rfx-refused-post-keeps-configuration`: the groups and the capacity are unchanged;
- `fn-rfx-refused-post-consumes-one-txid`: the files' frontier and the node's
  next txid are both one higher, and the files are `:ready` again.

The readers of ids, and how each accounts for the consumed one:

| reader | how | theorem |
| --- | --- | --- |
| the configuration record's txid | it is the node's next txid at staging, so it stands above every burned id | `fn-rfx-config-record-txid-is-the-node-next-by-definition` |
| the open's frontier | joined over the records and the configuration records (B10's fix, host/store-node-host.lisp `fn-store-cfg-next-txid`); the replayed node is idle at or below it | lane limits-live-2, books/open-frontier.lisp `fn-ofr-loop-ok-within-frontier` [landing] |
| the replay | a gap in the ids is jumped, never refused | `fn-ofr-apply-record-idle-past-txid` [landing] |
| the export | the frontier is an archive entry (allocation-frontier.json) and the import plan returns it | `fn-sxp-import-of-export-replays-the-same-history` (PRF-205) |

Refusals with no state of their own (TLS, auth: the decision's word is the
whole effect): `fn-auth-step-protected-only-refuses-authinfo-before-tls`,
`fn-tlsr-decide-carries-the-facts-or-a-named-refusal`. A limits refusal
(`fn-lim-decide` `:refused`) publishes nothing: lane limits-live-2 [landing].

## C. The open accepts every state a clean stop leaves

LANDED (closure-theorems-2, 2026-09-29): books/closure-open.lisp (`fn-clo-`,
PRF-945), teeth tests/acl2/closure-open-tests.lisp. The two halves meet at
the finalize the host reaches through `fn-sco-store-open`
(books/store-checkpoint-open; host/store-node-host.lisp, host/owner-host.lisp;
= `fn-rii-sco-store-open`, PRF-321), whose :logic body is `fn-sco-finalize`
with three history refusals, :history, :replay, :frontier.

- limits-live-2's half (books/open-frontier, PRF-937, merged from
  lane/limits-live-b10 d5f96db80): `fn-ofr-replay-ok-frontier-admits` -- an
  :ok replay is admitted at `fn-ofr-frontier configs events floor`, the fold
  the host computes from its own records.
- the configured model's half (books/config-store-traces, config-store-steps):
  `fn-cst-recoverablep configs events frontier` is the clean stop the store
  steps carry (`fn-cstp-relation-*`), and `fn-cstp-recoverable-facts` says it
  replays :ok.
- `fn-clo-finalize-never-answers-frontier-at-the-computed-frontier`: for ANY
  checkpoint C of the history (C's records are the events; C's drained fold
  is `fn-cpr-replay configs events` -- `fn-sco-capture` is one,
  `fn-sco-replay-of-capture`; the host's extended captures reduce to it,
  `fn-sco-extend-of-capture`) and any natural floor, the finalize at the
  computed frontier is not `(:error :frontier)`. The :frontier arm is DEAD at
  the computed frontier: it is reachable only when the frontier the host
  passes is not the fold of its own records.
- KEYSTONE `fn-clo-clean-stop-is-accepted-or-identity`: on a clean stop, with
  configs non-empty and the events an observed history below the computed
  frontier, the finalize's answer has kind :ok or is `(:error :identity)`.
  `-capture-` and `-store-open-` state it of `fn-sco-capture` and of the
  second value of `fn-sco-store-open` (the host's call).
- Teeth: the positive witness on open-frontier-tests' fixture (every
  hypothesis, the conclusion, and which disjunct: :ok, the open); the
  MUTATION witness (at frontier 6, not the fold, the same clean stop IS
  refused :frontier); the HYPOTHESIS-REMOVAL witness (the configuration chain
  starting at the late record: retained hypotheses affirmed,
  `fn-cst-recoverablep` fails, the conclusion fails, the answer is :replay).

Owed (rows, not theorems here):
- The events half of "the frontier the host passes is `fn-ofr-frontier`":
  host/store-host.lisp `fn-store-log-next-txid-of-events` is program mode
  (limits-live-2's obstruction); PRF-937 covers the config half by call
  (`fn-store-cfg-next-txid` calls `fn-ofr-configs-next`). Until the events
  half is a logic-mode function with a named equation, the composition's
  "computed frontier" is by transcription. Owner: limits-live-3.
- DISCHARGED (same day): `fn-clo-observed-at-the-computed-frontier` -- an
  observed history below the recorded frontier is observed below the
  computed one (`fn-sf-record-listp` bounds each txid by the frontier only,
  and `fn-ofr-events-next` is above every event's txid), so the keystone
  needs only the recorded frontier's premises plus the uint32 bound on the
  computed frontier (`fn-clo-capture-of-clean-stop-opens-or-identity`), and
  `fn-clo-relation-state-opens-or-identity` states it of any state
  `fn-cst-relation` describes: its history opens, or is refused :identity.
  Witness: config-observed-tests' ready state (`*cpo-t-ready*`), answer :ok.
- The :identity refusal (identity, consumer and topic contexts of the
  checkpoint) is the carried contexts' own claim (acceptance-stamp,
  consumer, topic lanes), outside this composition.
- The trace alphabet beyond the store-node model: `fn-cst-recoverablep` is
  over `fn-cpr-replay`, so every event kind `fn-replay-apply-record` applies
  and every configuration record are in scope; reclaim/expiry/compaction
  rewrite the durable history (online-reclaim, byte-model: their own
  "the rewritten history is recoverable" theorems, cited when they land).

## D. The replay dispatcher's alphabet is the writers' alphabet

tools/alphabet_check.py, a `make check` step (`--summary --strict`). Read
from the source, never typed: the configuration deltas' declared kinds
(`*fn-cfg-delta-kinds*`), encoder (`fn-cfg-kind-code`), decoder
(`fn-cfg-code-kind`), dispatcher (`fn-cfg-apply-delta`) and writers (every
`(fn-cfg-delta-make :K ...)` in books/ and host/); the store events' encoder
(`fn-store-event-encode`), decoder, kind reader and the replay's dispatch
(`fn-replay-apply-record`, `fn-rii-apply-record`), through the one
hand-written wire-to-row table (`fn-record-p` is `fn-held-p`, `fn-stxa-p` is
`fn-hstxa-p`: alpha). The step FAILS when a writer produces a kind the
dispatcher, decoder or encoder lacks (exactly a `:set-limit` added to the
writers and not to `fn-cfg-apply-delta`), and reports a dead arm. The
`defevent` families (planning/events.json) agree by construction and are
listed. At 1922efe84: 27 configuration kinds written, 27 dispatched; 7 store
event kinds encoded, 7 dispatched; 0 missing.

Converting `fn-cfg-kind-code`/`fn-cfg-code-kind` and `fn-store-event-kind-code`
to `defevent` forms is the wide-book edit (config.lisp, store-events.lisp)
this lane did not take (wide-config was held); the check does not need it.

## E. import ∘ export = identity over the current alphabet

On dev: `fn-sxp-import-of-export-replays-the-same-history` (PRF-205,
books/store-export.lisp) over (profile, frontier, configuration records as
exact octets, records as exact octets of every kind), and the streamed host
path equal to it (`fn-sxp-stream-is-the-export`,
`fn-sxi-stream-plan-is-the-import-plan`). Because the archive carries the
records and the configuration records as octets, every kind the writers have
today (the new `:set-limit`, `:withdraw-article` configuration deltas; the
retention, identity, consumer and topic events; a reclaimed pack's records)
travels without a change to the theorem -- section D's check is what keeps
"every kind" true as the writers grow. What does not travel is stated in the
book: feed journals and BP spools (the 2026-09-28 review's obligation
transfer). Teeth for the new kinds (an archive holding one record of each
current kind round-trips): NEXT.

## Rows for docs/resource-contract.md

This lane merged origin/lane/resource-contract (97840dafa; the batch merges
it in that order) and added rows X1 (section B: the three composed theorems
and the by-definition table, `books/refusal-effect`) and X2 (section D's
step and section A's audit) to `tools/resource_contract.py` ROWS with a
"Closure (X)" section of prose; the generated block is regenerated with
`tools/resource_contract.py --write` on the box at READY.

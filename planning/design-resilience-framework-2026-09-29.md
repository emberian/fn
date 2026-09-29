# A shared, model-based resilience framework (design, 2026-09-29)

Lane `lane/resilience-framework` (Fable 5.1), from dev `33bb1ada7`, row W7 of
`build/coordinator/COMPLETE-BEFORE-6.6.0.md`, from GPT-6's second review
(`warranty-quality-proof-engineering.md` §1-§9): "a shared, model-based
resilience framework with four interchangeable execution modes ... sharing
the workload language, the correctness model, the failure corpus and the
minimizer." First increment: `tools/resilience/` (the IR, the whole-history
checker, the native cut adapter, the fracture tooth, the tester mutations).

## 0. The sentence

One scenario language, one correctness model, one failure corpus, one
minimizer; four backends that each establish a different thing; a checker
that asks whether ONE legal execution of the contract explains ALL the
observations together, and says "inconclusive" when it runs out of budget,
never "valid"; a run is green only when the history is consistent AND the
scenario's positive witnesses were observed. The deliverable is never "we ran
N crashes": it is "the smallest execution that violates this commitment,
under this stated failure model, reproduced on this executable".

## 1. What exists today, and what each piece becomes

| Existing | Region | Today | Becomes |
|---|---|---|---|
| `tests/campaign/native_cuts.py` | the cut tables (`POST_LOG_CUTS`, `LOG_CUTS`, `IMPORT_CUTS`, `EXPORT_CUTS`, `STATE_CHECKPOINT_CUTS`, `STATEMENT_CUTS`) and `verify_*` | names each process-death cut and its byte-program coordinate; the `candidate` column is checked against the model program's steps | the **boundary registry**: every named cut is a boundary a fault can attach to; the candidate column is the contract's crash rule at that boundary (source: the model programs, via `verify_*`). Not rewritten; imported. |
| `tests/test_native_crash_model.py` (`NativeCampaignMixin`) | `run_post_log_cut` | posts, kills at `FN_NATIVE_POST_FAULT=CUT:kill`, asserts the killed history is prior or prior+candidate per the column, recovers, inspects, retries | **adapter** `tools/resilience/adapters/native_cuts.py`: the same process calls, but the run records three journals and the checker gives the verdict. The mixin's per-step asserts are the adapter's observations. |
| `tools/native_program_check.py` | `check_program`, `Walk` | source-level: the host's persistence ops ↔ the modeled program's steps, cut by cut | unchanged; it is the **coordinate check** (the boundary a scenario names exists in the host at the place the model says). A scenario naming an unregistered boundary is refused at load. |
| `tools/power_loss.py` | `choose_cuts`, `build_image`, `evaluate`, `check_store`, `classify`, `bindings`, `second_cut` | dm-log-writes block replay; per-article oracle (acked = reference bytes; unacked = reference or 430); bindings and number stability; second cut during recovery | **block-replay backend adapter** (W7d): its crash-image selection becomes the environment fact `persisted-write-selection`; `classify`/`bindings` become observations into the journal; the checker composes them (today each permitted alternative is judged independently: §2 of the review). |
| `tests/campaign/native_production_kill.py`, `native_operator_campaign.py`, `native_block_fault.py` | timed kills, operator verbs, block faults | native campaigns with their own verdicts | **native backend adapters** (W7c): timed kills stay a mode with a weaker replay label (`replay: timed`). |
| INN lab (`tests/test_inn_lab.py`, `tests/inn/`) | fn ↔ real INN | interop with feeds, duplicates, loops, cuts | **differential backend adapter** (W7e): the same workload language, explicit normalization rules (numbers and transport fields only), never a second physical fault schedule. |
| `tools/run_simulator.py` + `host/simulator.lisp` | `acceptance-durable` | fixed ACL2 scenarios (executable model evidence) | the seed of the **deterministic backend** (W7f); today it is NOT a general engine and the design says so. |
| `tests/scenarios/catalog.json` | SCN-001.. | prose scenarios with requirement ids | each SCN becomes an IR scenario or names the IR scenario(s) that realize it (W7g). |

New: `tools/resilience/` (IR, journal, contract model, checker, witnesses,
verdicts, mutations, adapters); `tests/test_resilience_checker.py`;
`tests/test_native_resilience_cuts.py`.

## 2. The scenario IR (version 1)

A scenario is data (JSON; `tools/resilience/scenario.py` loads, validates and
dumps it). Identities are SYMBOLIC (`post-A`, `article-A`, `obligation-O1`,
`generation-G2`), bound to concrete Message-IDs, numbers and paths only by
the backend at run time and recorded in the journal's binding table. Faults
attach to NAMED BOUNDARIES, never to sleeps or syscall counts.

```
Scenario v1
  id, version, title, requirements[]            symbolic, cites REQ ids
  contract: profile                             "local-commit-log" (v1);
                                                names the theorems the model
                                                transcribes and the pending ones
  initial: recipe                               "empty-store" | "prior-posts" +
                                                a list of prior posts, groups
  actors[]                                      {name, kind: client|operator|peer|nemesis}
  operations[]                                  ordered; each {id, actor, op, args}
     op ∈ post | read | list-group | retry | recover | restart | reader-snapshot |
          deliver-chunk | disconnect | policy-change | acquire-hold | release-hold |
          begin-compaction | deliver-delayed-page | replay-media | ...
  faults[]                                      {at: {operation, boundary},
                                                 action: kill | lose-response |
                                                         withhold-completion |
                                                         report-error | drop-writes |
                                                         substitute-record | rollback,
                                                 class: contract-admissible |
                                                        assumption-challenging,
                                                 stage: issued|performed|persisted|observed}
  healing: {steps[]}                            stop faults, restore contacts, let
                                                primitives finish, provide resources,
                                                run recovery, probe useful operations
  assertions: {contract-consistent: true,
               bound: {kind, value}}            the declared healing bound, or an
                                                explicitly experimental budget
  witnesses[]                                   required POSITIVE witnesses:
                                                post-accepted, retry-reconciled,
                                                read-during-competing-work,
                                                reclaim-freed, ...
  replay: exact | timed | image                 what the backend can reproduce
```

A fault names `{operation: post-A, boundary: log-written, action: kill}`.
The boundary registry is `tests/campaign/native_cuts.py`'s cut tables plus
the review's schedule points (§5 below) as they gain a host coordinate. A
scenario naming a boundary the registry lacks fails validation by name.

Two randomness streams (workload, faults) so removing an unrelated action
does not scramble the environment; dependency edges between operations
(`retry-A` requires `post-A`; `list-group` after `post-A`) so the minimizer
never produces "the receipt without the post".

## 3. The four backends and what each establishes

| Backend | Executes | Establishes | Replay | Adapter |
|---|---|---|---|---|
| Deterministic simulation | the ACL2 model (and later the extracted core) under controlled clock, randomness, I/O outcomes, completion delivery, socket fragments, scheduling | the CONTRACT's behaviour under an exact schedule; exhaustive small worlds | exact | `run_simulator.py` (seed; W7f makes it general) |
| Native fault-controlled | the developer image with `FN_NATIVE_*_FAULT` at named boundaries; timed kills | the SHIPPED executable's behaviour at each modeled boundary; timed kills with a weaker label | exact at a named cut; `timed` otherwise | `adapters/native_cuts.py` (this increment); production-kill, operator, block-fault (W7c) |
| Block-level crash replay | dm-log-writes images, fs recovery, recovery-during-recovery | the DISK model: which persisted-write selections the platform can present, and that the store's recovery meets them | `image` (the selection is kept) | `power_loss.py` (W7d) |
| Interoperability | fn against INN, dtn7, later µD3TN | shared PROTOCOL semantics; never fn's stronger retention/durability contract | exact workload, no fault schedule | INN lab (W7e) |

Determinism is advertised at the boundary actually controlled: a seed is not
determinism while native threads, foreign libraries, clocks or iteration
order still steer execution.

## 4. Two fault classes, kept apart

**Contract-admissible** (`class: contract-admissible`): process death, write
loss before durability, short I/O, reported errors, lost replies, temporary
disconnection, permitted scheduling delay. A violation is a counterexample
to the promise (after checking the harness and the oracle).

**Assumption-challenging** (`class: assumption-challenging`): a device losing
acknowledged durable writes, substitution of a different valid record,
rollback of a store image, misdirected reads, a peer lying about retention.
The question is different: which violations are DETECTED, how are they
CONTAINED, what EVIDENCE remains. Some cannot be detected without an
independent trusted commitment (whole-image rollback vs a genuinely older
state), and the verdict says so.

They never share a pass rate. A campaign summary has two tables.

## 5. The effect model and the schedule points

Every effect has up to four stages: `issued → performed → persisted →
completion observed`. A fault names its stage: "performed, completion lost"
(the write reached storage, the reply did not) and "completion reported
failure, some writes reached storage" are both scenarios; an injected failed
fsync is never implemented as "none of the preceding writes happened".

| Schedule point | Boundary (registry name) | Adversarial interleaving |
|---|---|---|
| Publication durable, client response pending | `log-fenced` (POST_LOG_CUTS) | lose the reply, restart, retry the original identity |
| Page read outstanding | `page-read-outstanding` (pending: no host coordinate yet) | cancel the reader, retire the old generation, then deliver the read |
| Reclaim candidate selected | `reclaim-candidate-selected` (pending) | acquire a new independent hold before the destructive action |
| New checkpoint prepared | `state-checkpoint-staged-durable` .. `state-checkpoint-durable` (STATE_CHECKPOINT_CUTS) | crash before installation, during it, during cleanup |
| Recovery has performed a repair write | `log-truncated`, `log-recovered`, `recovery-stage-unlinked` (RECOVERY/LOG_CUTS) | crash again before recovery completes |
| Receipt observed | `receipt-observed` (pending: BP row) | duplicate it, reorder with a policy change, lose its durable completion |

"Pending" boundaries are registry rows without a host coordinate: a scenario
may name them, the validator marks the scenario `not-executable` on the
native backend until the coordinate lands (`native_program_check` decides),
and no verdict is manufactured.

## 6. The history checker

`tools/resilience/checker.py`. Its question: **does ONE legal execution of
the contract explain all the observations together?**

Semantics. `B_t` is the set of contract histories consistent with the
observations through `t`. A lost reply leaves both "committed" and "not
committed" in `B`; a later read, retry, group listing, receipt or restart
NARROWS it; a violation is `B_t = ∅`, reported with the observation that
emptied it and the last non-empty set (the explanation the engineers act
on). The checker has an explicit budget (histories enumerated, observations
consumed); exhausting it yields `inconclusive`, never `consistent`.
"Uncertain" is never a third permanent outcome that excuses later
inconsistency: it is a set of two histories that must collapse to one.

Three histories, recorded and judged separately:

- **client observations** (invocation, reply or its loss, disconnect,
  timeout, bytes returned, snapshot identity): the ONLY history that
  establishes what the client was promised;
- **internal diagnostic events** (admissions, chosen records, publication
  boundaries reached, generation switches, effect identities): diagnosis,
  never evidence of a promise ("durable" in a log line is not an ack);
- **environment facts** (which write completed, which bytes were in the
  crash image, which completion was withheld, which fault fired).

The observation journal is written OUTSIDE the faulted store (a sealed
JSONL with a count trailer): losing the evidence of an acknowledged
operation must never make losing the operation look acceptable; a journal
without its seal is `truncated-history`, a harness failure.

The contract model (`tools/resilience/contract.py`) is the only fn
semantics in Python: a transcription of named theorem statements into
narrowing rules, each rule citing its theorem (T2 `fn-lg-batch-crash-is-a-prefix`
for the crash prefix; `fn-durable-completion-installs-exact-pending-article`
and `fn-durable-completion-publishes-message-id` for what a committed post
serves; `fn-duplicate-accepted-prepare-is-no-op` for the retry; the cut
table's candidate column, verified against the model programs by
`native_cuts.verify_post_log_cut_map`, for the per-boundary fate). Rules
whose theorem is pending are marked `pending` in the model and the checker
reports which pending rules a verdict rests on. Where the image can answer a
predicate (the committed history: `--fn log scan-store`), the adapter asks
the image and records the answer as an internal event; Python never
recomputes it.

Consistency models: local acceptance and publication against the local
contract; pinned readers against snapshot semantics; replication against
delivery and evidence rules; custody against the undertaking discharged. No
global linearizability is imposed. Porcupine-style sequential specs apply
to the genuinely linearizable sub-interfaces only (a later profile).

## 7. Healing and positive witnesses

Every scenario ends in a healing phase (stop faults, restore contacts, let
outstanding primitives finish, provide declared resources, run recovery and
reconciliation, probe useful operations) and asserts the relevant work
finishes within the declared bound or an explicitly experimental budget.

A run is GREEN only when the history is consistent AND every required
witness was observed in the CLIENT history: some posts accepted, some
retries reconciled, some reads completed during competing work, some
reclaims freed eligible content. A node that refuses everything is
`no-witness`, never greener. This is the verdict's second coordinate, not
a warning.

## 8. Verdicts and the feedback table

`Verdict.kind ∈ {consistent, violation, inconclusive, no-witness,
harness-failure}`; `harness-failure` names its cause (`fault-never-occurred`,
`truncated-history`, `checker-corrupted`, `stage-killed`). Every minimized
violation ends with GPT-6's classification: extraction/attachment differs
from the proved function → repair the boundary; matches the model but
violates the promise → strengthen the spec or theorem; violates a declared
assumption → detection/containment or platform; the checker rejected a
legal behaviour → repair the oracle and keep the case as a checker
regression; the fault never occurred or evidence was lost → harness, not a
pass. Regressions retain the scenario AND the observations (executable and
dependency identities, initial-state recipe, exact fault decisions,
persisted-write selection, oracle version, minimized explanation), not a
seed.

## 9. Test the testers

`tools/resilience/mutations.py` applies each of GPT-6's seven mutations to a
run — suppress the workload, refuse every post, disable a fault hook,
corrupt a checker result, truncate a history, omit a witness, kill a stage —
and `tests/test_resilience_checker.py` shows each yields a NON-green verdict
distinguished by name from a successful run and from each other. A
framework change that makes any mutation green is a regression.

## 10. Implementation order and the rows

W7a **IR + checker + witnesses + mutations** (this increment). DONE:
`tools/resilience/` loads and validates v1 scenarios; the checker narrows a
lost reply by a read, a retry and a group listing; the two-group fracture is
REFUSED (the tooth); budget exhaustion is `inconclusive`; refuse-everything
is `no-witness`; the seven mutations are each distinguished; tests named.
BEFORE THE CUT.

W7b **the native cut campaign as scenarios** (this increment). DONE:
`POST_LOG_CUTS` generate scenarios (one per cut, the fault at the cut's
boundary, the candidate column as the crash rule); the adapter runs them
on the developer image recording the three journals; the verdict is the
checker's; a kill that did not happen is `harness-failure`;
`tests/test_native_resilience_cuts.py` passes on hbox. BEFORE THE CUT.

W7c **the other native campaigns adapted** (production-kill, operator
campaign, block-fault, the recovery cuts, the served owner's cuts). DONE:
each campaign's verdict comes from the checker over its journals; timed
kills carry `replay: timed`; the old per-campaign asserts are gone or are
observations. BEFORE THE CUT for the recovery and served-owner cuts (they
are release cut coverage); AFTER for the rest.
Status (lane resilience-framework-2, 2026-09-29): the recovery cuts (the
real recovery killed at each `RECOVERY_CUTS` cut and at `log-truncated` /
`log-recovered` over a torn candidate, its writes recorded, recovery
again, the original commitments checked), the served owner's cuts (killed
at each `POST_LOG_CUTS` cut with a two-group POST in flight on the
listener; `operator recover`; memberships observed through LISTGROUP and
STAT on the restarted node, bytes through ARTICLE), the owner's open killed
at each recovery barrier, and the checkpoint cuts are
`tools/resilience/adapters/native_cuts.py`'s five families; every scenario
declares a healing bound (experimental until the contract names one) and
the checker's `healing-overran` judges it. The offline per-group
observation is `store inspect --group` (row S3d) and is pending by name on
an image without it. Production-kill, the operator campaign and the block
faults are still AFTER the cut. The schedule points of §5 are
`tools/resilience/schedule_points.py`: seven scenarios executable, five
pending by name (page read outstanding and reclaim candidate selected:
lane online-reclaim-8, which owns reader generations since the pin port
and whose kill form `reclaim-captured` exists; receipt observed:
bp-remainder-3). incremental-finalize-3 confirmed (2026-09-29) that the
capture adds no earlier prepared boundary: the NEXT bound is written inside
the same staged checkpoint file, and the cuts stay STATE_CHECKPOINT_CUTS'.

W7d **power_loss as a backend**. DONE: crash-image selection is an
environment fact with the storage profile's ordering constraints made
explicit (preflush/FUA semantics from dm-log-writes); `classify`/`bindings`
are observations; the checker composes them whole-history (the "old or new
per article" independence is gone); recovery-during-recovery is a second
fault at a recovery boundary; the pre-recovery image is kept. AFTER THE
CUT (the convergence checklist runs the current rig once). Landed
2026-09-29 (lanes resilience-framework-3 and -4): the adapter over the
rig's records (`persisted-write-selection`, the second cut as a second
fault, the recovery count as `persisted-records`); the rig's classify
writes per-article outcomes (`per`) and bindings per-number outcomes
(`observed_numbers`), each its own `read` / `number` observation, so the
prefix property is judged per article and number stability per number
from the rig's next run on (the 2026-09-26 records carry counts only).

W7e **the INN lab as a differential backend**. DONE: the lab's workload is
IR; normalization rules are explicit and named (numbers, transport fields);
response classes, identities, memberships and authored bytes are never
normalized; the RFC adjudicates. AFTER THE CUT. Landed 2026-09-29 (lane
resilience-framework-4, first increment, record-driven like W7d's):
`tools/resilience/adapters/inn_lab.py` turns the lab's findings into six
IR scenarios (fn-to-inn, inn-to-fn, fn-term, innd-cut, operator-post,
inn-refusals) judged by the checker under `relay-changes-permitted`
(Path and Xref the named normalization, each with its RFC 5537 section;
the differential itself is judged, never the lab's ok), `loop-refused`,
`injection-complete` and the `peer-transfer` fact; boundaries `peer-idle`
and `peer-innd`; the same rules judge both agents. Over the three findings
files every verdict is the lab's. Remaining: the lab running from the
scenarios (its checks as journal writes) on hbox with INN.

W7f **the deterministic backend**. DONE: completion delivery and the
selected scheduling boundaries are deterministic in the simulator; a small
exhaustive suite around uncertainty, two independent holds, a generation
change and repeated recovery. AFTER THE CUT.

W7g **Hypothesis rule-based generation + dependency-aware shrinking**.
DONE: stateful workloads over the IR with bundles for symbolic identities;
shrinking preserves prerequisites (a retry never survives its post's
removal); separate randomness streams; the minimized scenario reproduces
under the same backend. AFTER THE CUT.

W7h **semantic coverage + structure-aware storage mutation**. DONE: the
coverage signature (publication phase, client-outcome certainty, pending
effect classes, reader-generation relation, hold-count class, headroom
band, evidence-version relation, recovery attempt) counts abstract
situations; checksum-preserving and checksum-breaking storage cases; the
corpus keeps boundary-sized payloads. AFTER THE CUT.

W7i **LibAFL / Antithesis evaluated against the same corpus**, each
evaluation proving the intended faults occur, the storage model matches the
declared campaign, and feedback reaches SBCL code. AFTER THE CUT.

## 11. What this increment does not claim

No theorem changed; no native verdict is transferred from the old asserts
to the new checker until W7b's module runs on the box at the READY sha; the
"pending" schedule points have no host coordinate and no verdict; the
checker's enumeration is explicit and small (histories are products of
per-uncertain-post fates) and says `inconclusive` past its budget.

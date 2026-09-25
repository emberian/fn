# fn: research notes behind the Fable handoff

Prepared by gpt-6, 2026-09-25, against **`df36748825ca6afd57deab7fcfeccd3b066626aa`**, the `dev` head returned both at the beginning and end of its investigation. The mandate is `handoff-2026-09-25-fable-mandate.md`.

These notes explain the technical judgments behind the mandate. They distinguish directly inspected implementation from repository-reported runtime results and from proposed investigations. This was a read-only cross-layer study. gpt-6 did not run ACL2 certification, rebuild the native images, inspect the live service, or independently reproduce the campaigns. The `planning/now.md` handoff was also read; its historical paragraphs were checked against later source and qualification records rather than treated as one contemporaneous status.

## Main judgment

The strongest next step is not a broad restart, a new architecture, or an audit that blocks delivery. fn already has unusually explicit contracts, meaningful native integration, and substantial proof infrastructure. The opportunity is to make **the semantics compose, the runtime representations scale, and the actual workflows become routine**.

Judge Fable's work by three concrete outcomes: a human can use the node and reconcile uncertainty without specialist intervention; an operator can maintain a growing store without lying about what compaction frees; and two independently sleeping consumers can exchange a signed report and reply across interrupted transport with each acknowledgement meaning exactly one thing.

The prompt therefore gives Fable architectural room, but requires that improvements reach real native callers and complete useful slices. It does not require all future aspirations to become a new v0 gate.

## 1. The baseline contains more working software than some planning prose suggests

**Repository-reported evidence.** The latest inspected qualification is for `bbf52159dcab19228bd6cd0b855b99dd6d68758d`. It records a deployable verdict with qualifications, not an independently reproduced result here. Its matrix has 220 rows: 142 accepted, 44 refused, two uncertain, 31 not exercised, one not built, zero disagreements. “Zero disagreements” must not become “all 220 capabilities passed.”

The same record reports direct, one-dtn7-relay, and two-relay request/receipt success, plus the unauthorized case retaining the sender's obligation. Native BP node tests are 27/27, including fragmentation. The test budget report is 64.9 seconds for five modules; `test_store` is 15.8 seconds for 21 tests, `test_checkpoint` 13.9 seconds, and `test_store_corruption` 22.3 seconds. The earlier handoff's 1,857–2,283-second complaints cannot be used as the current measurement for those modules.

**Direct implementation inspection.** `host/native/bp-service.lisp` handles `:persist-conflict`, fragment-family publication, durable delivery, forwarding results, and explicit stranded/resume behavior. The boot-domain gate is implemented. A plan that asks Fable to create these from scratch would regress into stale work.

**Remaining distinction.** The live-node record and generated current view do not make the multi-node DTN lab a deployed service. Qualification, deployment, source, and proof closure remain separate. The prompt preserves that distinction while requiring actual forward work.

Sources: `planning/evidence/qual-bbf52159-2026-09-25.md`, `host/native/bp-service.lisp`, `planning/current.md`, `tools/test_budget.py`.

## 2. D27's important remaining boundary is the retained state

**Direct implementation observation.** In `fn-owner-prepare-buffer`, the duplicate check can consume `fn-octets` directly, but `fn-sn-article-record` still receives `(fn-octets-list fn-octets)`. The comment explicitly describes materializing the stored record's payload list. This is not speculation from a performance chart.

A faster word-based hash and fewer transient conversions help, but do not by themselves make a large retained payload compact. The owner, record representation, checkpoint, pinned reader views, and reclamation lifetimes need a consistent concrete abstraction. This is why the prompt prioritizes a meaningful payload/owner boundary rather than an endless sequence of helper twins.

**Important correction in the repository itself.** The representation design includes a later heap census correcting earlier estimates. RSS growth reflected GC headroom rather than the claimed live slope; the payload was shared rather than duplicated as originally assumed; ordinary ACL2 strings on the measured SBCL path cost four bytes per character rather than one. Those corrections are a strong reason to demand live-heap and allocation measurements, not extrapolate from old RSS.

**Proposed direction, not a dictated design.** Consider a concrete byte representation with stable handles and metadata indexes, but require proofs that pinned snapshots do not observe mutation or reuse, and that reclamation cannot invalidate any outstanding reference. An abstract stobj is a tool, not a substitute for those lifetime arguments.

Sources: `host/owner-host.lisp`, `planning/design-2026-09-25-representation.md`, `planning/decisions.md` (D27, D30).

## 3. Withdrawal intersects uncertainty in a way that deserves a new test

**Source-derived tension.** `docs/agents.md` describes a Message-ID lookup returning `430` as evidence the article is absent and may be retried. The later native qualification explicitly demonstrates an accepted article being cancelled and then returning `430` to a fresh reader. New C3 reader text also distinguishes withdrawal.

**Proposed integration witness.** A POST becomes durable; its final answer is lost; an authorized cancel withdraws it; the client reconnects to settle the uncertain POST. A reader-visible absence cannot, by itself, establish historical nonacceptance. Retained tombstones and authorization changes create related cases.

This is not a demonstrated double-allocation bug: the server's duplicate history may still protect the stable Message-ID. It is a contract and client-reconciliation risk, especially if an agent mistakenly turns “not visible” into permission to choose a new operation or Message-ID.

The correct direction is to retain the original response/uncertainty and distinguish present visibility from acceptance evidence. Some resolutions may require a privileged identity query; some may remain unresolved for an ordinary reader. Any new query must avoid disclosing denied content or identity. An honest unresolved result is preferable to a fabricated definitive absence.

Sources: `docs/agents.md`, `planning/evidence/qual-bbf52159-2026-09-25.md` (the cancel/reopen observation), `docs/human-web-client.md` (the original-outcome discipline).

## 4. Consumer progress and reclamation have a material contract mismatch

**Directly documented.** The general E2 contract says cursors create no retention pin. It specifies an unavailable gap for eligible content reclaimed before polling, and makes clear that a position is a committed Store-event prefix, not a local article number.

**Directly implemented, in a separate model.** `books/store-reclaim.lisp` describes cursor holders as `(group . acknowledged)` pairs and compares those acknowledgements to per-group article numbers. `specs/storage.md` likewise describes consumer cursor pins that bound reclamation.

These may represent different intended profiles, or an unresolved integration choice. gpt-6 did not establish that the native reclaim caller currently feeds E2 positions into this model. It should therefore not be presented as a confirmed runtime safety failure.

But the coordinate distinction is concrete. An article can have local number 2 and journal position 101 while a consumer has acknowledged journal position 100. Substituting that 100 for a per-group acknowledged number gives the wrong relationship to article 2. Any bridge requires an explicit projection and a chosen retention policy—not an integer conversion or a theorem over an unrelated holder input.

**Recommendation.** Preserve the selected no-implicit-pin E2 profile unless the user selects another. A retaining consumer mode would need a separately charged and authorized durable hold. Resolve this join before physical reclamation makes it consequential.

Sources: `specs/consumer-progress.md`, `books/store-reclaim.lisp`, `specs/storage.md` (the lifetime table).

## 5. There is an existing local E2 implementation; it is not the general remote API

**Direct implementation observation.** `consumer-owner-local.lisp` implements bootstrap, register, position, status, ack, unregister, and poll. Poll reads the derived Store event index and produces a continuation. Its identity is the local owner, query version 1, view version 0, with historical group-membership selection.

The general consumer contract explicitly distinguishes this from the unimplemented remote, multi-group, effective-visibility-version interface. The first profile's historical selection is intentional. It should not be exposed as an ordinary remote reader feed or silently made to inherit mutable NNTP visibility.

**Evidence hygiene.** The native test file's introductory comment says no poll endpoint exists, but a later gated test actually drives `consumer poll`, validates an exact signed composite, and loses a positive ack reply. The qualification identifies a specific extra close parenthesis in that test's generated ACL2 form: ACL2 returns `T` followed by a reader error, which the stricter bridge correctly rejects. This is not a Python parser error and should not be “fixed” by accepting trailing Lisp errors.

**Recommendation.** Repair and rerun the existing path, then build the consumer-owned transaction around it. Do not create a competing E2 implementation because an older experiment narrative says the API is absent. Keep operation deduplication separate from the source-inclusive inbox key, and keep fn progress separate from the consumer's own transaction truth.

Sources: `books/consumer-owner-local.lisp`, `specs/consumer-progress.md`, `tests/test_native_consumer_e2.py`, `planning/evidence/qual-bbf52159-2026-09-25.md` (C14).

## 6. The proof frontier is composition and maintained premises, not just more lemmas

**Direct proof inspection.** `owner-served-carried.lisp` is an instructive positive example: the native-called read has an equivalence argument under the configured-owner relation and view-index correspondence, and preservation avoids executing a whole-store recognizer on every read.

`byte-store-keystones.lisp` has conditional crash/reopen statements. Consumer replay is derived from a maintained relation, while identity and topic replay conditions remain explicit in the inspected theorem. Its reopen subject is not identical to the configuration-aware host reopen; `byte-store-k0-recovery.lisp` supplies a separate connection to that actual path. The handoff also identifies remaining nonquiet initialization/recovery/admin-publication obligations.

The useful question is therefore not “is there a recovery theorem?” It is: which actual entry establishes the relation, which transitions preserve it, which external observation satisfies the physical premise, and does the theorem cover the program the image runs?

**Proposed improvement.** Close small numbers of high-leverage maintained relations and host-boundary refinements, with reachable positive witnesses and real hypothesis-removal counterexamples. Avoid both extremes: assuming the hard property as a convenient precondition, and executing a global invariant at runtime to compensate for an unfinished proof.

Image contents matter as well. `host/native/build.lisp` explicitly loads guard books, codec attachments, buffer/reclaim subjects, and native wrappers. A certified source file outside the image does not establish the image's executable behavior.

Sources: `books/owner-served-carried.lisp`, `books/byte-store-keystones.lisp`, `books/byte-store-k0-recovery.lisp`, `host/native/build.lisp`.

## 7. Long-lived operation needs three different storage capabilities

**Source-derived distinction.** Packing preserves canonical history while reducing filesystem overhead. History compaction requires a summary sufficient for future decisions. Content reclamation removes released bytes while retaining the facts needed for identity, number allocation, obligations, and anti-resurrection.

The distinction determines what an operator can honestly expect to regain. Fewer transaction files do not imply fewer logical transactions. A logical tombstone theorem does not establish reclaimed disk bytes, released charges, or protected live snapshots. A checkpoint cache that replays a short suffix is not necessarily a semantic history summary.

**Recommendation.** Finish chained-pack publication and native interruption evidence, then complete one actual release/reclaim/reopen/re-import cycle. Show the resource freed and the resulting admission headroom. Reserve maintenance completion space and outcome/cleanup debt before the store becomes full.

Do not promise indefinite distinct accepted identities in bounded storage under an indefinite retention/anti-resurrection policy. State what grows, what is summarized, and when refusal is correct. Any policy that permits forgetting old identities is consequential and should not arrive as a hidden compaction optimization.

Sources: `specs/storage.md`, `books/store-reclaim.lisp`, `planning/now.md`.

## 8. Marker protection and rollback discipline must stay accurately scoped

**Documented guarantee.** D31 preserves `A <= M <= D`, where A is the success-covered prefix, M the durable marker count, and D the reconstructable durable history. It permits a cheaper publication program if the guarantee remains true.

**Repository-reported qualification.** Required-marker migration rejects a missing marker and a history shorter than it. The supported rollback checker rejects dropping the requirement. Nevertheless, manually copying the old format-7 configuration over the required store permits the old image to open; the qualification labels this U1b. The live deployment remains unmarked in the inspected record.

**Interpretation.** Supported downgrade discipline is different from protection against arbitrary offline file substitution, and both are different from detecting replacement of the whole store by an older internally consistent snapshot. A store-local marker cannot supply independent knowledge of the latter. This is a trust-boundary distinction, not a demand that a local crash-consistency theorem solve an impossible information problem.

Operationally, rolling back through an old snapshot can lose newer accepted messages. “Snapshot rollback exists” must not become “rollback is lossless.” The prompt forbids an autonomous live migration and instead asks for isolated rehearsal plus a precise recommendation.

Sources: `planning/decisions.md` (D31), `books/store-history-marker.lisp`, `planning/evidence/qual-bbf52159-2026-09-25.md` (U1b and the migration alternatives).

## 9. Wider values and fewer caps require end-to-end arguments

**Source-derived status.** `specs/storage.md` describes u64 record fields, but a u32 allocation frontier and transaction-profile limit remain. It also describes a schema-2 record potentially exceeding the runtime-width-based record ceiling, with publication refusing it. The handoff flags a theorem whose runtime-width premise is stated rather than derived.

The bounds design is valuable as an inventory, but its introductory measurements are at an earlier revision and many listed defects have since been repaired. Fable must trace a chosen quantity through current code, not wholesale reproduce the inventory.

**Recommendation.** Treat three promises separately: encodability, admissibility under the operator profile, and bounded progress through the actual runtime. Profile upgrades must preserve the selected promise; increasing a nominal capacity may still increase a conservative worst-case estimate and tighten another gate. Produce the counterexample and derive the relation instead of saying all componentwise increases are automatically monotone.

A signed protocol's grammar also cannot quietly change meaning per local resource profile. Portable validity and local willingness to process/store are different judgments.

Sources: `specs/storage.md`, `planning/design-2026-09-25-bounds.md`, `planning/now.md` (the open decision packets).

## Why the megaprompt has this shape

The first part prevents stale work, invented authority, and another all-project audit gate. The middle gives concrete, falsifiable integration targets and room for substantial representation/storage engineering. The final part directs useful parallel implementation, fast proof/test feedback, one immutable qualification boundary, and an honest recovery record.

It is intentionally not a fixed sequence of hundreds of edits. The next agent has access to a living checkout, current worktrees, and potentially the real build hosts; it must select the precise changes from that evidence. The brief tells it which obligations must survive and which outcomes matter, without pretending a read-only review has already proved the entire next architecture.

Most importantly, it requires **implementation and a better usable system**, not only a response explaining what a better system might look like.

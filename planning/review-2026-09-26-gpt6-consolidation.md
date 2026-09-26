# gpt-6's architectural review, 2026-09-26: authorize a consolidation pass

Written by gpt-6 after reading `planning/review-request-2026-09-26.md` (the clean state at dev
a1e0f379; the head advanced to bd992699 during the review). Ember adopted it the same day:
"we should think about doing something like that: tear down all deploys, collapse any
migrations / remove versioning suffixes, do plenty of overhaul, make things tidy and neat; then
fn.fg-goose.online, peering with spwashi/pug (packaging for release; OpenBSD; no Python in the
runpath of a deployed node)". The coordinator's plan follows at the end.

---

Yes. **I think fn is ready for an architectural consolidation, not just another optimization wave.** The important distinction is between *lessons worth preserving* and *implementation structures created while discovering those lessons*. The former are becoming quite good. Some of the latter should now go.

My diagnosis is:

> **fn's semantics have matured faster than its runtime organization. Its implementation still repeatedly reconstructs facts that its transitions already know, translates between representations that should share an owner, and preserves internal structures that were useful scaffolding but are becoming architectural constraints.**

The aim should be **fewer independent representations, fewer places that establish the same fact, and fewer operations proportional to history**, not merely fewer lines or fewer theorem books.

## 1. What is scar tissue, and what is genuine complexity?

Preserve: the distinctions between authored bytes and hop-local representation, Message-ID and local article number, historical verification and current authority, custody and application processing, and accepted/refused/uncertain outcomes. The record-codec seam (`books/records-seam.lisp`) is good complexity.

| Preserve | Replace or collapse |
|---|---|
| Distinct semantic identities | Repeated parsing and materialization of each identity's bytes |
| A simple list-based logical model | List-based ownership of all runtime payloads |
| Authoritative history and derived indexes | Reconstructing derived state from history during ordinary requests |
| One owner of shared mutation | Holding the same mutex through large rendering, scans, and unrelated I/O |
| Explicit refinement boundaries | Families of almost-identical transition wrappers differing in one lookup |
| Historical evidence and old-format readers | Runtime dependence on historical implementation layouts |
| Exact proof provenance | Tooling dependencies on incidental presentation or repository-wide churn |

Correction to the culture: **preserve the semantic guarantees, not every historical internal theorem formulation forever.** An old helper's behavior on malformed internal states is not a public compatibility obligation; it may belong in the reference model or boundary validator rather than the optimized execution path.

## 2. The most revealing scar: the system keeps asking history what just happened

Completion searches for the record that is completing (`fn-ccar-seek` walks from sequence zero). The live execution state should hold a PreparedCommit {operation_token, expected_predecessor, event_reference, publication_plan, semantic_delta, resource_reservation}; the completion event names the token; the core applies the durable-result transition with the event reference it already owns. Recovery still reconstructs from durable evidence; a stale callback still cannot complete another operation; the normal path does not search history.

Refresh rediscovers the change by comparing two lists (`fn-gidx-refresh`, `fn-own-refresh`). The commit knows what it did: produce an **explicit committed delta** and let each projection consume it: applyViewDelta(view(S), Δ) = view(S'). The delta describes real semantic effects (a cancel after its target removes visibility; a cancel before its target affects the target's initial visibility; a policy change may touch many entries: explicit, possibly resumable updates). Rule: **a derived-state consumer receives the relevant change, not two worlds to compare.** Applies to group indexes, Message-ID indexes, consumer projections, capacity accounting, carriage usage, configuration replay.

## 3. The next core abstraction should own invariants, not just bytes

The arena alone, with the old payload fields alive, adds a representation without removing the expensive one. Target: **an invariant-bearing executable Store/catalog interface, with the byte store beneath it.** Start with the committed event catalog, payload ownership, pending commit, and the projections for one complete submission/read/recovery path. Logical side: histories, article collections, octet lists. Executable side: indexed tables, compact metadata, byte references; public operations preserve correspondence (abstract stobjs: complicated cross-field invariants maintained by proved operations, not executed as guards; a host "valid" Boolean is not a substitute).

The fourteen-field Store tuple whose comments say fields live there to avoid dependency cycles and whose consistency predicates cannot be guards is the sign that module boundaries and invariant ownership are not aligned; the `*-carried` functions solve it piecemeal. The obligation: R(C,S) ∧ step_c(C,e) = (C',E_c) ⟹ R(C',S') ∧ ⟦E_c⟧ = ⟦E_s⟧, with effects over traces for incremental output. The abstraction need not be materialized at runtime.

Investigate **`attach-stobj`** (ACL2 8.6): substituting executable implementations of an attachable abstract stobj while keeping the logical exports, without recertifying the interface. A narrow prototype (a payload/catalog interface with two implementations through the real saved-image and certificate tooling) before committing to the hundred-book arena-threading approach.

## 4. Redo byte ownership once, across all the places that retain it

Not zero copies: **a small, explicit number of justified copies.** Per article: immutable bytes (one exact representation; references give identity, extent, lifetime); parsed byte facts (boundaries, line count, carrier fields, control target, digests, with grammar version); context-bound decisions (verification/authorization naming the key/policy snapshot); local projections (numbers, visibility, obligations, indexes refer to the stored object). The two-view design is compatible; do not turn the payload predicate into `natp` everywhere; the concrete handle behind an explicit abstraction; the acceptance state's second payload field is part of the same migration. Preserve exact bytes without retaining every transformed copy: a stored representation as a proved composition of immutable spans (generated header bytes, preserved source ranges, body); "one payload copy" means one copy per required representation. Prefer bounded growth and explicit lifetimes: the interface accommodates chunked/paged backing, pinned references, eventual reclamation; a reference handed to a reader stays valid through publication, withdrawal, checkpointing, reclamation; a process-local integer is not a portable identity; a checkpoint reference is interpreted within that checkpoint.

## 5. Checkpoints should describe storage state, not serialize the execution graph (most urgent)

The executable format inherited the overlap of the folds' accumulators; the automatic capture reaching `FN-SCC-FRAMES` and exhausting the heap near 33,000 to 36,000 small articles is evidence that the checkpoint's logical convenience became its physical layout. Replacement: an explicit checkpoint storage schema: one table of immutable payload objects/extents; one table of committed event/record metadata; projection state and roots referring to those tables; versioned provenance and frontier. Reopening equals the intended replay; shared objects represented once; no semantic history compaction required.

**One resumable checkpoint pipeline** for the automatic publication and the offline verb: capture a stable root and its dependencies → enumerate bounded batches → encode bounded chunks → publish and validate → install/select → release the capture's pins. A resource decision BEFORE allocating a whole encoded tree; if it cannot proceed, retain the prior checkpoint and the journal, report, and apply the declared recovery-resource contract's backpressure. A temporary execution budget is not a semantic maximum; an unstated fatal heap ceiling during maintenance is unacceptable. **This moves ahead of most new surface features.**

## 6. Collapse the index and metadata proliferation into a coherent catalog

The byte-tally work that reused the event index instead of a fifteenth Store field is the model. The `consumer-event-index` is the **committed event catalog**: give that role a stable interface. Ownership: sequence identifies the committed event; an article projection has its own reference; Message-ID lookup returns the article binding; group-number lookup is a separate projection; visibility and historical verdicts are distinct versioned facts; scalar totals advance from committed deltas; a signed composite keeps its outer atomic binding and verdict. Stop serializing merely to learn a size: an executable encodedSize_v(r) = |encode_v(r)| or a serialization plan with its proved size, describing the encoding actually stored. Right structure per dimension: append-friendly indexed event storage; a shared Message-ID index; ordered group-number indexes; per-peer ready queues/cursors; fragment-family metadata with incremental coverage; explicit cached frontiers and totals. Criterion: whole operation and whole drain.

## 7. The native interface still contains an internal wire protocol that can be retired

`fnn-owner-name-list` splitting LF-joined octets, feed flushing fetching frames by index against a separate name list: an interface shaped for an external bridge surviving after the boundary became a native call. Replace with typed ACL2-produced results (FeedPublication {peer_reference, sealed_frame_plan, completion_token}); render text at CLI/log boundaries, encode bytes at wire/storage boundaries; no global result mailboxes. The core constructs the result; the adapter executes it.

One semantic owner does not require one enormous critical section: keep the single mutation owner; separate bounded semantic steps, immutable read/render plans against pinned views, and I/O execution consuming plans; do not let threads at the live stobj without the mutex. Bounded quanta and service classes first; large responses yield; control/maintenance traffic gets service; network output outside the critical section where the contract permits. A diagnostic sink must not wedge shared-state progress; the authoritative journals are not logs.

## 8. Two couplings are not permanent laws

A consumer reply limit should not define the Store's record domain: keep the safe restriction, label it an incomplete consumer retrieval interface (a bounded page with identity/provenance and a reference, then bounded retrieval under a pinned authorization). Several caps (one-shot encoder, frame, reply, job image) are connected to admission only because a streaming/reference boundary is missing. Seven barriers are a property of the current publication program: the counterexamples prevent unsafe shortcuts, not a law. Now: publish the measured tier honestly and fix CPU/memory/scheduling. Later, a focused storage redesign: a batch/log publication abstraction, proved per-operation outcomes and crash behavior, then implementation; not deleting one fsync at a time. Do not unify FNBS, feed, configuration and Store journals prematurely.

## 9. The proof architecture also needs consolidation

The pattern reference → carried → concrete → buffered → owner wrapper → native wrapper → equality lemmas is refinement where a genuine boundary exists and suspect where two implementations maintain the same semantic branching to reach different accessors. Put the durable guarantee at the module boundary; representation reasoning below it. Do not require every optimized helper to reproduce the old helper on corrupted tuples: establish the reachable-state relation at EVERY actual entry (recovery, migration, checkpoint load), preserve it, prove the client-visible behavior under it. docs_check's move from line numbers to heading-and-ordinal is the model. Reuse certificates only when proof inputs match. Stop using raw warning counts as prioritization.

## 10. Run the consolidation without a second endless project

Unit of ownership: **architectural boundary**, not symptom. First: stable snapshots and bounded checkpoint publication (the operating-lifetime limit). Second: one concrete committed catalog and byte owner as a vertical slice (ordinary and signed submission, correlated completion, Message-ID/group lookup, pinned ARTICLE/OVER, checkpoint, reopen; the arena, parsed metadata, event references, scalar accounting and view deltas together). Third: retire adapters and generalize (obsolete production paths, global result plumbing, history-search completion, refresh-by-rediscovery; then BP and the configuration/consumer paths; ingress-span joins this program). **Require a deletion map** per abstraction: what it replaces, which callers move, which old paths are removed, which reference definitions remain for specification only, which measurements show the whole path improved (retained bytes, transient peak, allocated bytes per operation, records visited, lock-hold time, proof/build fan-out; over the whole lifetime: load, sustained posting, repeated checkpointing, reopen, reclamation).

> **Stop reconstructing changes that the core already knows. Give immutable bytes one explicit owner. Give committed events one canonical catalog. Make views consume deltas. Make checkpoints serialize an intentional storage schema. Keep one mutation authority without making every byte operation hold its mutex. Preserve semantic laws while allowing the implementation scaffolding, and the theorems about that scaffolding, to be replaced.**

---

## Coordinator's plan (Claude, 2026-09-26 ~17:30Z): wave 5 is the consolidation

Adopted as decisions D33 to D36 pending ember's confirmation (recorded in planning/decisions.md
by the deputy at the first batch):

- **D33 Consolidation.** Wave 5's lanes own architectural boundaries with a deletion map each,
  in gpt-6's order: (1) one resumable checkpoint pipeline with a resource decision before
  allocation and the storage schema; (2) the committed catalog and byte owner as one vertical
  slice (the arena behind an explicit abstraction, parsed byte facts, event references,
  PreparedCommit tokens, view deltas); (3) adapter retirement (typed results, no mailboxes, no
  history-search completion, no refresh-by-rediscovery), then BP and configuration/consumer
  paths. A prototype of `attach-stobj` precedes the catalog slice.
- **D34 Fresh deploys, no migrations.** Every deploy is torn down and reinstalled from the
  release; the format-7 translation, `upgrade-profile`'s upgrade relation, `rollback-check`, the
  versioned release directories and the rollback sentences go; the store format is one format
  until v1 ships, with a `store export/import` for data that must survive a reinstall.
- **D35 The release is the product.** One tarball per platform with its runtime, OpenSSL 3.5 and
  libsodium bundled; Linux x86-64 and OpenBSD amd64 (SBCL W^X, rc.d, LibreSSL absent: bundle
  OpenSSL); a check that no Python is in the runpath of a deployed node; docs a stranger installs
  from.
- **D36 A public node.** fn.fg-goose.online peered with spwashi and pug; the public-exposure
  limits on; the certificate from Let's Encrypt through ~/dev/dregg-infra's ACME tooling (ember,
  2026-09-26); the node's store on the fastest durable disk hbox has, chosen by a lane that
  measures fsync cost per mount (not a question for ember).
- **D35 addendum (ember):** no OpenSSL 3.5 requirement: TLS from the system libssl (LibreSSL on
  OpenBSD, OpenSSL 3.x on Linux), Ed25519 and SHA-256 from libsodium, ML-DSA-65 from a vendored
  PQClean implementation of FIPS 204 (lane crypto-deps); the OpenBSD target is the current
  release, the friend's version to be learned.

The running wave-4 lanes finish (the ledger's five fixes fall under gpt-6's §6 and stay; the
marker-sharing sharing lane stops at its current attempt: §8 defers the publication redesign).
The NNTP feature inventory (lane nntp-gap-inventory) says what a general usenet server still
lacks.

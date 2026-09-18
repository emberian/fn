# Current work: executable components and integration

The [decision workbook](decisions.md) is a backlog, not a questionnaire that must
be completed before coding. The user authorized broad Terra implementation waves
with Luna/Sol/Astra work and convergence in batches. Routine reversible choices
are owned by the implementation team; public byte formats, cryptographic suites,
and deployment remain explicitly separate decisions.

## Completed integrated checkpoints

- Acceptance has certified initial-state, transition-preservation, immutable
  binding, and local-number uniqueness results. The theorem hypotheses retain
  the abstract durable-completion/recovery boundary.
- Wire framing, CBOR primitives, retention accounting, journal crash experiments,
  disconnected fact exchange, and an experimental NNTP reader have executable
  books and assertion tests. Their full subsystem contracts are still open.
- The acceptance simulator executes the actual definitions in ACL2.
- The node now connects retention and acceptance in one transaction, with
  general transition preservation and article-to-pin binding proofs.
- The reader runs over a real loopback socket via a persistent ACL2 process;
  independent `nntplib` client traffic and the socket regression suite passed.
- Review repairs strengthened wire-state bounds, distinguished journal sequence
  from transaction identity, and hardened NNTP numeric/projection handling.

The first [checkpoint](../tests/evidence/2026-09-18-integrated.md) covered 19
certified roots and nine Python tests. The later
[storage batch](../tests/evidence/2026-09-18-storage.md) passed `make test` with
25 roots, the simulator, and 26 Python tests. It adds complete primitive and
record round trips, typed replay proofs, a real immutable-file store with durable
allocation, and a reader over recovered state. Independent NNTP client traffic
and maximum-profile 128-article replay also passed. The third
[article batch](../tests/evidence/2026-09-18-articles.md) passed with 29 roots,
the simulator, and 27 Python tests. It adds exact successful-parse input
preservation, general retention-release invariants, and LISTGROUP ranges/cursors;
independent client traffic also passed. Each record retains exact source hashes,
outcomes, proof scope, and remaining limitations.

The fourth [reader/storage batch](../tests/evidence/2026-09-18-wildmat-storage.md)
passed with 33 roots, the simulator, and 31 Python tests plus the independent
client. It adds UTF-8 wildmat/filtering, explicit command bounds, two real recovery
hardening fixes, and an executable file-publication kernel with initial fence/gate
proofs and crash traces. It does not close full adapter refinement.

See [implementation status](../docs/implementation.md), the
[proof registry](proofs.json), and [milestones](milestones.md) for scope. A
certified component does not close a complete milestone or prove the host/disk.

## Working rhythm

One writer owns each area. Agents certify their own roots while independent
areas advance. Root integrates a frozen batch, runs the combined suite, records
evidence, and updates the registries. Review each coherent batch once; repair
correctness findings, track remaining proof scope, then advance.

The user requested frequent local checkpoint commits on 2026-09-18. Commits are
for synchronization and may include unfinished work; a commit is not evidence
of passing tests. Keep generated logs/certificates under ignored build paths,
and retain concise evidence summaries and exact source hashes in the repository.

## Current engineering choices

- ACL2 8.7 on SBCL 2.6.8 for the development model, with Python tooling.
- Interpreted ACL2 bridge for the first host experiment; raw Common Lisp calls
  to unguarded logical functions are not the integration argument.
- One owner and one shared-state transaction pending at a time.
- Exact octet payloads and exact Message-ID strings; no native signing preimage.
- Local cross-post names must all be configured; failure is atomic.
- No automatic expiry or history pruning. Resource charges include retained
  history, and inadequate capacity rejects new obligations.
- Experimental CBOR uint32/byte-string primitives; no persistent/native schema
  frozen by their existence.

## Active assurance-closure wave

On 2026-09-18 the user explicitly prioritized burning down the remaining hard
assurance work rather than continuing to widen prototype surface area. The fifth
[fields/transfer/storage batch](../tests/evidence/2026-09-18-fields-transfer.md)
has passed with 38 certified roots, the actual-core simulator and 32 Python tests.
Source hashes were unchanged. Semantic fields, bounded transfer staging,
file-kernel step/crash preservation and the real recovery-read fence are integrated.

The current wave uses all 13 available slots (root plus 12 workers). One writer
owns each new file set; shared base definitions remain stable unless root
coordinates a concrete counterexample repair. Targeted certifications may run in
parallel on independent new roots; root freezes and certifies their union once.

| Owner/task | Completion criterion for this wave |
| --- | --- |
| Sol: record canonicality | General successful exact record decoding re-encodes the original bytes |
| Sol: file traces | Arbitrary finite kernel traces preserve state, stable history and earlier acknowledged records, including repeated crash/recovery |
| Terra: adapter fault matrix | Enumerated before/after-effect syscall failures preserve prior commits, classify uncertainty correctly and fence/recover allocation |
| Luna: process crashes | Deterministic actual process deaths at persistence boundaries preserve prior commits and identity allocation on reopen |
| Terra: transfer preservation | General reserve/add-chunk transitions preserve state and capacity/count invariants |
| Terra: transfer assembly | Complete candidates have exact declared length and agree with all retained chunk bytes |
| Terra: article postconditions | Successful parsing establishes output recognizer and meaningful source/header/field bounds |
| Terra: wire event API | Production event-yield step preserves state and accounts for consumed/unconsumed input |
| Terra: NNTP sessions | General implemented dispatcher preserves the session recognizer and stated cursor consistency |
| Terra: UTF-8/parser | Successful decode establishes scalar validity/progress/output bounds; parsed wildmat recognizer |
| Astra: matcher correspondence | Actual DP wildcard matcher agrees with independent anchored semantics |
| Luna: obligation map | Finite actionable inventory tying remaining claims to PRF/REQ/SCN IDs and closure criteria |

Root records evidence, fixes concrete integration/adapter findings, and updates
registries. An assignment is not a proof or a completion claim. General guards,
work bounds, live pending-node/file composition, actual adapter correspondence,
physical qualification, authorization/signatures, and persistent exchange remain
visible obligations; the inventory determines subsequent closure waves. No new
permission ceremony or serial review chain is introduced.

The [local persistence experiment](../specs/store-experiment.md) is integrated:
bounded transaction bytes, replay, allocation across aborted process lifetimes,
fault tests, and a read-only NNTP view. The [walkthrough](../docs/local-experiment.md)
makes this checkpoint executable without treating it as the final news service.

Next: compose bounded article parsing, injection, and provenance with the reader;
complete the selected reader command profile; qualify/refine the existing disk
adapter against the crash model; lift invariants through journal integration,
finite traces, and guards. The
current node and journal are separate models: connecting them is a real next
implementation task, not something implied by having certified both books.
The next user-facing design discussion has
[concrete native-versus-legacy byte examples](../docs/article-byte-examples.md)
for D01, followed by principal/key custody (D09). These proposals do not silently
select a signing grammar or cryptographic suite.

Private-group cryptography remains a separate requirements/research track.
Shared community groups come first; MLS is a candidate, not a commitment.
